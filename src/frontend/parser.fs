// Copyright (C) 2026 Elkeid Me
//
// This file is part of Lui.
//
// Lui is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// Lui is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Lui.  If not, see <http://www.gnu.org/licenses/>.

module Parser

open AST
open System
open System.Collections.Immutable
open Utils
open XParsec
open XParsec.CharParsers
open XParsec.OperatorParsing
open XParsec.Parsers

let private createCounter (init: uint32) =
    let mutable count = init

    fun () ->
        count <- count + 1u
        count

let private counter = createCounter 0u

// 使用 `Map` 而不是 `HashMap`，保持纯函数式，避免在解析过程中出现副作用。
type BlockInfo = { SymbolTable: Map<string, Handler>; InLoop: bool }

/// - `Counter`: 生成唯一标识符的计数器。
/// - `SymbolTable`: 全局的符号表，存储 `Handler` 到 `Definition` 的映射。
/// - `RetType`: 当前函数的返回类型。
/// - `Blocks`: 当前作用域栈，每个作用域包含一个符号表和是否在循环内的信息。
/// - `ParsingType`: 当前正在解析的基础类型（用于处理类型声明）。
///
///   注意，解析数组声明时，仍然使用数组元素类型作为 `ParsingType`。
type Context =
    { SymbolTable: SymbolTableType // 符号表，存储解析至今的所有局部、全局定义或声明。
      RetType: AST.Type
      Blocks: BlockInfo list
      ParsingType: AST.Type }

let inline private isInLoop context = (List.head context.Blocks).InLoop

let inline private isGlobal context =
    match context.Blocks with
    | [ _ ] -> true
    | _ -> false

let inline private enterBlock startLoopNow context =
    let inLoop = startLoopNow || isInLoop context
    { context with Blocks = { SymbolTable = Map.empty; InLoop = inLoop } :: context.Blocks }

let inline private enterFuncBody retType context =
    { context with RetType = retType; Blocks = { SymbolTable = Map.empty; InLoop = false } :: context.Blocks }

let inline private exitBlock context =
    { context with Blocks = List.tail context.Blocks }

let inline private insertDef handler def context =
    let newSymbolTable = Map.add handler def context.SymbolTable
    let currentBlock = List.head context.Blocks

    let updatedBlock =
        { currentBlock with SymbolTable = Map.add def.ID handler currentBlock.SymbolTable }

    { context with SymbolTable = newSymbolTable; Blocks = updatedBlock :: List.tail context.Blocks }

let inline private insertDefs handlers defs context =
    let newSymbolTable =
        (handlers, defs)
        ||> Seq.zip
        |> Seq.fold (fun symbolTable (handler, def) -> Map.add handler def symbolTable) context.SymbolTable

    let currentBlock = List.head context.Blocks

    let newCurrentSymbolTable =
        (defs, handlers)
        ||> Seq.zip
        |> Seq.fold (fun symbolTable (def, handler) -> Map.add def.ID handler symbolTable) currentBlock.SymbolTable

    let updatedBlock = { currentBlock with SymbolTable = newCurrentSymbolTable }

    { context with SymbolTable = newSymbolTable; Blocks = updatedBlock :: List.tail context.Blocks }

let inline private searchDef context identifier =
    context.Blocks
    |> List.tryFind (fun block -> Map.containsKey identifier block.SymbolTable)
    |> Option.map (fun block ->
        let handler = block.SymbolTable.[identifier]
        context.SymbolTable.[handler], handler)

let inline private makeConstInt (x: ^T) =
    { Inner = Int(int x); Type = Type.Int; Category = RValue; IsConst = true }

let inline private makeConstFloat (x: ^T) =
    { Inner = Float(single x); Type = Type.Float; Category = RValue; IsConst = true }

let private createParserRef () =
    let dummyParser =
        fun _ -> Impl.panic "A parser created by createParserRef was not initialized"

    let r = ref dummyParser
    let inline p stream = r.Value stream
    p, r

let inline private failParser message = fail (Message message)
let inline private isIdentStartChar c = Char.IsLetter c || c = '_'
let inline private isIdentChar c = Char.IsLetterOrDigit c || c = '_'
let private skipString s = pstring s >>% ()

let private cxxComment =
    skipString "//" .>> manyCharsTill anyChar (skipNewline <|> eof)

let private blockComment =
    skipString "/*" .>> manyCharsTill anyChar (skipString "*/")

let private ws = skipMany (choice [ cxxComment; blockComment; spaces1 ])
let private ch c = skipChar c .>> ws

let private pIdentifier =
    let pIdentStartChar = satisfy isIdentStartChar
    let pIdentChar = satisfy isIdentChar
    many1Chars2 pIdentStartChar pIdentChar .>> ws

module private Expressions =
    /// `ind` 即 Indicator function
    let inline private ind f (a: ^T) (b: ^T) = if f a b then 1 else 0

    let inline private checkType argMustInt ty (l: Expr) (r: Expr) =
        match l.Type, r.Type with
        | Type.Int, Type.Int -> Type.Int
        | Type.Int, Type.Float
        | Type.Float, Type.Int
        | Type.Float, Type.Float when not argMustInt -> ty
        | _ -> failwith "Invalid type of operands."

    let inline private binaryOpCheck
        argMustInt
        ty
        ([<InlineIfLambda>] fun1)
        ([<InlineIfLambda>] fun2)
        ([<InlineIfLambda>] fun3)
        ([<InlineIfLambda>] fun4)
        constructor
        (l: Expr)
        _
        (r: Expr)
        =
        let ty = checkType argMustInt ty l r

        let inner =
            match l.Inner, r.Inner with
            | Int l, Int r -> fun1 l r
            | Float l, Int r when not argMustInt -> fun2 l r
            | Int l, Float r when not argMustInt -> fun3 l r
            | Float l, Float r when not argMustInt -> fun4 l r
            | _ -> constructor struct (l, r)

        { Inner = inner; Type = ty; Category = RValue; IsConst = l.IsConst && r.IsConst }

    let private arithRelOpCheckBase ty constConstructor funInt funFloat =
        binaryOpCheck
            false
            ty
            (fun l r -> Int(funInt l r))
            (fun l r -> constConstructor (funFloat l (single r)))
            (fun l r -> constConstructor (funFloat (single l) r))
            (fun l r -> constConstructor (funFloat l r))

    let private arithOpCheck = arithRelOpCheckBase Type.Float Float
    let private relOpCheck = arithRelOpCheckBase Type.Int Int
    let inline private placeholder _ _ = unreachable ()

    let private intOpCheck fun_ =
        binaryOpCheck true Type.Int (fun l r -> Int(fun_ l r)) placeholder placeholder placeholder

    let private logicOpCheck funLogic =
        let inline genericFun (l: 'T) (r: 'U) =
            Int(funLogic (l <> LanguagePrimitives.GenericZero<'T>) (r <> LanguagePrimitives.GenericZero<'U>))

        binaryOpCheck false Type.Int genericFun genericFun genericFun genericFun

    let inline private assignOpCheckBase mustInt constructor (l: Expr) _ (r: Expr) =
        if l.Category <> LValue then failwith "R-value on the left hand side of assign operator."
        let ty = checkType mustInt (if mustInt then l.Type else Type.Int) l r
        { Inner = constructor struct (l, r); Type = ty; Category = LValue; IsConst = false }

    let private assignOpCheck = assignOpCheckBase false
    let private intAssignOpCheck = assignOpCheckBase true

    let private rightAssocInfixOps =
        [ "=", P1, assignOpCheck Assignment
          "+=", P1, assignOpCheck AddAssign
          "-=", P1, assignOpCheck SubAssign
          "*=", P1, assignOpCheck MulAssign
          "/=", P1, assignOpCheck DivAssign
          "%=", P1, intAssignOpCheck ModAssign
          "&=", P1, intAssignOpCheck AndAssign
          "|=", P1, intAssignOpCheck OrAssign
          "^=", P1, intAssignOpCheck XorAssign
          "<<=", P1, intAssignOpCheck ShLAssign
          ">>=", P1, intAssignOpCheck SaRAssign ]

    let private leftAssocInfixOps =
        [ "||", P2, logicOpCheck (ind (||)) LogicOr

          "&&", P3, logicOpCheck (ind (&&)) LogicAnd

          "^", P4, intOpCheck (^^^) Xor

          "|", P5, intOpCheck (|||) Or

          "&", P6, intOpCheck (&&&) And

          "==", P7, relOpCheck (ind (=)) (ind (=)) Eq
          "!=", P7, relOpCheck (ind (<>)) (ind (<>)) Neq

          "<", P8, relOpCheck (ind (<)) (ind (<)) Les
          ">", P8, relOpCheck (ind (>)) (ind (>)) Grt
          "<=", P8, relOpCheck (ind (<=)) (ind (<=)) Leq
          ">=", P8, relOpCheck (ind (>=)) (ind (>=)) Geq

          "<<", P9, intOpCheck (<<<) ShL
          ">>", P9, intOpCheck (>>>) SaR

          "+", P10, arithOpCheck (+) (+) Add
          "-", P10, arithOpCheck (-) (-) Sub

          "*", P11, arithOpCheck (*) (*) Mul
          "/", P11, arithOpCheck (/) (/) Div
          "%", P11, intOpCheck (%) Mod ]

    let private checkLogicNot _ (expr: Expr) =
        if not (expr.Type.IsInt || expr.Type.IsFloat) then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int(ind (=) i 0)
            | Float f -> Int(ind (=) f 0.0f)
            | _ -> LogicNot expr

        { Inner = inner; Type = Type.Int; Category = RValue; IsConst = expr.IsConst }

    let private checkNeg _ (expr: Expr) =
        if not (expr.Type.IsInt || expr.Type.IsFloat) then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int -i
            | Float f -> Float -f
            | _ -> Neg expr

        { Inner = inner; Type = expr.Type; Category = RValue; IsConst = expr.IsConst }

    let private checkNot _ (expr: Expr) =
        if not expr.Type.IsInt then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int ~~~i
            | _ -> Not expr

        { Inner = inner; Type = Type.Int; Category = RValue; IsConst = expr.IsConst }

    let private prefixOps =
        [ "!", P12, checkLogicNot
          "+", P12, fun _ (expr: Expr) -> expr
          "-", P12, checkNeg
          "~", P12, checkNot ]

    let inline private op s = pstring s .>> ws
    let inline private makeOpBase con (symbol, prec: Precedence, map: ^T) = con symbol prec (op symbol) map
    let private makeLeftAssocInfixOp = makeOpBase Operator.infixLeftAssoc
    let private makeRightAssocInfixOp = makeOpBase Operator.infixRightAssoc
    let private makePrefixOp = makeOpBase Operator.prefix

    let private operators: Operators<string, unit, Expr, char, Context, ReadableString> =
        let brackets =
            Operator.enclosedBy "(" ")" P30 (op "(") (op ")") (fun _ expr _ -> expr)

        let ops =
            seq {
                yield! rightAssocInfixOps |> Seq.map makeRightAssocInfixOp
                yield! leftAssocInfixOps |> Seq.map makeLeftAssocInfixOp
                yield! prefixOps |> Seq.map makePrefixOp
                yield brackets
            }

        Operator.create ops

    let private literal =
        let cvtInt (fromBase: int) value =
            if value = "" then 0 else Convert.ToInt32(value, fromBase)

        let binDigit = satisfy (fun c -> c = '0' || c = '1')
        let octDigit = satisfy (fun c -> c >= '0' && c <= '7')
        let nonZeroDecDigit = satisfy (fun c -> c >= '1' && c <= '9')
        let hexDigit = satisfy Char.IsAsciiHexDigit

        let inline intBase pPrefix pDigits fromBase =
            pPrefix .>>. pDigits
            |>> fun struct (prefix, digits) -> $"{prefix}{digits}" |> cvtInt fromBase

        let inline intPrefix s = pstring s <|> pstring (s.ToUpper())
        let intHex = intBase (intPrefix "0x") (many1Chars hexDigit) 16
        let intOct = intBase (pchar '0') (manyChars octDigit) 8
        let intBin = intBase (intPrefix "0b") (many1Chars binDigit) 2
        let intDec = intBase nonZeroDecDigit (manyChars digit) 10
        let intLiteral = choice [ intHex; intBin; intOct; intDec ] |>> makeConstInt

        let floatLiteral =
            let inline expBase expInd =
                anyOf [ expInd; Char.ToUpper expInd ] >>. opt (anyOf [ '+'; '-' ])
                .>>. many1Chars digit
                |>> fun struct (sign, digits) -> if sign = ValueSome '-' then -float digits else float digits

            let floatDecExp = expBase 'e' |>> Double.Exp10
            let floatHexExp = expBase 'p' |>> Double.Exp2

            let inline float1Base frac exp =
                pipe2 frac (opt exp |>> ValueOption.defaultValue 1.0) (*)

            let floatDec1 =
                float1Base
                    (manyChars digit .>> skipChar '.' .>>. many1Chars digit
                     |>> (fun struct (x, y) -> float $"{x}.{y}")
                     <|> (many1Chars digit .>> skipChar '.' |>> float))
                    floatDecExp

            let floatHex1 =
                float1Base
                    (intPrefix "0x" >>. manyChars hexDigit .>> skipChar '.' .>>. many1Chars hexDigit
                     |>> fun struct (x, y) ->
                         float (cvtInt 16 x) + float (cvtInt 16 y) / Double.Exp2(float y.Length * 4.0))
                    floatHexExp

            let inline float2Base pHead pDigits = pipe2 (pHead |>> float) pDigits (*)
            let floatDec2 = float2Base (many1Chars digit) floatDecExp
            let floatHex2 = float2Base intHex floatHexExp
            choice [ floatHex1; floatHex2; floatDec1; floatDec2 ] |>> makeConstFloat

        choice [ floatLiteral; intLiteral ] .>> ws

    let private identifier =
        pIdentifier .>>. getUserState
        >>= fun struct (id, context) ->
            match searchDef context id with
            | Some(def, handler) ->
                preturn { Inner = Var handler; Type = def.Type; Category = LValue; IsConst = def.IsConst }
            | None -> failParser $"Undefined identifier: {id}"

    let expr, private exprRef = createParserRef ()

    let private arrayAccess =
        let intExpr =
            expr
            >>= function
                | { Expr.Type = Type.Int } as expr -> preturn expr
                | _ -> failParser "Expecting an expression of type `int`."
        // let inline checkPointer indices handler baseType dims init =

        pIdentifier .>>. many1 (between (ch '[') (ch ']') intExpr)

    let private functionCall =
        tuple3 pIdentifier (between (ch '(') (ch ')') (sepBy expr (ch ','))) getUserState
        >>= fun struct (id, args, context) ->
            let struct (args, _) = args

            match searchDef context id with
            | Some(def, handler) ->
                match def.Type with
                | Type.Function(retType, paramTypes) ->
                    if paramTypes.Length <> args.Length then
                        failParser $"Function `{id}` expects {paramTypes.Length} arguments, but got {args.Length}."
                    else if not (Seq.forall2 typeCastable (args |> Seq.map _.Type) paramTypes) then
                        failParser $"Function `{id}` argument type mismatch."
                    else
                        preturn { Inner = AST.Func(handler, args); Type = retType; Category = RValue; IsConst = false }
                | _ -> failParser $"`{id}` is not a function."
            | None -> failParser $"Undefined identifier: {id}"

    let private pAtom = choice [ identifier; literal ]
    exprRef.Value <- Operator.parser pAtom operators

open Expressions

let inline private keyword keyword_ =
    pstring keyword_ .>> notFollowedBy (satisfy isIdentChar) .>> ws

let inline private breakContinueBase keyword_ ret =
    keyword keyword_ .>> ch ';' >>. userStateSatisfies isInLoop >>% ret
    <?> $"`{keyword_}` statement must be used in loop."

let private break_ = breakContinueBase "break" Break
let private continue_ = breakContinueBase "continue" Continue

let private return_ =
    let checkExpr context (expr: Expr) =
        match typeCastable expr.Type context.RetType with
        | true -> preturn (ValueSome expr)
        | false -> failParser "Return expression type mismatch."

    keyword "return" >>. getUserState
    >>= function
        | { RetType = Void } -> ch ';' >>% Return ValueNone
        | context -> expr .>> ch ';' >>= checkExpr context |>> Return

let private block, private blockRef = createParserRef ()
let private statement, private stmtRef = createParserRef ()
let private blockItem, private blockItemRef = createParserRef ()

let private manyBlockItem =
    let filter =
        function
        | Statement Statement.Empty -> false
        | _ -> true

    let builder = Seq.filter filter >> ImmutableArray.CreateRange
    many blockItem |>> builder

let private blockWithoutScope = between (ch '{') (ch '}') manyBlockItem

let private ifWhileHelper startLoopNow =
    between
        (updateUserState (enterBlock startLoopNow))
        (updateUserState exitBlock)
        (choice [ blockWithoutScope; statement |>> (Statement >> ImmutableArray.Create) ])

let private ifHelper = ifWhileHelper false
let private whileHelper = ifWhileHelper true

let private arithExpr =
    expr
    >>= function
        | { Type = Type.Int | Type.Float } as expr -> preturn expr
        | _ -> failParser "Expecting an expression of type `int` or `float`."

let private condExpr = between (ch '(') (ch ')') arithExpr

let private ifElse =
    tuple3
        (keyword "if" >>. condExpr)
        ifHelper
        (opt (keyword "else" >>. ifHelper)
         |>> ValueOption.defaultValue ImmutableArray.Empty)
    |>> If

let private whileLoop = keyword "while" >>. condExpr .>>. whileHelper |>> While

// 必须先 `ch '{'`，再更新 `context`
blockRef.Value <-
    between (ch '{' >>. updateUserState (enterBlock false)) (ch '}' >>. updateUserState exitBlock) manyBlockItem

stmtRef.Value <-
    let exprStmt = expr .>> ch ';' |>> Statement.Expr
    let emptyStmt = ch ';' >>% Statement.Empty
    choice [ whileLoop; ifElse; continue_; break_; return_; exprStmt; emptyStmt ]

blockItemRef.Value <- choice [ block |>> AST.Block; statement |>> Statement ]

let parse path =
    let sysyLib =
        [ Type.Function(Type.Int, ImmutableArray.Empty), "getint"
          Type.Function(Type.Int, ImmutableArray.Empty), "getch"
          Type.Function(Type.Float, ImmutableArray.Empty), "getfloat"
          Type.Function(Type.Int, ImmutableArray.CreateRange [ Pointer Type.Int ]), "getarray"
          Type.Function(Type.Int, ImmutableArray.CreateRange [ Pointer Type.Float ]), "getfarray"
          Type.Function(Type.Void, ImmutableArray.CreateRange [ Type.Int ]), "putint"
          Type.Function(Type.Void, ImmutableArray.CreateRange [ Type.Int ]), "putch"
          Type.Function(Type.Void, ImmutableArray.CreateRange [ Type.Float ]), "putfloat"
          Type.Function(Type.Void, ImmutableArray.CreateRange [ Type.Int; Pointer Type.Int ]), "putarray"
          Type.Function(Type.Void, ImmutableArray.CreateRange [ Type.Int; Pointer Type.Float ]), "putfarray" ]

    let handlers = List.init (List.length sysyLib) (fun _ -> counter ())

    let globalSymbolTable =
        sysyLib
        |> Seq.map (fun (ty, name) ->
            { Init = ValueNone; Type = ty; ID = name; IsConst = false; IsArg = false; IsGlobal = true })
        |> Seq.zip handlers
        |> Map.ofSeq

    let symbolTable = Seq.zip (Seq.map snd sysyLib) handlers |> Map.ofSeq

    let reader =
        Reader.ofString
            (IO.File.ReadAllText(path, Text.Encoding.UTF8))
            { SymbolTable = globalSymbolTable
              RetType = Type.Void
              ParsingType = Type.Int
              Blocks = [ { SymbolTable = symbolTable; InLoop = false } ] }

    let parser = ws >>. expr .>> eof .>>. getUserState

    match parser reader with
    | Ok(expr, context) -> Ok({ Ast = []; SymbolTable = context.SymbolTable }, expr)
    | Error err -> Error $"Parse error: {err}"


module private Definitions =
    let private int_ = keyword "int" >>% Type.Int
    let private float_ = keyword "float" >>% Type.Float
    let private void_ = keyword "void" >>% Type.Void
    let private type_ = choiceL [ int_; float_; void_ ] "a type."
    let private nonVoidType = choiceL [ int_; float_ ] "a non-void type."

    // 正整数常量表达式，用于数组维度等场景。
    let private posiConstInt =
        expr
        >>= function
            | { Inner = Int i } when i > 0 -> preturn i
            | _ -> failParser "Expecting a positive integer constant."

    let private constExpr =
        expr
        >>= function
            | { IsConst = true } as e -> preturn e
            | _ -> failParser "Expecting a constant expression."
