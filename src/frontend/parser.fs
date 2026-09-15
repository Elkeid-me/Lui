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

type private ImmutableArray<'T> with
    member this.Eq(other: ImmutableArray<'T>) =
        if this.IsDefault || other.IsDefault then
            this.IsDefault = other.IsDefault
        else
            this.AsSpan().SequenceEqual(other.AsSpan())

let private createCounter (init: uint32) =
    let mutable count = init

    fun () ->
        count <- count + 1u
        count

let private counter = createCounter 0u

// 使用 `Map` 而不是哈希表，保持纯函数式，避免在解析过程中出现副作用。
type BlockInfo = { SymbolTable: Map<string, Handler>; InLoop: bool }

/// - `Counter`: 生成唯一标识符的计数器。
/// - `SymbolTable`: 全局的符号表，存储 `Handler` 到 `Definition` 的映射，即所有局部、全局定义或声明。
/// - `RetType`: 当前函数的返回类型。
/// - `Blocks`: 当前作用域栈，每个作用域包含一个符号表和是否在循环内的信息。
type Context = { SymbolTable: SymbolTableType; RetType: AST.Type; Blocks: BlockInfo list }

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
        let handler = block.SymbolTable[identifier]
        context.SymbolTable[handler], handler)

let private currentExist context identifier =
    Map.containsKey identifier (List.head context.Blocks).SymbolTable

let inline private makeConstInt (x: ^T) =
    { Inner = Int(int x); Type = Type.Int; Category = ValueCategory.R; IsConst = true }

let inline private makeConstFloat (x: ^T) =
    { Inner = Float(single x); Type = Type.Float; Category = ValueCategory.R; IsConst = true }

let private createParserRef () =
    let dummyParser =
        fun _ -> Impl.panic "A parser created by createParserRef was not initialized"

    let reference = ref dummyParser
    let inline parser stream = reference.Value stream
    parser, reference

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
        | _ -> failwith $"Invalid type of operands. {l} and {r}."

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

        { Inner = inner; Type = ty; Category = ValueCategory.R; IsConst = l.IsConst && r.IsConst }

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
        let inline genericFun (l: ^T) (r: ^U) =
            Int(funLogic (l <> LanguagePrimitives.GenericZero< ^T>) (r <> LanguagePrimitives.GenericZero< ^U>))

        binaryOpCheck false Type.Int genericFun genericFun genericFun genericFun

    let inline private assignOpCheckBase mustInt constructor (l: Expr) _ (r: Expr) =
        if l.Category <> ValueCategory.L then failwith "R-value on the left hand side of assign operator."
        let ty = checkType mustInt (if mustInt then l.Type else Type.Int) l r
        { Inner = constructor struct (l, r); Type = ty; Category = ValueCategory.L; IsConst = false }

    let private assignOpCheck = assignOpCheckBase false
    let private intAssignOpCheck = assignOpCheckBase true

    let private rightAssocInfixOps =
        [ "=", [ '=' ], P1, assignOpCheck Assignment
          "+=", [], P1, assignOpCheck AddAssign
          "-=", [], P1, assignOpCheck SubAssign
          "*=", [], P1, assignOpCheck MulAssign
          "/=", [], P1, assignOpCheck DivAssign
          "%=", [], P1, intAssignOpCheck ModAssign
          "&=", [], P1, intAssignOpCheck AndAssign
          "|=", [], P1, intAssignOpCheck OrAssign
          "^=", [], P1, intAssignOpCheck XorAssign
          "<<=", [], P1, intAssignOpCheck ShLAssign
          ">>=", [], P1, intAssignOpCheck SaRAssign ]

    let private leftAssocInfixOps =
        [ "||", [], P2, logicOpCheck (ind (||)) LogicOr

          "&&", [], P3, logicOpCheck (ind (&&)) LogicAnd

          "^", [ '=' ], P4, intOpCheck (^^^) Xor

          "|", [ '|'; '=' ], P5, intOpCheck (|||) Or

          "&", [ '&'; '=' ], P6, intOpCheck (&&&) And

          "==", [], P7, relOpCheck (ind (=)) (ind (=)) Eq
          "!=", [], P7, relOpCheck (ind (<>)) (ind (<>)) Neq

          "<", [ '<'; '=' ], P8, relOpCheck (ind (<)) (ind (<)) Les
          ">", [ '>'; '=' ], P8, relOpCheck (ind (>)) (ind (>)) Grt
          "<=", [], P8, relOpCheck (ind (<=)) (ind (<=)) Leq
          ">=", [], P8, relOpCheck (ind (>=)) (ind (>=)) Geq

          "<<", [ '=' ], P9, intOpCheck (<<<) ShL
          ">>", [ '=' ], P9, intOpCheck (>>>) SaR

          "+", [ '+'; '=' ], P10, arithOpCheck (+) (+) Add
          "-", [ '-'; '=' ], P10, arithOpCheck (-) (-) Sub

          "*", [ '=' ], P11, arithOpCheck (*) (*) Mul
          "/", [ '=' ], P11, arithOpCheck (/) (/) Div
          "%", [ '=' ], P11, intOpCheck (%) Mod ]

    let private checkLogicNot _ (expr: Expr) =
        if not (expr.Type.IsInt || expr.Type.IsFloat) then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int(ind (=) i 0)
            | Float f -> Int(ind (=) f 0.0f)
            | _ -> LogicNot expr

        { Inner = inner; Type = Type.Int; Category = ValueCategory.R; IsConst = expr.IsConst }

    let private checkNeg _ (expr: Expr) =
        if not (expr.Type.IsInt || expr.Type.IsFloat) then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int -i
            | Float f -> Float -f
            | _ -> Neg expr

        { Inner = inner; Type = expr.Type; Category = ValueCategory.R; IsConst = expr.IsConst }

    let private checkNot _ (expr: Expr) =
        if not expr.Type.IsInt then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int ~~~i
            | _ -> Not expr

        { Inner = inner; Type = Type.Int; Category = ValueCategory.R; IsConst = expr.IsConst }

    let private prefixOps =
        [ "!", [ '=' ], P12, checkLogicNot
          "+", [ '+'; '=' ], P12, fun _ (expr: Expr) -> expr
          "-", [ '-'; '=' ], P12, checkNeg
          "~", [], P12, checkNot ]

    let inline private op s notFollowedChar =
        pstring s .>> notFollowedBy (anyOf notFollowedChar) .>> ws

    let inline private makeOpBase con (symbol, notFollowedChar, prec: Precedence, map: ^T) =
        con symbol prec (op symbol notFollowedChar) map

    let private makeLeftAssocInfixOp = makeOpBase Operator.infixLeftAssoc
    let private makeRightAssocInfixOp = makeOpBase Operator.infixRightAssoc
    let private makePrefixOp = makeOpBase Operator.prefix

    let private operators: Operators<string, unit, Expr, char, Context, ReadableString> =
        let brackets =
            Operator.enclosedBy "(" ")" P30 (op "(" []) (op ")" []) (fun _ expr _ -> expr)

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

    let inline private toConstByType x =
        function
        | Type.Int -> makeConstInt x
        | Type.Float -> makeConstFloat x
        | _ -> unreachable ()

    let private identifier =
        pIdentifier .>>. getUserState
        >>= fun struct (id, context) ->
            match searchDef context id with
            | Some({ Init = ValueSome(Expr { Inner = Int i }); Type = ty; IsConst = true }, _) ->
                toConstByType i ty |> preturn
            | Some({ Init = ValueSome(Expr { Inner = Float f }); Type = ty; IsConst = true }, _) ->
                toConstByType f ty |> preturn
            | Some(def, handler) ->
                preturn { Inner = Var handler; Type = def.Type; Category = ValueCategory.L; IsConst = def.IsConst }
            | None -> failParser $"Undefined identifier: {id}"

    let expr, private exprRef = createParserRef ()

    let private arrayAccess =
        let intExpr =
            expr
            >>= function
                | { Expr.Type = Type.Int } as expr -> preturn expr
                | _ -> failParser "Expecting an expression of type `int`."

        let inline checkPointer (indices: ImmutableArray<Expr>) handler def =
            let rec pointerDimsLength =
                function
                | Pointer baseType
                | Array(baseType, _) -> 1 + pointerDimsLength baseType
                | _ -> 0

            let rec typeAfterIndices count ty =
                if count = 0 then
                    ty
                else
                    match ty with
                    | Pointer baseType
                    | Array(baseType, _) -> typeAfterIndices (count - 1) baseType
                    | _ -> unreachable ()

            let defaultValue () =
                match typeAfterIndices indices.Length def.Type with
                | Type.Int -> makeConstInt 0
                | Type.Float -> makeConstFloat 0.0f
                | _ -> unreachable ()

            let tryGetConstValue init ty =
                if not (indices |> Seq.forall _.Inner.IsInt) then
                    ValueNone
                else
                    let rec getElementByIndices (items: InitList) remaining =
                        match remaining with
                        | [ { Inner = Int index } ] ->
                            match Seq.tryItem index items with
                            | Some(InitListItem.Expr { Inner = Int value }) -> toConstByType value ty
                            | Some(InitListItem.Expr { Inner = Float value }) -> toConstByType value ty
                            | _ -> defaultValue ()
                        | { Inner = Int index } :: tail ->
                            match Seq.tryItem index items with
                            | Some(InitListItem.InitList nested) -> getElementByIndices nested tail
                            | _ -> defaultValue ()
                        | _ -> unreachable ()

                    getElementByIndices init (indices |> Seq.toList) |> ValueSome

            let dimsLength = pointerDimsLength def.Type
            let ty = typeAfterIndices indices.Length def.Type
            let possibleInner = ArrayElem struct (handler, indices)

            if indices.Length > dimsLength then
                failParser $"Too many indices for array or pointer `{def.ID}`."
            elif indices.Length < dimsLength then
                if def.IsConst then
                    failParser $"Too few indices for const array access `{def.ID}`."
                else
                    preturn { Inner = possibleInner; Type = ty; Category = ValueCategory.R; IsConst = false }
            elif def.IsConst then
                match def.Init with
                | ValueSome(List init) ->
                    match tryGetConstValue init ty with
                    | ValueSome value -> preturn value
                    | ValueNone ->
                        preturn { Inner = possibleInner; Type = ty; Category = ValueCategory.R; IsConst = false }
                | _ -> unreachable ()
            else
                preturn { Inner = possibleInner; Type = ty; Category = ValueCategory.L; IsConst = false }

        tuple3 pIdentifier (many1 (between (ch '[') (ch ']') intExpr)) getUserState
        >>= fun struct (id, indices, context) ->
            match searchDef context id with
            | Some({ Init = ValueSome(List _) } as def, handler) -> checkPointer indices handler def
            | Some({ Type = Array(_, _) | Pointer _ } as def, handler) -> checkPointer indices handler def
            | Some _ -> failParser $"`{id}` is not an array or pointer."
            | None -> failParser $"Undefined identifier: `{id}`."


    let private functionCall =
        tuple3 pIdentifier (between (ch '(') (ch ')') (sepBy expr (ch ',')) |>> structFst) getUserState
        >>= fun struct (id, args, context) ->
            match searchDef context id with
            | Some(def, handler) ->
                match def.Type with
                | Type.Function(retType, paramTypes) ->
                    if paramTypes.Length <> args.Length then
                        failParser $"Function `{id}` expects {paramTypes.Length} arguments, but got {args.Length}."
                    elif not (Seq.forall2 typeCastable (args |> Seq.map _.Type) paramTypes) then
                        failParser $"Function `{id}` argument type mismatch."
                    else
                        preturn
                            { Inner = AST.Func(handler, args)
                              Type = retType
                              Category = ValueCategory.R
                              IsConst = false }
                | _ -> failParser $"`{id}` is not a function."
            | None -> failParser $"Undefined identifier: {id}"

    let private pAtom = choice [ functionCall; arrayAccess; identifier; literal ]
    exprRef.Value <- Operator.parser pAtom operators

open Expressions

let inline private keyword keyword_ =
    pstring keyword_ .>> notFollowedBy (satisfy isIdentChar) .>> ws

let inline private breakContinueBase keyword_ ret =
    keyword keyword_ >>. ch ';' >>. userStateSatisfies isInLoop >>% ret
    <?> $"`{keyword_}` statement must be used in loop."

let private break_ = breakContinueBase "break" Break
let private continue_ = breakContinueBase "continue" Continue

let private return_ =
    let inline checkExpr context (expr: Expr) =
        match typeCastable expr.Type context.RetType with
        | true -> expr |> ValueSome |> preturn
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

    many blockItem |>> (Seq.filter filter >> ImmutableArray.CreateRange)

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
            | { Inner = Int i } when i > 0 -> i |> uint64 |> preturn
            | _ -> failParser "Expecting a positive integer constant."

    let private constExpr =
        expr
        >>= function
            | { Inner = Int _ | Float _ } as expr -> preturn expr
            | _ -> failParser "Expecting a constant expression."

    let inline private makeVarDef isConst baseType name arrDimOpt initOpt =
        getUserState
        >>= fun context ->
            if currentExist context name then
                failParser $"Redefinition of identifier: `{name}`."
            else
                let ty =
                    match arrDimOpt with
                    | ValueSome dim -> Seq.foldBack (fun d ty -> Type.Array(ty, d)) dim baseType
                    | ValueNone -> baseType

                let handler = counter ()
                let isGlobal = isGlobal context

                let def =
                    { Init = initOpt; Type = ty; ID = name; IsConst = isConst; IsParam = false; IsGlobal = isGlobal }

                updateUserState (insertDef handler def) >>% handler

    let private initListItem, private initListItemRef = createParserRef ()
    let private constInitListItem, private constInitListItemRef = createParserRef ()

    let private initList =
        between (ch '{') (ch '}') (sepBy initListItem (ch ',') |>> structFst)

    let private constInitList =
        between (ch '{') (ch '}') (sepBy constInitListItem (ch ',') |>> structFst)

    initListItemRef.Value <- choice [ initList |>> InitListItem.InitList; arithExpr |>> InitListItem.Expr ]
    constInitListItemRef.Value <- choice [ constInitList |>> InitListItem.InitList; constExpr |>> InitListItem.Expr ]

    type private InitBuilderItem =
        | Expr of Expr
        | InitList of ImmutableArray<InitBuilderItem>.Builder

    type private InitBuilder = ImmutableArray<InitBuilderItem>.Builder

    let inline private processInitList (arrDim: ImmutableArray<uint64>) (initList: InitList) =
        let dimsProd =
            (arrDim, 1UL) ||> Seq.scanBack (*) |> Seq.take arrDim.Length |> Seq.toList

        let inline createBuilder initLength =
            ImmutableArray.CreateBuilder<InitBuilderItem> initLength

        let inline wrap items = InitList items
        let inline emptyBuilder () = wrap (createBuilder 0)

        let rec toBuilder (items: InitList) =
            let builder: InitBuilder =
                (createBuilder items.Length, items)
                ||> Seq.fold (fun builder item ->
                    match item with
                    | InitListItem.Expr expr -> builder.Add(Expr expr)
                    | InitListItem.InitList subItems -> builder.Add(wrap (toBuilder subItems))

                    builder)

            builder

        let rec toImmutable (builder: InitBuilder) =
            let result: ImmutableArray<InitListItem>.Builder =
                (ImmutableArray.CreateBuilder<InitListItem> builder.Count, builder)
                ||> Seq.fold (fun result item ->
                    match item with
                    | Expr expr -> result.Add(InitListItem.Expr expr)
                    | InitList subBuilder -> result.Add(InitListItem.InitList(toImmutable subBuilder))

                    result)

            result.ToImmutable()

        /// `makeListWithDimsProd`: 基于给定的 `dimsProd`，将 `initList` 转换为符合数组维度的初始化列表。
        let rec makeListWithDimsProd dimsProd (currentInitList: InitBuilder) =
            let rec insertLeaf (items: InitBuilder) dimsProd sum leaf =
                match dimsProd with
                | [] ->
                    items.Add(Expr leaf)
                    1UL
                | dimensionProduct :: tail ->
                    if items.Count = 0 || sum % dimensionProduct = 0UL then items.Add(emptyBuilder ())

                    match items[items.Count - 1] with
                    | InitList head -> insertLeaf head tail sum leaf
                    | _ -> unreachable ()

            let rec insertSubList (items: InitBuilder) dimsProd sum subItems =
                match dimsProd with
                | [] -> failwith "Too many initializer lists."
                | _ :: subProd :: _ when sum % subProd = 0UL ->
                    let processedSub = makeListWithDimsProd (List.tail dimsProd) subItems

                    items.Add(wrap processedSub)
                    subProd
                | _ ->
                    if items.Count = 0 then items.Add(emptyBuilder ())

                    match items[items.Count - 1] with
                    | InitList head -> insertSubList head (List.tail dimsProd) sum subItems
                    | _ -> failwith "Initializer list does not match array dimensions."

            let insert (sum, builder) initElem =
                let subSum =
                    match initElem with
                    | Expr leaf -> insertLeaf builder (List.tail dimsProd) sum leaf
                    | InitList subInitList -> insertSubList builder dimsProd sum subInitList

                let newSum = sum + subSum
                if newSum > List.head dimsProd then failwith "Too many initializers."
                newSum, builder

            let builder = createBuilder currentInitList.Count
            ((0UL, builder), currentInitList) ||> Seq.fold insert |> snd

        initList |> toBuilder |> makeListWithDimsProd dimsProd |> toImmutable |> List

    let private variable =
        tuple3 (opt (keyword "const" >>% ())) nonVoidType (opt (keyword "const" >>% ()))
        >>= fun struct (const1, ty, const2) ->
            if ValueOption.isSome const1 || ValueOption.isSome const2 then
                let constArrayDef =
                    tuple3 pIdentifier (many1 (between (ch '[') (ch ']') posiConstInt)) (ch '=' >>. constInitList)
                    >>= fun struct (name, arrDim, init) ->
                        makeVarDef true ty name (ValueSome arrDim) (ValueSome(processInitList arrDim init))

                let constVarDef =
                    pIdentifier .>> ch '=' .>>. constExpr
                    >>= fun struct (name, init) -> makeVarDef true ty name ValueNone (ValueSome(AST.Init.Expr init))

                sepBy1 (constArrayDef <|> constVarDef) (ch ',') .>> ch ';' |>> structFst
            else
                let arrayDef =
                    tuple3 pIdentifier (many1 (between (ch '[') (ch ']') posiConstInt)) (opt (ch '=' >>. initList))
                    >>= fun struct (name, arrDim, init) ->
                        makeVarDef false ty name (ValueSome arrDim) (ValueOption.map (processInitList arrDim) init)

                let varDef =
                    pIdentifier .>>. opt (ch '=' >>. expr)
                    >>= fun struct (name, init) ->
                        makeVarDef false ty name ValueNone (ValueOption.map AST.Init.Expr init)

                sepBy1 (arrayDef <|> varDef) (ch ',') .>> ch ';' |>> structFst

    let private param =
        tuple3 nonVoidType pIdentifier (opt (ch '[' >>. ch ']' >>. many (between (ch '[') (ch ']') posiConstInt)))
        |>> fun struct (baseType, name, ptrDimOpt) ->
            let ty =
                match ptrDimOpt with
                | ValueSome dim -> (dim, baseType) ||> Seq.foldBack (fun d ty -> Type.Array(ty, d)) |> Pointer
                | ValueNone -> baseType

            struct (ty, name)

    // 考虑到同一函数可能多次声明，因此这里用 `newRetType`，以表示与可能已存储的 `retType` 区分。
    let inline private makeFuncDecl newRetType name (newParams: ImmutableArray<struct (AST.Type * string)>) context =
        let parseInitial =
            let paramTypes = newParams |> Seq.map structFst |> ImmutableArray.CreateRange

            match searchDef context name with
            | Some(def, _) ->
                match def.Type with
                | Type.Function(retType, paramTypes) when retType = newRetType && paramTypes.Eq paramTypes ->
                    preturn ImmutableArray.Empty
                | _ -> failParser $"Conflicting types for `{name}`."
            | None ->
                let handler = counter ()
                let ty = Type.Function(newRetType, paramTypes)

                let def =
                    // TODO: 暂不允许函数在局部作用域声明
                    { Init = ValueNone; Type = ty; ID = name; IsGlobal = true; IsParam = false; IsConst = false }

                updateUserState (insertDef handler def) >>. preturn ImmutableArray.Empty

        parseInitial .>> ch ';'

    let private makeFuncDef newRetType name (newParams: ImmutableArray<struct (AST.Type * string)>) context =
        let paramHandlers =
            Seq.init newParams.Length (fun _ -> counter ()) |> ImmutableArray.CreateRange

        let paramTypes = newParams |> Seq.map structFst |> ImmutableArray.CreateRange

        let paramDefs =
            newParams
            |> Seq.map (fun struct (ty, id) ->
                { Init = ValueNone; Type = ty; ID = id; IsGlobal = false; IsParam = true; IsConst = false })

        let ty = Type.Function(newRetType, paramTypes)

        let makeDef body =
            let init = ValueSome(Function { Block = body; ArgHandlers = paramHandlers })
            { Init = init; Type = ty; ID = name; IsGlobal = true; IsParam = false; IsConst = false }

        let contextUpdateParser, handler =
            match searchDef context name with
            | None ->
                let handler = counter ()

                let contextUpdateFunction =
                    insertDef handler (makeDef ImmutableArray.Empty)
                    >> enterFuncBody newRetType
                    >> insertDefs paramHandlers paramDefs

                updateUserState contextUpdateFunction, handler
            | Some({ Type = Type.Function(retType, paramTypes); Init = ValueNone }, handler) when
                retType = newRetType && paramTypes.Eq paramTypes
                ->
                updateUserState (enterFuncBody newRetType >> insertDefs paramHandlers paramDefs), handler
            | _ -> failParser $"Conflicting types for `{name}`.", 0u // 0 是占位符

        contextUpdateParser >>. blockWithoutScope .>> updateUserState exitBlock
        >>= (fun body ->
            updateUserState (fun context ->
                { context with SymbolTable = Map.add handler (makeDef body) context.SymbolTable }))
        >>. (handler |> ImmutableArray.Create |> preturn)

    let private functionDef =
        tuple5
            type_
            pIdentifier
            (between (ch '(') (ch ')') (sepBy param (ch ',')) |>> structFst)
            (choice
                [ followedBy (lookAhead (ch ';')) >>% true
                  followedBy (lookAhead (ch '{')) >>% false ])
            getUserState
        >>= fun struct (retType, id, params_, isDecl, context) ->
            if not (isGlobal context) then
                failParser "Function definition is not allowed in local scope."
            elif isDecl then
                makeFuncDecl retType id params_ context
            else
                makeFuncDef retType id params_ context

    let defs = choice [ functionDef; variable ]

blockItemRef.Value <- choice [ block |>> AST.Block; Definitions.defs |>> Def; statement |>> Statement ]

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
            { Init = ValueNone; Type = ty; ID = name; IsConst = false; IsParam = false; IsGlobal = true })
        |> Seq.zip handlers
        |> Map.ofSeq

    let symbolTable = Seq.zip (Seq.map snd sysyLib) handlers |> Map.ofSeq

    let reader =
        Reader.ofString
            (IO.File.ReadAllText(path, Text.Encoding.UTF8))
            { SymbolTable = globalSymbolTable
              RetType = Type.Void
              Blocks = [ { SymbolTable = symbolTable; InLoop = false } ] }

    let parser = ws >>. many Definitions.defs .>> eof .>>. getUserState

    match parser reader with
    | Ok struct (defs, context) ->
        Ok { Ast = defs |> Seq.concat |> ImmutableArray.CreateRange; SymbolTable = context.SymbolTable }
    | Error err -> Error $"Parse error: {err}"
