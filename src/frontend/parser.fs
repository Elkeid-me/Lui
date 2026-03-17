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
open FParsec
open Utils

let private createCounter () =
    let mutable count = 0u

    fun () ->
        count <- count + 1u
        count

type BlockInfo = { SymbolTable: Map<string, Handler>; InLoop: bool }

/// - `Counter`: 生成唯一标识符的计数器。
/// - `SymbolTable`: 全局的符号表，存储 `Handler` 到 `Definition` 的映射。
/// - `RetType`: 当前函数的返回类型。
/// - `Blocks`: 当前作用域栈，每个作用域包含一个符号表和是否在循环内的信息。
/// - `ParsingType`: 当前正在解析的基础类型（用于处理类型声明）。
///
///   注意，解析数组声明时，仍然使用数组元素类型作为 `ParsingType`。
type Context =
    { Counter: unit -> uint
      SymbolTable: Map<Handler, Definition>
      RetType: Type
      Blocks: BlockInfo list
      ParsingType: Type }

let private isInLoop context = (List.head context.Blocks).InLoop

let private isGlobal context =
    match context.Blocks with
    | [ _ ] -> true
    | _ -> false

let private enterBlock startLoopNow context =
    let inLoop = startLoopNow || isInLoop context
    { context with Blocks = { SymbolTable = Map.empty; InLoop = inLoop } :: context.Blocks }

let private enterFuncBody retType context =
    { context with RetType = retType; Blocks = { SymbolTable = Map.empty; InLoop = false } :: context.Blocks }

let private exitBlock context =
    { context with Blocks = List.tail context.Blocks }

let private insertDef handler def context =
    let newSymbolTable = Map.add handler def context.SymbolTable
    let currentBlock = List.head context.Blocks

    let updatedBlock =
        { currentBlock with SymbolTable = Map.add def.ID handler currentBlock.SymbolTable }

    { context with SymbolTable = newSymbolTable; Blocks = updatedBlock :: List.tail context.Blocks }

let private searchDef context identifier =
    context.Blocks
    |> List.tryFind (fun block -> Map.containsKey identifier block.SymbolTable)
    |> Option.map (fun block ->
        let handler = block.SymbolTable.[identifier]
        context.SymbolTable.[handler], handler)

let inline private makeConstInt (x: 'T) =
    { Inner = Int(int x); Type = Type.Int; Category = RValue; IsConst = true }

let inline private makeConstFloat (x: 'T) =
    { Inner = Float(single x); Type = Type.Float; Category = RValue; IsConst = true }

let private cxxComment =
    skipString "//" .>> manyCharsTill anyChar (skipNewline <|> eof)

let private blockComment =
    skipString "/*" .>> manyCharsTill anyChar (skipString "*/")

let private ws = skipMany (choice [ cxxComment; blockComment; skipAnyOf " \t\n" ])
let private ch c = pchar c .>> ws

let private literal =
    let cvtInt (base_: int) int_ = System.Convert.ToInt32(int_, base_)
    let hexInt = regex @"0[xX][0-9a-fA-F]+" |>> (cvtInt 16 >> makeConstInt)
    let binInt = regex @"0[bB][01]+" |>> (cvtInt 2 >> makeConstInt)
    let octInt = regex @"0[0-7]*" |>> (cvtInt 8 >> makeConstInt)
    let decInt = regex @"[1-9]\d*" |>> (cvtInt 10 >> makeConstInt)

    let decFloat =
        regex @"(((\d*\.\d+)|(\d+\.))([eE][-+]?\d+)?)|((\d+)([eE][-+]?\d+))"
        |>> (single >> makeConstFloat)

    let hexFloat =
        regex @"0[xX](([0-9a-fA-F]*\.[0-9a-fA-F]+)|([0-9a-fA-F]+\.?))[pP][+-]?\d+"
        |>> (HexFloat.SingleFromHexString >> makeConstFloat)

    let pInt = choiceL [ hexInt; binInt; octInt; decInt ] "integer literal"
    let pFloat = choiceL [ hexFloat; decFloat ] "floating-point literal"

    pFloat <|> pInt .>> ws

module Operators =
    [<Literal>]
    let private Left = Associativity.Left

    [<Literal>]
    let private Right = Associativity.Right

    type InfixOperatorDetails = { Symbol: string; Prec: int; Assoc: Associativity; Map: Expr -> Expr -> Expr }

    let inline private lei f (a: 'T) (b: 'T) =
        if b = LanguagePrimitives.GenericZero<'T> then a else f a b

    /// `ind` 即 Indicator function
    let inline private ind f (a: 'T) (b: 'T) = if f a b then 1 else 0

    let checkType argMustInt ty (l: Expr) (r: Expr) =
        match l.Type, r.Type with
        | Type.Int, Type.Int -> Type.Int
        | Type.Int, Type.Float
        | Type.Float, Type.Int
        | Type.Float, Type.Float when not argMustInt -> ty
        | _ -> failwith "Invalid type of operands."

    let inline private binaryOpCheck argMustInt ty fun1 fun2 fun3 fun4 constructor (l: Expr) (r: Expr) =
        let ty = checkType argMustInt ty l r

        let inner =
            match l.Inner, r.Inner with
            | Int l, Int r -> fun1 l r
            | Float l, Int r when not argMustInt -> fun2 l r
            | Int l, Float r when not argMustInt -> fun3 l r
            | Float l, Float r when not argMustInt -> fun4 l r
            | _ -> constructor (l, r)

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

    let inline private assignOpCheckBase mustInt constructor (l: Expr) (r: Expr) =
        if l.Category <> LValue then failwith "R-value on the left hand side of assign operator."
        let ty = checkType mustInt (if mustInt then l.Type else Type.Int) l r
        { Inner = constructor (l, r); Type = ty; Category = LValue; IsConst = false }

    let private assignOpCheck = assignOpCheckBase false
    let private intAssignOpCheck = assignOpCheckBase true

    let infixOperators =
        [ { Symbol = "="; Prec = 1; Assoc = Right; Map = assignOpCheck Assignment }
          { Symbol = "+="; Prec = 1; Assoc = Right; Map = assignOpCheck AddAssign }
          { Symbol = "-="; Prec = 1; Assoc = Right; Map = assignOpCheck SubAssign }
          { Symbol = "*="; Prec = 1; Assoc = Right; Map = assignOpCheck MulAssign }
          { Symbol = "/="; Prec = 1; Assoc = Right; Map = assignOpCheck DivAssign }
          { Symbol = "%="; Prec = 1; Assoc = Right; Map = intAssignOpCheck ModAssign }
          { Symbol = "&="; Prec = 1; Assoc = Right; Map = intAssignOpCheck AndAssign }
          { Symbol = "|="; Prec = 1; Assoc = Right; Map = intAssignOpCheck OrAssign }
          { Symbol = "^="; Prec = 1; Assoc = Right; Map = intAssignOpCheck XorAssign }
          { Symbol = "<<="; Prec = 1; Assoc = Right; Map = intAssignOpCheck ShLAssign }
          { Symbol = ">>="; Prec = 1; Assoc = Right; Map = intAssignOpCheck SaRAssign }

          { Symbol = "||"; Prec = 2; Assoc = Left; Map = logicOpCheck (ind (||)) LogicOr }

          { Symbol = "&&"; Prec = 3; Assoc = Left; Map = logicOpCheck (ind (&&)) LogicAnd }

          { Symbol = "^"; Prec = 4; Assoc = Left; Map = intOpCheck (^^^) Xor }

          { Symbol = "|"; Prec = 5; Assoc = Left; Map = intOpCheck (|||) Or }

          { Symbol = "&"; Prec = 6; Assoc = Left; Map = intOpCheck (&&&) And }

          { Symbol = "=="; Prec = 7; Assoc = Left; Map = relOpCheck (ind (=)) (ind (=)) Eq }
          { Symbol = "!="; Prec = 7; Assoc = Left; Map = relOpCheck (ind (<>)) (ind (<>)) Neq }

          { Symbol = "<"; Prec = 8; Assoc = Left; Map = relOpCheck (ind (<)) (ind (<)) Les }
          { Symbol = ">"; Prec = 8; Assoc = Left; Map = relOpCheck (ind (>)) (ind (>)) Grt }
          { Symbol = "<="; Prec = 8; Assoc = Left; Map = relOpCheck (ind (<=)) (ind (<=)) Leq }
          { Symbol = ">="; Prec = 8; Assoc = Left; Map = relOpCheck (ind (>=)) (ind (>=)) Geq }

          { Symbol = "<<"; Prec = 9; Assoc = Left; Map = intOpCheck (<<<) ShL }
          { Symbol = ">>"; Prec = 9; Assoc = Left; Map = intOpCheck (>>>) SaR }

          { Symbol = "+"; Prec = 10; Assoc = Left; Map = arithOpCheck (+) (+) Add }
          { Symbol = "-"; Prec = 10; Assoc = Left; Map = arithOpCheck (-) (-) Sub }

          { Symbol = "*"; Prec = 11; Assoc = Left; Map = arithOpCheck (lei (*)) (lei (*)) Mul }
          { Symbol = "/"; Prec = 12; Assoc = Right; Map = arithOpCheck (lei (/)) (lei (/)) Div }
          { Symbol = "%"; Prec = 11; Assoc = Left; Map = intOpCheck (%) Mod } ]

    type UnaryOperatorDetails = { Symbol: string; Prec: int; Map: Expr -> Expr }

    let private checkLogicNot (expr: Expr) =
        if not (expr.Type.IsInt || expr.Type.IsFloat) then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int(ind (=) i 0)
            | Float f -> Int(ind (=) f 0.0f)
            | _ -> LogicNot expr

        { Inner = inner; Type = Type.Int; Category = RValue; IsConst = expr.IsConst }

    let private checkNeg (expr: Expr) =
        if not (expr.Type.IsInt || expr.Type.IsFloat) then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int -i
            | Float f -> Float -f
            | _ -> Neg expr

        { Inner = inner; Type = expr.Type; Category = RValue; IsConst = expr.IsConst }

    let private checkNot (expr: Expr) =
        if not expr.Type.IsInt then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | Int i -> Int ~~~i
            | _ -> Not expr

        { Inner = inner; Type = Type.Int; Category = RValue; IsConst = expr.IsConst }

    let prefixOperators =
        [ { Symbol = "!"; Prec = 12; Map = checkLogicNot }
          { Symbol = "+"; Prec = 12; Map = id }
          { Symbol = "-"; Prec = 12; Map = checkNeg }
          { Symbol = "~"; Prec = 12; Map = checkNot }
          { Symbol = "++"; Prec = 12; Map = id }
          { Symbol = "--"; Prec = 12; Map = id } ]

    let postfixOperators =
        [ { Symbol = "++"; Prec = 13; Map = id }
          { Symbol = "--"; Prec = 13; Map = id } ]

let private operatorParser = OperatorPrecedenceParser()

for detail in Operators.infixOperators do
    let operator =
        InfixOperator(detail.Symbol, ws, detail.Prec, detail.Assoc, detail.Map)

    operatorParser.AddOperator operator

for detail in Operators.prefixOperators do
    let operator = PrefixOperator(detail.Symbol, ws, detail.Prec, true, detail.Map)
    operatorParser.AddOperator operator

for detail in Operators.postfixOperators do
    let operator = PostfixOperator(detail.Symbol, ws, detail.Prec, true, detail.Map)
    operatorParser.AddOperator operator

let private keyword str =
    attempt (pstring str .>> notFollowedBy (regex @"[a-zA-Z0-9_]")) .>> ws

let private expr = operatorParser.ExpressionParser .>> ws <?> "an expression"
let private parenExpr = between (ch '(') (ch ')') expr
operatorParser.TermParser <- choice [ literal; parenExpr ]
let private parenExpr = between (ch '(') (ch ')') expr
let private identifierStr = regex @"[a-zA-Z_][a-zA-Z0-9_]*" .>> ws
let private followedByCh c = followedBy (ch c)

let private block, blockRef = createParserForwardedToRef ()
let private statement, stmtRef = createParserForwardedToRef ()

let private breakContinueBase keyword_ ret =
    keyword keyword_ .>> ch ';' >>. getUserState
    >>= fun state ->
        match isInLoop state with
        | true -> preturn ret
        | false -> fail $"`{keyword_}` statement must be used in loop."

let private break_ = breakContinueBase "break" Break
let private continue_ = breakContinueBase "continue" Continue

let private return_ =
    let checkExpr state (expr: Expr) =
        match typeCastable expr.Type state.RetType with
        | true -> preturn (Some expr)
        | false -> fail "Return expression type mismatch."

    keyword "return" >>. getUserState
    >>= function
        | { RetType = Void } -> ch ';' >>% Return None
        | state -> expr .>> ch ';' >>= checkExpr state |>> Return

let private blockItem, blockItemRef = createParserForwardedToRef ()
let private blockWithoutScope = between (ch '{') (ch '}') (many blockItem)

let private ifWhileHelper =
    choice [ blockWithoutScope; statement |>> (Statement >> List.singleton) ]

let private ifHelper =
    between (updateUserState (enterBlock false)) (updateUserState exitBlock) ifWhileHelper

let private whileHelper =
    between (updateUserState (enterBlock true)) (updateUserState exitBlock) ifWhileHelper

let private arithExpr =
    expr
    >>= function
        | { Type = Type.Int | Type.Float } as expr -> preturn expr
        | _ -> fail "Expecting an expression of type `int` or `float`."

let private condExpr = between (ch '(') (ch ')') arithExpr
