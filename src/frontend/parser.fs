// Copyright (C) 2025 Elkeid Me
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

let unreachable () = failwith "Unreachable code."
let todo () = failwith "Not implemented yet."

let createCounter () =
    let count = 0 |> uint |> ref

    fun () ->
        count.Value <- count.Value + uint 1
        count.Value

type HashMap<'K, 'V> = System.Collections.Generic.Dictionary<'K, 'V>
type BlockInfo = { SymbolTable: HashMap<string, Handler>; InLoop: bool }

/// - `Counter`: 生成唯一标识符的计数器。
/// - `SymbolTable`: 全局的符号表，存储 `Handler` 到 `Definition` 的映射。
/// - `RetType`: 当前函数的返回类型。
/// - `Blocks`: 当前作用域栈，每个作用域包含一个符号表和是否在循环内的信息。
/// - `ParsingType`: 当前正在解析的基础类型（用于处理类型声明）。
///
///   注意，解析数组声明时，仍然使用数组元素类型作为 `ParsingType`。
type Context =
    { Counter: unit -> uint
      SymbolTable: HashMap<Handler, Definition>
      RetType: Type
      Blocks: BlockInfo list
      ParsingType: Type }

let isInLoop state = (List.head state.Blocks).InLoop

let isGlobal state =
    match state.Blocks with
    | [ _ ] -> true
    | _ -> false

let enterBlock startLoopNow state =
    let inLoop = if startLoopNow then true else isInLoop state
    { state with Blocks = { SymbolTable = HashMap(); InLoop = inLoop } :: state.Blocks }

let enterFuncBody retType state =
    { state with
        RetType = retType
        Blocks = { SymbolTable = HashMap(); InLoop = false } :: state.Blocks }

let exitBlock state =
    { state with Blocks = List.tail state.Blocks }

let insertDef handler def state =
    state.SymbolTable.Add(handler, def)
    state.Blocks.Head.SymbolTable.Add(def.ID, handler)
    state

let insertDefs handlers defs state =
    for handler, def in List.zip handlers defs do
        state.SymbolTable.Add(handler, def)
        state.Blocks.Head.SymbolTable.Add(def.ID, handler)

    state

let searchDef context identifier =
    context.Blocks
    |> List.tryFind _.SymbolTable.ContainsKey(identifier)
    |> Option.map _.SymbolTable.[identifier]
    |> Option.map (fun h -> context.SymbolTable.[h], h)

let currentExist context identifier =
    context.Blocks.Head.SymbolTable.ContainsKey identifier

let boolIntFun f a b = if f a b then 1 else 0

let arithOpCheck fnInt fnFloat constructor (l: Expr) (r: Expr) =
    let ty =
        match l.Type, r.Type with
        | Type.Int, Type.Int -> Type.Int
        | Type.Int, Type.Float
        | Type.Float, Type.Int
        | Type.Float, Type.Float -> Type.Float
        | _ -> failwith "Invalid type of operands."

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnInt l r)
        | ExprInner.Float l, ExprInner.Int r -> ExprInner.Float(fnFloat l (single r))
        | ExprInner.Int l, ExprInner.Float r -> ExprInner.Float(fnFloat (single l) r)
        | ExprInner.Float l, ExprInner.Float r -> ExprInner.Float(fnFloat l r)
        | _ -> constructor (l, r)

    { Inner = inner; Type = ty; Category = RValue; IsConst = l.IsConst && r.IsConst }

let intOpCheck fnInt constructor (l: Expr) (r: Expr) =
    if not (l.Type.IsInt && r.Type.IsInt) then failwith "Invalid type of operands."

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnInt l r)
        | _ -> constructor (l, r)

    { Inner = inner; Type = Type.Int; Category = RValue; IsConst = l.IsConst && r.IsConst }

let logicOpCheck fnLogic constructor (l: Expr) (r: Expr) =
    if not ((l.Type.IsInt || l.Type.IsFloat) && (r.Type.IsInt || r.Type.IsFloat)) then
        failwith "Invalid type of operands."

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnLogic (l <> 0) (r <> 0))
        | ExprInner.Float l, ExprInner.Int r -> ExprInner.Int(fnLogic (l <> 0.0f) (r <> 0))
        | ExprInner.Int l, ExprInner.Float r -> ExprInner.Int(fnLogic (l <> 0) (r <> 0.0f))
        | ExprInner.Float l, ExprInner.Float r -> ExprInner.Int(fnLogic (l <> 0.0f) (r <> 0.0f))
        | _ -> constructor (l, r)

    { Inner = inner; Type = Type.Int; Category = RValue; IsConst = l.IsConst && r.IsConst }

let relOpCheck fnIntComp fnFloatComp constructor (l: Expr) (r: Expr) =
    if not ((l.Type.IsInt || l.Type.IsFloat) && (r.Type.IsInt || r.Type.IsFloat)) then
        failwith "Invalid type of operands."

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnIntComp l r)
        | ExprInner.Float l, ExprInner.Int r -> ExprInner.Int(fnFloatComp l (single r))
        | ExprInner.Int l, ExprInner.Float r -> ExprInner.Int(fnFloatComp (single l) r)
        | ExprInner.Float l, ExprInner.Float r -> ExprInner.Int(fnFloatComp l r)
        | _ -> constructor (l, r)

    { Inner = inner; Type = Type.Int; Category = RValue; IsConst = l.IsConst && r.IsConst }

let assignOpCheck constructor (l: Expr) (r: Expr) =
    if l.Category <> LValue then failwith "R-value on the left hand side of assign operator."

    if not ((l.Type.IsInt || l.Type.IsFloat) && (r.Type.IsInt || r.Type.IsFloat)) then
        failwith "Invalid type of operands."

    { Inner = constructor (l, r); Type = l.Type; Category = LValue; IsConst = false }

let intAssignOpCheck constructor (l: Expr) (r: Expr) =
    if l.Category <> LValue then failwith "R-value on the left hand side of assign operator."

    if not (l.Type.IsInt && r.Type.IsInt) then failwith "Invalid type of operands."
    { Inner = constructor (l, r); Type = Type.Int; Category = LValue; IsConst = false }

let cxxComment = skipString "//" .>> manyCharsTill anyChar (skipNewline <|> eof)
let blockComment = skipString "/*" .>> manyCharsTill anyChar (skipString "*/")
let singleSpace = choiceL [ cxxComment; blockComment; skipAnyOf " \t\n" ] ""
let ws = skipMany singleSpace

let str s = pstring s .>> ws
let ch c = pchar c .>> ws

let inline makeConstInt (x: 'T) =
    { Inner = x |> int |> ExprInner.Int; Type = Type.Int; Category = RValue; IsConst = true }

let inline makeConstFloat (x: 'T) =
    { Inner = x |> single |> ExprInner.Float; Type = Type.Float; Category = RValue; IsConst = true }

let literal =
    let cvtInt (base_: int) int_ = System.Convert.ToInt32(int_, base_)
    let hexInt = regex @"0[xX][0-9a-fA-F]+" |>> (cvtInt 16 >> makeConstInt)
    let binInt = regex @"0[bB][01]+" |>> (cvtInt 2 >> makeConstInt)
    let octInt = regex @"0[0-7]*" |>> (cvtInt 8 >> makeConstInt)
    let decInt = regex @"[1-9]\d*" |>> (cvtInt 10 >> makeConstInt)

    let decFloat =
        regex @"(((\d*\.\d+)|(\d+\.))([eE][-+]?\d+)?)|((\d+)([eE][-+]?\d+))"
        |>> (single >> makeConstFloat)

    let hexFloat =
        regex @"0[xX](([0-9a-fA-F]*\.[0-9a-fA-F]+)|([0-9a-fA-F]+\.))|([0-9a-fA-F]+)[pP][+-]\d+"
        |>> (HexFloat.SingleFromHexString >> makeConstFloat)

    let pInt = choiceL [ hexInt; binInt; octInt; decInt ] "integer literal"
    let pFloat = choiceL [ hexFloat; decFloat ] "floating-point literal"

    pFloat <|> pInt .>> ws

module Operators =
    type InfixOperatorDetails = { Symbol: string; Precedence: int; Assoc: Associativity; Map: Expr -> Expr -> Expr }

    let private leiArithInt f a b =
        match a, b with
        | a, 0 -> a
        | a, b -> f a b

    let private leiArithFloat f a b =
        match a, b with
        | a, 0.0f -> a
        | a, b -> f a b

    let infixOperators =
        [ { Symbol = "="; Precedence = 1; Assoc = Associativity.Right; Map = assignOpCheck Assignment }
          { Symbol = "+="; Precedence = 1; Assoc = Associativity.Right; Map = assignOpCheck AddAssign }
          { Symbol = "-="; Precedence = 1; Assoc = Associativity.Right; Map = assignOpCheck SubAssign }
          { Symbol = "*="; Precedence = 1; Assoc = Associativity.Right; Map = assignOpCheck MulAssign }
          { Symbol = "/="; Precedence = 1; Assoc = Associativity.Right; Map = assignOpCheck DivAssign }
          { Symbol = "%="; Precedence = 1; Assoc = Associativity.Right; Map = intAssignOpCheck ModAssign }
          { Symbol = "&="; Precedence = 1; Assoc = Associativity.Right; Map = intAssignOpCheck AndAssign }
          { Symbol = "|="; Precedence = 1; Assoc = Associativity.Right; Map = intAssignOpCheck OrAssign }
          { Symbol = "^="; Precedence = 1; Assoc = Associativity.Right; Map = intAssignOpCheck XorAssign }
          { Symbol = "<<="; Precedence = 1; Assoc = Associativity.Right; Map = intAssignOpCheck ShLAssign }
          { Symbol = ">>="; Precedence = 1; Assoc = Associativity.Right; Map = intAssignOpCheck SaRAssign }

          { Symbol = "||"
            Precedence = 2
            Assoc = Associativity.Left
            Map = logicOpCheck (boolIntFun (||)) LogicOr }

          { Symbol = "&&"
            Precedence = 3
            Assoc = Associativity.Left
            Map = logicOpCheck (boolIntFun (&&)) LogicAnd }

          { Symbol = "^"; Precedence = 4; Assoc = Associativity.Left; Map = intOpCheck (^^^) Xor }

          { Symbol = "|"; Precedence = 5; Assoc = Associativity.Left; Map = intOpCheck (|||) Or }

          { Symbol = "&"; Precedence = 6; Assoc = Associativity.Left; Map = intOpCheck (&&&) And }

          { Symbol = "=="
            Precedence = 7
            Assoc = Associativity.Left
            Map = relOpCheck (boolIntFun (=)) (boolIntFun (=)) Eq }
          { Symbol = "!="
            Precedence = 7
            Assoc = Associativity.Left
            Map = relOpCheck (boolIntFun (<>)) (boolIntFun (<>)) Neq }

          { Symbol = "<"
            Precedence = 8
            Assoc = Associativity.Left
            Map = relOpCheck (boolIntFun (<)) (boolIntFun (<)) Les }
          { Symbol = ">"
            Precedence = 8
            Assoc = Associativity.Left
            Map = relOpCheck (boolIntFun (>)) (boolIntFun (>)) Grt }
          { Symbol = "<="
            Precedence = 8
            Assoc = Associativity.Left
            Map = relOpCheck (boolIntFun (<=)) (boolIntFun (<=)) Leq }
          { Symbol = ">="
            Precedence = 8
            Assoc = Associativity.Left
            Map = relOpCheck (boolIntFun (>=)) (boolIntFun (>=)) Geq }

          { Symbol = "<<"; Precedence = 9; Assoc = Associativity.Left; Map = intOpCheck (<<<) ShL }
          { Symbol = ">>"; Precedence = 9; Assoc = Associativity.Left; Map = intOpCheck (>>>) SaR }

          { Symbol = "+"; Precedence = 10; Assoc = Associativity.Left; Map = arithOpCheck (+) (+) Add }
          { Symbol = "-"; Precedence = 10; Assoc = Associativity.Left; Map = arithOpCheck (-) (-) Sub }

          { Symbol = "*"
            Precedence = 11
            Assoc = Associativity.Left
            Map = arithOpCheck (leiArithInt (*)) (leiArithFloat (*)) Mul }
          { Symbol = "/"
            Precedence = 12
            Assoc = Associativity.Right
            Map = arithOpCheck (leiArithInt (/)) (leiArithFloat (/)) Div }
          { Symbol = "%"; Precedence = 11; Assoc = Associativity.Left; Map = intOpCheck (%) Mod } ]

    type UnaryOperatorDetails = { Symbol: string; Precedence: int; Map: Expr -> Expr }

    let checkArithUnary fnInt fnFloat constructor (expr: Expr) =
        let ty =
            match expr.Type with
            | Type.Int -> Type.Int
            | Type.Float -> Type.Float
            | _ -> failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | ExprInner.Int i -> ExprInner.Int(fnInt i)
            | ExprInner.Float f -> ExprInner.Float(fnFloat f)
            | _ -> constructor expr

        { Inner = inner; Type = ty; Category = RValue; IsConst = expr.IsConst }

    let private checkNot (expr: Expr) =
        if not (expr.Type.IsInt || expr.Type.IsFloat) then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | ExprInner.Int i -> ExprInner.Int(boolIntFun (=) i 0)
            | ExprInner.Float f -> ExprInner.Int(boolIntFun (=) f 0.0f)
            | _ -> LogicNot expr

        { Inner = inner; Type = Type.Int; Category = RValue; IsConst = expr.IsConst }

    let private checkNega (expr: Expr) =
        let ty =
            match expr.Type with
            | Type.Int -> Type.Int
            | Type.Float -> Type.Float
            | _ -> failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | ExprInner.Int i -> ExprInner.Int -i
            | ExprInner.Float f -> ExprInner.Float -f
            | _ -> Nega expr

        { Inner = inner; Type = ty; Category = RValue; IsConst = expr.IsConst }

    let private checkBitnot (expr: Expr) =
        if not expr.Type.IsInt then failwith "Invalid type of operand."

        let inner =
            match expr.Inner with
            | ExprInner.Int i -> ExprInner.Int ~~~i
            | _ -> Nega expr

        { Inner = inner; Type = Type.Int; Category = RValue; IsConst = expr.IsConst }

    let prefixOperators =
        [ { Symbol = "!"; Precedence = 12; Map = checkNot }
          { Symbol = "+"; Precedence = 12; Map = id }
          { Symbol = "-"; Precedence = 12; Map = checkNega }
          { Symbol = "~"; Precedence = 12; Map = checkBitnot }
          { Symbol = "++"; Precedence = 12; Map = id }
          { Symbol = "--"; Precedence = 12; Map = id } ]

    let postfixOperators =
        [ { Symbol = "++"; Precedence = 13; Map = id }
          { Symbol = "--"; Precedence = 13; Map = id } ]

let operatorParser = OperatorPrecedenceParser<Expr, unit, Context>()

Operators.infixOperators
|> List.iter (fun details ->
    let operator =
        InfixOperator(details.Symbol, ws, details.Precedence, details.Assoc, details.Map)

    operatorParser.AddOperator operator)

Operators.prefixOperators
|> List.iter (fun details ->
    let operator =
        PrefixOperator(details.Symbol, ws, details.Precedence, true, details.Map)

    operatorParser.AddOperator operator)

Operators.postfixOperators
|> List.iter (fun details ->
    let operator =
        PostfixOperator(details.Symbol, ws, details.Precedence, true, details.Map)

    operatorParser.AddOperator operator)

let keyword str =
    attempt (pstring str .>> notFollowedBy (regex @"[a-zA-Z0-9_]")) .>> ws

let expr = operatorParser.ExpressionParser .>> ws <?> "an expression"
let parenExpr = between (ch '(') (ch ')') expr
let identifierStr = regex @"[a-zA-Z_][a-zA-Z0-9_]*" .>> ws
let private followedByCh c = followedBy (ch c)

let identifier =
    tuple3 identifierStr getUserState (opt (choice [ followedByCh '(' >>% true; followedByCh '[' >>% false ]))
    >>= fun (name, state, isCallOrArray) ->
        match isCallOrArray with
        | None ->
            match searchDef state name with
            | Some(def, handler) ->
                preturn (
                    match def.Init, def.Type with
                    | Some(ConstInt x), Type.Int -> makeConstInt x
                    | Some(ConstInt x), Type.Float -> makeConstFloat x
                    | Some(ConstFloat x), Type.Int -> makeConstInt x
                    | Some(ConstFloat x), Type.Float -> makeConstFloat x
                    | _, ty when ty.IsInt || ty.IsFloat ->
                        { Inner = Var handler; Type = ty; Category = LValue; IsConst = false }
                    | _, ty -> { Inner = Var handler; Type = ty; Category = RValue; IsConst = false }
                )
            | None -> fail $"Undefined identifier: `{name}`."
        | Some true ->
            between (ch '(') (ch ')') (sepBy expr (ch ','))
            >>= fun args ->
                match searchDef state name with
                | Some(def, handler) ->
                    match def.Type with
                    | Type.Function(retType, paramTypes) ->
                        if paramTypes.Length <> args.Length then
                            fail $"Function `{name}` argument count mismatch."
                        else if not (List.forall2 typeConvertible (args |> List.map _.Type) paramTypes) then
                            fail $"Function `{name}` argument type mismatch."
                        else
                            preturn { Inner = Func(handler, args); Type = retType; Category = RValue; IsConst = false }
                    | _ -> fail $"`{name}` is not a function."
                | None -> fail $"Undefined function: `{name}`."
        | Some false ->
            let intExpr =
                expr
                >>= fun expr ->
                    match expr.Type with
                    | Type.Int -> preturn expr
                    | _ -> fail "Expecting an expression of type `int`."

            many1 (between (ch '[') (ch ']') intExpr)
            >>= fun indices ->
                let checkPointer indices handler baseType dims init =
                    let indicesLen = List.length indices
                    let dimsLen = List.length dims

                    if indicesLen - 1 < dimsLen then
                        preturn
                            { Inner = ArrayElem(handler, indices)
                              Type = Pointer(baseType, List.skip indicesLen dims)
                              Category = RValue
                              IsConst = false }
                    else if indicesLen - 1 = dimsLen then
                        if Option.isSome init && List.forall _.Inner.IsInt indices then
                            let rec getElem list_ indices =
                                match indices with
                                | [ i ] ->
                                    match List.tryItem i list_ with
                                    | Some(Int x) -> makeConstInt x
                                    | Some(Float x) -> makeConstFloat x
                                    | _ ->
                                        match baseType with
                                        | Type.Int -> makeConstInt 0
                                        | Type.Float -> makeConstFloat 0.0f
                                        | _ -> unreachable ()

                                | i :: rest ->
                                    match List.tryItem i list_ with
                                    | Some(ConstInitList subList) -> getElem subList rest
                                    | _ ->
                                        match baseType with
                                        | Type.Int -> makeConstInt 0
                                        | Type.Float -> makeConstFloat 0.0f
                                        | _ -> unreachable ()
                                | _ -> unreachable ()

                            match init with
                            | Some list_ ->
                                preturn (
                                    getElem
                                        list_
                                        (List.map
                                            (fun e ->
                                                match e.Inner with
                                                | ExprInner.Int i -> i
                                                | _ -> unreachable ())
                                            indices)
                                )
                            | None -> unreachable ()
                        else
                            preturn
                                { Inner = ArrayElem(handler, indices)
                                  Type = baseType
                                  Category = LValue
                                  IsConst = false }
                    else
                        fail $"Too many indices for array or pointer `{name}`."

                match searchDef state name with
                | Some({ Init = Some(ConstList list); Type = Array(baseType, dims) }, handler) ->
                    checkPointer indices handler baseType (List.tail dims) (Some list)
                | Some({ Type = Array(baseType, dims) }, handler) ->
                    checkPointer indices handler baseType (List.tail dims) None
                | Some({ Type = Pointer(baseType, dims) }, handler) -> checkPointer indices handler baseType dims None
                | Some _ -> fail $"`{name}` is not an array or pointer."
                | None -> fail $"Undefined function: `{name}`."

let block, blockRef = createParserForwardedToRef ()
let statement, stmtRef = createParserForwardedToRef ()

operatorParser.TermParser <- choice [ literal; identifier; parenExpr ]

let break_ =
    keyword "break" .>> ch ';' >>. getUserState
    >>= fun state ->
        match isInLoop state with
        | true -> preturn Break
        | false -> fail "`break` statement must be used in loop."

let continue_ =
    keyword "continue" .>> ch ';' >>. getUserState
    >>= fun state ->
        match isInLoop state with
        | true -> preturn Continue
        | false -> fail "`continue` statement must be used in loop."

let return_ =
    let checkExpr state (expr: Expr) =
        if typeConvertible expr.Type state.RetType then
            preturn (Some expr)
        else
            fail "Return expression type mismatch."

    keyword "return" >>. getUserState
    >>= fun state ->
        match state.RetType with
        | Void -> ch ';' >>% Return None
        | _ -> expr .>> ch ';' >>= checkExpr state |>> Return

let blockItem, blockItemRef = createParserForwardedToRef ()
let blockNoRegion = between (ch '{') (ch '}') (many blockItem)

let ifWhileHelper =
    choice [ blockNoRegion; statement |>> (Statement >> List.singleton) ]

let ifHelper =
    between (updateUserState (enterBlock false)) (updateUserState exitBlock) ifWhileHelper

let whileHelper =
    between (updateUserState (enterBlock true)) (updateUserState exitBlock) ifWhileHelper

let arithExpr =
    expr
    >>= fun expr ->
        match expr.Type with
        | Type.Int
        | Type.Float -> preturn expr
        | _ -> fail "Expecting an expression of type `int` or `float`."

let condExpr = between (ch '(') (ch ')') arithExpr

let ifElse =
    tuple3 (keyword "if" >>. condExpr) ifHelper (opt (keyword "else" >>. ifHelper) |>> Option.defaultValue [])
    |>> If

let whileLoop = keyword "while" >>. condExpr .>>. whileHelper |>> While

module Definitions =
    let private int_ = keyword "int" >>% Type.Int
    let private float_ = keyword "float" >>% Type.Float
    let private void_ = keyword "void" >>% Void
    let private types = choiceL [ int_; float_; void_ ] "a type"
    let private nonVoidTypes = choiceL [ int_; float_ ] "a non-void type"

    let private posiConstInt =
        expr
        >>= function
            | { Inner = ExprInner.Int i } when i > 0 -> preturn i
            | _ -> fail "Expecting a positive integer constant."

    let private constExpr =
        expr
        >>= fun e ->
            match e.IsConst with
            | true -> preturn e
            | false -> fail "Expecting a constant expression."

    let private param =
        tuple3
            nonVoidTypes
            (opt identifierStr)
            (opt (ch '[' >>. ch ']' >>. many (between (ch '[') (ch ']') posiConstInt)))
        |>> fun (ty, idOpt, arrDims) ->
            match arrDims with
            | Some dims -> Pointer(ty, dims |> List.map uint64), idOpt
            | None -> ty, idOpt

    let private makeFuncDecl newRetType name (newParams: (Type * string option) list) state =
        let parseInitial =
            match searchDef state name with
            | Some(def, _) ->
                match def.Type with
                | Type.Function(retType, paramTypes) when newRetType = retType && newParams |> List.map fst = paramTypes ->
                    preturn []
                | _ -> fail $"Conflicting types for `{name}`."
            | None ->
                let handler = state.Counter()

                let def =
                    { Init = None
                      Type = Type.Function(newRetType, newParams |> List.map fst)
                      ID = name
                      IsGlobal = true
                      IsArg = false }

                updateUserState (insertDef handler def) >>. preturn []

        parseInitial .>> ch ';'

    let private makeFuncDef newRetType name (newParams: (Type * string option) list) state =
        let argHandlers = List.init newParams.Length (fun _ -> state.Counter())

        let argDefs =
            newParams
            |> List.map (fun (ty, idOpt) ->
                let id = Option.defaultValue "" idOpt
                { Init = None; Type = ty; ID = id; IsGlobal = false; IsArg = true })

        let type_ = Type.Function(newRetType, newParams |> List.map fst)

        let makeDef body =
            { Init = Some(Function { Block = body; ArgHandlers = argHandlers })
              Type = type_
              ID = name
              IsGlobal = true
              IsArg = false }

        match searchDef state name with
        | None ->
            let handler = state.Counter()

            updateUserState (
                insertDef handler (makeDef [])
                >> enterFuncBody newRetType
                >> insertDefs argHandlers argDefs
            )
            >>. blockNoRegion
            .>> updateUserState exitBlock
            >>= (fun body ->
                updateUserState (fun state ->
                    state.SymbolTable.[handler] <- makeDef body
                    state))
            >>. preturn [ handler ]
        | Some(def, handler) ->
            match def.Type with
            | Type.Function(retType, paramTypes) when
                newRetType = retType
                && newParams |> List.map fst = paramTypes
                && def.Init.IsNone
                ->
                updateUserState (enterFuncBody newRetType >> insertDefs argHandlers argDefs)
                >>. blockNoRegion
                .>> updateUserState exitBlock
                >>= (fun body ->
                    updateUserState (fun state ->
                        state.SymbolTable.[handler] <- makeDef body
                        state))
                >>. preturn [ handler ]
            | _ -> fail $"Conflicting types for `{name}`."

    let private constArithExpr =
        constExpr
        >>= function
            | { Inner = ExprInner.Int i } -> preturn (Int i)
            | { Inner = ExprInner.Float f } -> preturn (Float f)
            | _ -> fail "Expecting a constant integer or floating-point expression."

    let private initListItem, initListItemRef = createParserForwardedToRef ()
    let private initList = between (ch '{') (ch '}') (sepBy initListItem (ch ','))
    let private constInitListItem, constInitListItemRef = createParserForwardedToRef ()

    let private constInitList =
        between (ch '{') (ch '}') (sepBy constInitListItem (ch ','))

    let processGenericInitList
        (isLeaf: 'T -> bool)
        (isNode: 'T -> 'T list option)
        (wrap: 'T list -> 'T)
        (dims: int list)
        (initList: 'T list)
        =

        let totalDepth = List.length dims
        let dimsProd = (dims, 1) ||> List.scanBack (*) |> List.take totalDepth

        let rec impl dimsProd currentInitList =
            let insert (sum, list_) initElem =
                match isNode initElem with
                | None when isLeaf initElem -> // 处理叶子节点 (Expr/Int/Float)
                    let rec insertLeaf list_ dimsProd leaf =
                        match dimsProd with
                        | [] -> leaf :: list_
                        | i :: rest ->
                            let paddedList =
                                if List.isEmpty list_ || sum % i = 0 then
                                    wrap [] :: list_
                                else
                                    list_

                            match paddedList with
                            | head :: restList -> wrap (insertLeaf (isNode head |> Option.get) rest leaf) :: restList
                            | _ -> failwith "unreachable"

                    let newList = insertLeaf list_ (List.tail dimsProd) initElem
                    sum + 1, newList

                | Some subInitList -> // 处理嵌套列表 (InitList/ConstInitList)
                    let rec insertSubList list_ dimsProd subItems =
                        match dimsProd with
                        | [] -> failwith "Too many initializer lists."
                        | _ :: i :: _ when sum % i = 0 ->
                            let processedSub = impl (List.tail dimsProd) subItems
                            i, wrap processedSub :: list_
                        | _ :: rest ->
                            let newList = if List.isEmpty list_ then wrap [] :: list_ else list_

                            match newList with
                            | head :: restList ->
                                let subSum, newHead = insertSubList (isNode head |> Option.get) rest subItems
                                subSum, wrap newHead :: restList
                            | _ -> failwith "Initializer list does not match array dimensions."

                    let subSum, newList = insertSubList list_ dimsProd subInitList
                    let newSum = sum + subSum

                    if newSum <= List.head dimsProd then
                        newSum, newList
                    else
                        failwith "Too many initializers."
                | _ -> failwith "Unknown item type."

            currentInitList |> List.fold insert (0, []) |> snd

        let rec reverseRecursive l =
            l
            |> List.map (fun x ->
                match isNode x with
                | Some sub -> wrap (reverseRecursive sub)
                | None -> x)
            |> List.rev

        impl dimsProd initList |> reverseRecursive

    let processInitList dims initList =
        processGenericInitList
            (function
            | InitListItem.Expr _ -> true
            | _ -> false)
            (function
            | InitList l -> Some l
            | _ -> None)
            InitList
            dims
            initList

    let processConstInitList dims initList =
        processGenericInitList
            (function
            | Int _
            | Float _ -> true
            | _ -> false)
            (function
            | ConstInitList l -> Some l
            | _ -> None)
            ConstInitList
            dims
            initList

    let private constDefAfter =
        opt (many1 (ch '[' >>. posiConstInt .>> ch ']')) .>> ch '='
        >>= fun arrDims ->
            match arrDims with
            | Some dims ->
                constInitList
                |>> fun init -> Some(dims |> List.map uint64), init |> processConstInitList dims |> ConstList
            | None ->
                constArithExpr
                |>> function
                    | Int i -> None, ConstInt i
                    | Float f -> None, ConstFloat f
                    | _ -> unreachable ()

    let private varDefAfter =
        opt (many1 (ch '[' >>. posiConstInt .>> ch ']'))
        >>= fun arrDims ->
            match arrDims with
            | Some dims ->
                opt (ch '=' >>. initList)
                |>> fun init -> Some(dims |> List.map uint64), init |> Option.map (processInitList dims >> List)
            | None -> opt (ch '=' >>. arithExpr) |>> fun exprOpt -> None, Option.map Expr exprOpt

    let private makeVarDef name arrDimOpt initOpt =
        getUserState
        >>= fun state ->
            if currentExist state name then
                fail $"Redefinition of identifier: `{name}`."
            else
                let ty = state.ParsingType

                let fullType =
                    match arrDimOpt with
                    | Some dims -> Array(ty, dims |> List.map uint64)
                    | None -> ty

                let handler = state.Counter()

                let def =
                    { Init = initOpt; Type = fullType; ID = name; IsGlobal = isGlobal state; IsArg = false }

                updateUserState (insertDef handler def) >>. preturn handler

    let defs =
        tuple5
            (opt (keyword "const" >>% ()))
            types
            (opt (keyword "const" >>% ()))
            identifierStr
            (choice
                [ followedByCh '(' >>% true
                  choice [ followedByCh '['; followedByCh ','; followedByCh '='; followedByCh ';' ]
                  >>% false ])
        >>= fun (const1, type_, const2, name, isFunc) ->
            let const_ = const1.IsSome || const2.IsSome

            if isFunc && not const_ then
                tuple3
                    (between (ch '(') (ch ')') (sepBy param (ch ',')))
                    (choice [ followedByCh ';' >>% true; followedByCh '{' >>% false ])
                    getUserState
                >>= fun (params_, isDecl, state) ->
                    if isDecl then
                        makeFuncDecl type_ name params_ state
                    else if isGlobal state then
                        makeFuncDef type_ name params_ state
                    else
                        fail "Function definitions are only allowed in global scope."
            else if type_.IsVoid then
                fail "Variables cannot be of type void."
            else
                let parse =
                    let tmp =
                        if const_ then
                            let wrap1 name (arrDimOpt, init) = makeVarDef name arrDimOpt (Some init)
                            let wrap2 (name, (arrDimOpt, init)) = makeVarDef name arrDimOpt (Some init)

                            constDefAfter >>= wrap1 name
                            .>>. opt (many (ch ',' >>. identifierStr .>>. constDefAfter >>= wrap2))
                        else
                            let wrap1 name (arrDimOpt, init) = makeVarDef name arrDimOpt init
                            let wrap2 (name, (arrDimOpt, init)) = makeVarDef name arrDimOpt init

                            varDefAfter >>= wrap1 name
                            .>>. opt (many (ch ',' >>. identifierStr .>>. varDefAfter >>= wrap2))

                    tmp .>> ch ';' |>> fun (x, l) -> x :: Option.defaultValue [] l

                updateUserState (fun state -> { state with ParsingType = type_ }) >>. parse

    initListItemRef.Value <- choice [ initList |>> InitList; arithExpr |>> InitListItem.Expr ]
    constInitListItemRef.Value <- choice [ constInitList |>> ConstInitList; constArithExpr ]


blockItemRef.Value <- choice [ block |>> Block; Definitions.defs |>> Def; statement |>> Statement ]

blockRef.Value <-
    between (ch '{' >>. updateUserState (enterBlock false)) (ch '}' >>. updateUserState exitBlock) (many blockItem)

stmtRef.Value <-
    let exprStmt = expr .>> ch ';' |>> Statement.Expr
    let emptyStmt = ch ';' >>% Empty
    choice [ whileLoop; ifElse; continue_; break_; return_; exprStmt; emptyStmt ]

let translationUnit = many Definitions.defs |>> List.concat
