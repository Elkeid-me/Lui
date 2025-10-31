module Parser

open AST
open FParsec

exception CompilerException of string

let createCounter () =
    let count = 0 |> uint |> ref

    fun () ->
        count.Value <- count.Value + uint 1
        count.Value

type HashMap<'K, 'V> = System.Collections.Generic.Dictionary<'K, 'V>
type BlockInfo = { SymbolTable: HashMap<string, Handler>; InLoop: bool }

type Context =
    { Counter: unit -> uint
      SymbolTable: HashMap<Handler, Definition>
      RetType: Type
      Blocks: BlockInfo list }

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

let boolIntFun f a b = if f a b then 1 else 0

let arithOpCheck fnInt fnFloat constructor (l: Expr) (r: Expr) =
    let ty =
        match l.Type, r.Type with
        | Type.Int, Type.Int -> Type.Int
        | Type.Int, Type.Float
        | Type.Float, Type.Int
        | Type.Float, Type.Float -> Type.Float
        | _ -> raise (CompilerException "Invalid type of operands.")

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnInt l r)
        | ExprInner.Float l, ExprInner.Int r -> ExprInner.Float(fnFloat l (single r))
        | ExprInner.Int l, ExprInner.Float r -> ExprInner.Float(fnFloat (single l) r)
        | ExprInner.Float l, ExprInner.Float r -> ExprInner.Float(fnFloat l r)
        | _ -> constructor (l, r)

    { Inner = inner; Type = ty; Category = RValue; IsConst = l.IsConst && r.IsConst }

let intOpCheck fnInt constructor (l: Expr) (r: Expr) =
    match l.Type, r.Type with
    | Type.Int, Type.Int -> ()
    | _ -> raise (CompilerException "Invalid type of operands.")

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnInt l r)
        | _ -> constructor (l, r)

    { Inner = inner; Type = Type.Int; Category = RValue; IsConst = l.IsConst && r.IsConst }

let logicOpCheck fnLogic constructor (l: Expr) (r: Expr) =
    match l.Type, r.Type with
    | Type.Int, Type.Int
    | Type.Float, Type.Int
    | Type.Int, Type.Float
    | Type.Float, Type.Float -> ()
    | _ -> raise (CompilerException "Invalid type of operands.")

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnLogic (l <> 0) (r <> 0))
        | ExprInner.Float l, ExprInner.Int r -> ExprInner.Int(fnLogic (l <> 0.0f) (r <> 0))
        | ExprInner.Int l, ExprInner.Float r -> ExprInner.Int(fnLogic (l <> 0) (r <> 0.0f))
        | ExprInner.Float l, ExprInner.Float r -> ExprInner.Int(fnLogic (l <> 0.0f) (r <> 0.0f))
        | _ -> constructor (l, r)

    { Inner = inner; Type = Type.Int; Category = RValue; IsConst = l.IsConst && r.IsConst }

let relOpCheck fnIntComp fnFloatComp constructor (l: Expr) (r: Expr) =
    match l.Type, r.Type with
    | Type.Int, Type.Int
    | Type.Float, Type.Int
    | Type.Int, Type.Float
    | Type.Float, Type.Float -> ()
    | _ -> raise (CompilerException "Invalid type of operands.")

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnIntComp l r)
        | ExprInner.Float l, ExprInner.Int r -> ExprInner.Int(fnFloatComp l (single r))
        | ExprInner.Int l, ExprInner.Float r -> ExprInner.Int(fnFloatComp (single l) r)
        | ExprInner.Float l, ExprInner.Float r -> ExprInner.Int(fnFloatComp l r)
        | _ -> constructor (l, r)

    { Inner = inner; Type = Type.Int; Category = RValue; IsConst = l.IsConst && r.IsConst }

let assignOpCheck con (l: Expr) (r: Expr) =
    if l.Category <> LValue then
        raise (CompilerException "R-value on the left hand side if assign operator.")

    let ty =
        match l.Type, r.Type with
        | Type.Int, Type.Int
        | Type.Int, Type.Float -> Type.Int
        | Type.Float, Type.Int
        | Type.Float, Type.Float -> Type.Float
        | _ -> raise (CompilerException "Invalid type of operands.")

    let inner = con (l, r)

    { Inner = inner; Type = ty; Category = LValue; IsConst = false }

let intAssignOpCheck con (l: Expr) (r: Expr) =
    if l.Category <> LValue then
        raise (CompilerException "R-value on the left hand side if assign operator.")

    let ty =
        match l.Type, r.Type with
        | Type.Int, Type.Int -> Type.Int
        | _ -> raise (CompilerException "Invalid type of operands.")

    let inner = con (l, r)

    { Inner = inner; Type = ty; Category = LValue; IsConst = false }

let cxxComment = skipString "//" .>> manyCharsTill anyChar skipNewline
let blockComment = skipString "/*" .>> manyCharsTill anyChar (skipString "*/")
let singleSpace = choiceL [ cxxComment; blockComment; skipAnyOf " \t\n" ] ""
let ws = skipMany singleSpace

let str s = pstring s .>> ws
let ch c = pchar c .>> ws

let literal =
    let makeFloat x =
        { Inner = x |> single |> ExprInner.Float; Type = Type.Float; Category = RValue; IsConst = true }

    let makeInt x =
        { Inner = ExprInner.Int x; Type = Type.Int; Category = RValue; IsConst = true }

    let cvtInt (base_: int) int_ = System.Convert.ToInt32(int_, base_)
    let subStr idx (str: string) = str.Substring idx

    let pHexInt = regex @"0[xX][0-9a-fA-F]+" |>> (subStr 2 >> cvtInt 16 >> makeInt)
    let pBinInt = regex @"0[bB][01]+" |>> (subStr 2 >> cvtInt 2 >> makeInt)
    let pOctInt = regex @"0[0-7]*" |>> (cvtInt 8 >> makeInt)
    let pDecInt = regex @"[1-9]\d*" |>> (int >> makeInt)

    let pDecFloat =
        regex @"(((\d*\.\d+)|(\d+\.))([eE][-+]?\d+)?)|((\d+)([eE][-+]?\d+))"
        |>> (single >> makeFloat)

    let pHexFloat =
        regex @"0[xX](([0-9a-fA-F]*\.[0-9a-fA-F]+)|([0-9a-fA-F]+\.))|([0-9a-fA-F]+)[pP][+-]\d+"
        |>> (HexFloat.SingleFromHexString >> makeFloat)

    let pInt = choiceL [ pHexInt; pBinInt; pOctInt; pDecInt ] "integer literal"
    let pFloat = pHexFloat <|> pDecFloat <?> "floating-point literal"

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
            Precedence = 6
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
            | _ -> raise (CompilerException "Invalid type of operand.")

        let inner =
            match expr.Inner with
            | ExprInner.Int i -> ExprInner.Int(fnInt i)
            | ExprInner.Float f -> ExprInner.Float(fnFloat f)
            | _ -> constructor expr

        { Inner = inner; Type = ty; Category = RValue; IsConst = expr.IsConst }

    let private checkNot (expr: Expr) =
        match expr.Type with
        | Type.Int
        | Type.Float -> ()
        | _ -> raise (CompilerException "")

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
            | _ -> raise (CompilerException "")

        let inner =
            match expr.Inner with
            | ExprInner.Int i -> ExprInner.Int -i
            | ExprInner.Float f -> ExprInner.Float -f
            | _ -> Nega expr

        { Inner = inner; Type = ty; Category = RValue; IsConst = expr.IsConst }

    let private checkBitnot (expr: Expr) =
        let ty =
            match expr.Type with
            | Type.Int -> Type.Int
            | _ -> raise (CompilerException "")

        let inner =
            match expr.Inner with
            | ExprInner.Int i -> ExprInner.Int ~~~i
            | _ -> Nega expr

        { Inner = inner; Type = ty; Category = RValue; IsConst = expr.IsConst }

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

let identifier =
    identifierStr .>>. getUserState
    >>= fun (name, state) ->
        match searchDef state name with
        | Some(def, handler) ->
            let inline makeConstInt (x: 'T) =
                { Inner = x |> int |> ExprInner.Int; Type = Type.Int; Category = RValue; IsConst = true }

            let inline makeConstFloat (x: 'T) =
                { Inner = x |> single |> ExprInner.Float; Type = Type.Float; Category = RValue; IsConst = true }

            preturn (
                match def.Init, def.Type with
                | Some(ConstInt x), Type.Int -> makeConstInt x
                | Some(ConstInt x), Type.Float -> makeConstFloat x
                | Some(ConstFloat x), Type.Int -> makeConstInt x
                | Some(ConstFloat x), Type.Float -> makeConstFloat x
                | _, ty when ty = Type.Int || ty = Type.Float ->
                    // .NET 9 起使用 `.IsInt` 和 `.IsFloat` 属性
                    { Inner = Var handler; Type = ty; Category = LValue; IsConst = false }
                | _, ty -> { Inner = Var handler; Type = ty; Category = RValue; IsConst = false }
            )
        | None -> fail $"Undefined identifier: {name}."

let funcCall =
    attempt (tuple3 identifierStr (between (ch '(') (ch ')') (sepBy expr (ch ','))) getUserState)
    >>= fun (name, args, state) ->
        match searchDef state name with
        | Some(def, handler) ->
            match def.Type with
            | Type.Function(retType, paramTypes) ->
                if paramTypes.Length <> args.Length then
                    fail $"Function {name} argument count mismatch."
                else if not (List.forall2 typeConvertible (args |> List.map _.Type) paramTypes) then
                    fail $"Function {name} argument type mismatch."
                else
                    preturn { Inner = Func(handler, args); Type = retType; Category = RValue; IsConst = false }
            | _ -> fail $"{name} is not a function."
        | None -> fail $"Undefined function: {name}."

// let arrayElem =
//     let checkPointer (indices: Expr) handler baseType lens =
//         if not (List.forall _.Type.IsInt indices) then
//             fail "Array indices must be of type `int`."
//         else


//     attempt (identifierBase .>>. many (between (ch '[') (ch ']') expr))
//     >>= fun ((name, def, handler), indices) ->
//         match def.Type with
//         | Array(elemType, dimensions) -> 1
//         | Pointer(elemType, dimensions) -> 1


let block, blockRef = createParserForwardedToRef ()
let statement, stmtRef = createParserForwardedToRef ()

operatorParser.TermParser <- choice [ literal; funcCall; identifier; parenExpr ]

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

let blockItem = choice [ block |>> Block; statement |>> Statement ]

let blockNoRegion = between (ch '{') (ch '}') (many blockItem)

let ifWhileHelper =
    choice [ blockNoRegion; statement |>> (Statement >> List.singleton) ]

let ifHelper =
    between (updateUserState (enterBlock false)) (updateUserState exitBlock) ifWhileHelper

let whileHelper =
    between (updateUserState (enterBlock true)) (updateUserState exitBlock) ifWhileHelper

let condExpr =
    parenExpr
    >>= fun expr ->
        match expr.Type with
        | Type.Int
        | Type.Float -> preturn expr
        | _ -> fail "Expecting an expression of type `int` or `float`."

let ifElse =
    tuple3 (keyword "if" >>. condExpr) ifHelper (opt (keyword "else" >>. ifHelper) |>> Option.defaultValue [])
    |>> If

let whileLoop = keyword "while" >>. condExpr .>>. whileHelper |>> While

module Definitions =
    let private int_ = keyword "int" >>% Type.Int
    let private float_ = keyword "float" >>% Type.Float
    let private void_ = keyword "void" >>% Void
    let private types = choice [ int_; float_; void_ ]
    let private nonVoidTypes = int_ <|> float_

    let private constInt =
        expr
        >>= fun e ->
            match e.Inner, e.Type with
            | ExprInner.Int i, Type.Int -> preturn i
            | _ -> fail "Expecting an integer constant."

    let private constExpr =
        expr
        >>= fun e ->
            match e.IsConst with
            | true -> preturn e
            | false -> fail "Expecting a constant expression."

    let private param =
        tuple3 nonVoidTypes (opt identifierStr) (opt (ch '[' >>. ch ']' >>. many (between (ch '[') (ch ']') constInt)))
        |>> fun (ty, idOpt, arrDims) ->
            match arrDims with
            | Some dims -> Pointer(ty, dims |> List.map uint64), idOpt
            | None -> ty, idOpt

    let makeFuncDecl newRetType name (newParams: (Type * string option) list) state =
        match searchDef state name with
        | Some(def, _) ->
            match def.Type with
            | Type.Function(retType, paramTypes) when
                newRetType = retType
                && newParams.Length = paramTypes.Length
                && Seq.forall2 (=) (Seq.map fst newParams) paramTypes
                ->
                preturn None
            | _ -> fail $"Conflicting types for {name}"
        | None ->
            updateUserState (fun state ->
                let handler = state.Counter()

                let def =
                    { Init = None
                      Type = Type.Function(newRetType, newParams |> List.map fst)
                      ID = name
                      IsGlobal = true
                      IsArg = false }

                state.SymbolTable.Add(handler, def)
                state.Blocks.Head.SymbolTable.Add(name, handler)
                state)
            >>. preturn None

    let makeFuncDef newRetType name (newParams: (Type * string option) list) state =
        let argHandlers =
            { 1 .. newParams.Length } |> Seq.map (fun _ -> state.Counter()) |> Seq.toList

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
            >>. preturn (Some handler)
        | Some(def, handler) ->
            match def.Type with
            | Type.Function(retType, paramTypes) when
                newRetType = retType
                && newParams.Length = paramTypes.Length
                && Seq.forall2 (=) (Seq.map fst newParams) paramTypes
                && def.Init.IsNone
                ->
                updateUserState (enterFuncBody newRetType >> insertDefs argHandlers argDefs)
                >>. blockNoRegion
                .>> updateUserState exitBlock
                >>= (fun body ->
                    updateUserState (fun state ->
                        state.SymbolTable.[handler] <- makeDef body
                        state))
                >>. preturn (Some handler)
            | _ -> fail $"Conflicting types for {name}."

    let funcDeclDef =
        tuple5
            types
            identifierStr
            (between (ch '(') (ch ')') (sepBy param (ch ',')))
            (choice [ followedBy (ch ';') >>% true; followedBy (ch '{') >>% false ])
            getUserState
        >>= fun (newRetType, name, newParams, isDecl, state) ->
            if isDecl then
                makeFuncDecl newRetType name newParams state
            else
                makeFuncDef newRetType name newParams state

do
    blockRef.Value <-
        between (ch '{' >>. updateUserState (enterBlock false)) (ch '}' >>. updateUserState exitBlock) (many blockItem)

    stmtRef.Value <-
        let exprStmt = expr .>> ch ';' |>> Statement.Expr
        let emptyStmt = ch ';' >>% Empty
        choice [ whileLoop; ifElse; continue_; break_; return_; exprStmt; emptyStmt ]
