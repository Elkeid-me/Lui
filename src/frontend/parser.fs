module Parser

open AST
open FParsec

exception CompilerException of string

type BlockInfo = { InLoop: bool }
type FunInfo = { retType: Type; Blocks: BlockInfo list }

let inLoop (state: FunInfo) = (List.head state.Blocks).InLoop

let enterBlock loopNow (state: FunInfo) =
    let inLoop = if loopNow then true else inLoop state
    { state with Blocks = { InLoop = inLoop } :: state.Blocks }

let exitBlock (state: FunInfo) =
    { state with Blocks = List.tail state.Blocks }

let boolIntFun f a b = if f a b then 1 else 0

let arithOpCheck fnInt fnFloat con (l: Expr) (r: Expr) =
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
        | _ -> con (l, r)

    { Inner = inner; Type = ty; Category = ValueCategory.RValue; IsConst = l.IsConst && r.IsConst }

let intOpCheck fnInt con (l: Expr) (r: Expr) =
    match l.Type, r.Type with
    | Type.Int, Type.Int -> ()
    | _ -> raise (CompilerException "Invalid type of operands.")

    let inner =
        match l.Inner, r.Inner with
        | ExprInner.Int l, ExprInner.Int r -> ExprInner.Int(fnInt l r)
        | _ -> con (l, r)

    { Inner = inner
      Type = Type.Int
      Category = ValueCategory.RValue
      IsConst = l.IsConst && r.IsConst }

let logicOpCheck fnLogic con (l: Expr) (r: Expr) =
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
        | _ -> con (l, r)

    { Inner = inner
      Type = Type.Int
      Category = ValueCategory.RValue
      IsConst = l.IsConst && r.IsConst }

let relOpCheck fnIntComp fnFloatComp con (l: Expr) (r: Expr) =
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
        | _ -> con (l, r)

    { Inner = inner
      Type = Type.Int
      Category = ValueCategory.RValue
      IsConst = l.IsConst && r.IsConst }

let assignOpCheck con (l: Expr) (r: Expr) =
    if l.Category <> ValueCategory.LValue then
        raise (CompilerException "R-value on the left hand side if assign operator.")

    let ty =
        match l.Type, r.Type with
        | Type.Int, Type.Int
        | Type.Int, Type.Float -> Type.Int
        | Type.Float, Type.Int
        | Type.Float, Type.Float -> Type.Float
        | _ -> raise (CompilerException "Invalid type of operands.")

    let inner = con (l, r)

    { Inner = inner; Type = ty; Category = ValueCategory.LValue; IsConst = false }

let intAssignOpCheck con (l: Expr) (r: Expr) =
    if l.Category <> ValueCategory.LValue then
        raise (CompilerException "R-value on the left hand side if assign operator.")

    let ty =
        match l.Type, r.Type with
        | Type.Int, Type.Int -> Type.Int
        | _ -> raise (CompilerException "Invalid type of operands.")

    let inner = con (l, r)

    { Inner = inner; Type = ty; Category = ValueCategory.LValue; IsConst = false }

let cxxComment = skipString "//" .>> manyCharsTill anyChar skipNewline
let blockComment = skipString "/*" .>> manyCharsTill anyChar (skipString "*/")
let singleSpace = choiceL [ cxxComment; blockComment; skipAnyOf " \t\n" ] ""
let ws = skipMany singleSpace

let str s = pstring s .>> ws
let ch c = pchar c .>> ws

let literal =
    let makeFloat f =
        { Inner = f |> single |> ExprInner.Float
          Type = Type.Float
          Category = ValueCategory.RValue
          IsConst = true }

    let makeInt i =
        { Inner = ExprInner.Int i; Type = Type.Int; Category = ValueCategory.RValue; IsConst = true }

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

    let leiArithInt f a b =
        match a, b with
        | a, 0 -> a
        | a, b -> f a b

    let leiArithFloat f a b =
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

    let checkNot (expr: Expr) =
        match expr.Type with
        | Type.Int
        | Type.Float -> ()
        | _ -> raise (CompilerException "")

        let inner =
            match expr.Inner with
            | ExprInner.Int i -> ExprInner.Int(boolIntFun (=) i 0)
            | ExprInner.Float f -> ExprInner.Int(boolIntFun (=) f 0.0f)
            | _ -> LogicNot expr

        { Inner = inner; Type = Type.Int; Category = ValueCategory.RValue; IsConst = expr.IsConst }

    let checkNega (expr: Expr) =
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

        { Inner = inner; Type = ty; Category = ValueCategory.RValue; IsConst = expr.IsConst }

    let prefixOperators =
        [ { Symbol = "!"; Precedence = 12; Map = checkNot }
          { Symbol = "+"; Precedence = 12; Map = id }
          { Symbol = "-"; Precedence = 12; Map = checkNega }
          { Symbol = "~"; Precedence = 12; Map = id }
          { Symbol = "++"; Precedence = 12; Map = id }
          { Symbol = "--"; Precedence = 12; Map = id } ]

    let postfixOperators =
        [ { Symbol = "++"; Precedence = 13; Map = id }
          { Symbol = "--"; Precedence = 13; Map = id } ]

let operatorParser = OperatorPrecedenceParser<Expr, unit, FunInfo>()

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
    pstring str .>> notFollowedBy (regex @"[a-zA-Z0-9_]") .>> ws

let expr = operatorParser.ExpressionParser .>> ws <?> "an expression."
let parenExpr = between (ch '(') (ch ')') expr

let block, blockRef = createParserForwardedToRef ()
let statement, stmtRef = createParserForwardedToRef ()

operatorParser.TermParser <- literal <|> parenExpr

let break_ =
    keyword "break" .>> ch ';' >>. getUserState
    >>= fun state ->
        match inLoop state with
        | true -> preturn Break
        | false -> fail "`break` statement must be used in loop."

let continue_ =
    keyword "continue" .>> ch ';' >>. getUserState
    >>= fun state ->
        match inLoop state with
        | true -> preturn Continue
        | false -> fail "`continue` statement must be used in loop."

let return_ =
    let checkExpr state (expr: Expr) =
        if typeConvertible expr.Type state.retType then
            preturn (Some expr)
        else
            fail "Return expression type mismatch."

    keyword "return" >>. getUserState
    >>= fun state ->
        match state.retType with
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

do
    blockRef.Value <-
        between (ch '{' >>. updateUserState (enterBlock false)) (ch '{' >>. updateUserState exitBlock) (many blockItem)

    stmtRef.Value <-
        let exprStmt = expr .>> ch ';' |>> Statement.Expr
        let emptyStmt = ch ';' >>% Empty
        choice [ whileLoop; ifElse; continue_; break_; return_; exprStmt; emptyStmt ]
