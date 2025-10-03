module Parser

open AST
open FParsec

exception CompilerException of string

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

let pLiteral =
    let makeFloat f =
        { Inner = f |> single |> ExprInner.Float
          Type = Type.Float
          Category = ValueCategory.RValue
          IsConst = true }

    let makeInt i =
        { Inner = ExprInner.Int i; Type = Type.Int; Category = ValueCategory.RValue; IsConst = true }

    choice [ pfloat .>> spaces |>> makeFloat; pint32 .>> spaces |>> makeInt ]

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
            Precedence = 11
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

let operatorParser = OperatorPrecedenceParser<Expr, unit, unit>()

operatorParser.TermParser <- pLiteral

Operators.infixOperators
|> List.iter (fun details ->
    let operator =
        InfixOperator(details.Symbol, spaces, details.Precedence, details.Assoc, details.Map)

    operatorParser.AddOperator operator)

Operators.prefixOperators
|> List.iter (fun details ->
    let operator =
        PrefixOperator(details.Symbol, spaces, details.Precedence, true, details.Map)

    operatorParser.AddOperator operator)

Operators.postfixOperators
|> List.iter (fun details ->
    let operator =
        PostfixOperator(details.Symbol, spaces, details.Precedence, true, details.Map)

    operatorParser.AddOperator operator)
