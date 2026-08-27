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
open Utils
open XParsec
open XParsec.CharParsers
open XParsec.OperatorParsing
open XParsec.Parsers

let inline private makeConstInt (x: ^T) =
    { Inner = Int(int x); Type = Type.Int; Category = RValue; IsConst = true }

let inline private makeConstFloat (x: ^T) =
    { Inner = Float(single x); Type = Type.Float; Category = RValue; IsConst = true }

// let private pIdentifier =
//     let isIdentStartChar c = Char.IsLetter c || c = '_'
//     let isIdentChar c = Char.IsLetterOrDigit c || c = '_'
//     let pIdentStartChar = satisfyL isIdentStartChar "一个字母或下划线"
//     let pIdentChar = satisfyL isIdentChar "一个字母、数字或下划线"
//     many1Chars2 pIdentStartChar pIdentChar

let private skipString s = pstring s >>% ()

let private cxxComment =
    skipString "//" .>> manyCharsTill anyChar (skipNewline <|> eof)

let private blockComment =
    skipString "/*" .>> manyCharsTill anyChar (skipString "*/")

let private ws = skipMany (choice [ cxxComment; blockComment; spaces1 ])

module internal Expressions =
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

    let inline private assignOpCheckBase mustInt constructor (l: Expr) _ (r: Expr) =
        if l.Category <> LValue then failwith "R-value on the left hand side of assign operator."
        let ty = checkType mustInt (if mustInt then l.Type else Type.Int) l r
        { Inner = constructor (l, r); Type = ty; Category = LValue; IsConst = false }

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

    let inline private op s = pstring s .>> ws >>% s
    let inline private makeOpBase con (symbol, prec: Precedence, map: ^T) = con symbol prec (op symbol) map
    let private makeLeftAssocInfixOp = makeOpBase Operator.infixLeftAssoc
    let private makeRightAssocInfixOp = makeOpBase Operator.infixRightAssoc
    let private makePrefixOp = makeOpBase Operator.prefix

    let private operators: Operators<string, unit, Expr, char, unit, ReadableString> =
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
        let cvtInt (base_: int) int_ =
            if int_ = "" then 0 else System.Convert.ToInt32(int_, base_)

        let binDigit = satisfy (fun c -> c = '0' || c = '1')
        let octDigit = satisfy (fun c -> c >= '0' && c <= '7')
        let nonZeroDecDigit = satisfy (fun c -> c >= '1' && c <= '9')
        let hexDigit = satisfy Char.IsAsciiHexDigit

        let inline intBase pHead pDigits base_ =
            pHead .>>. pDigits
            |>> fun struct (head, digits) -> $"{head}{digits}" |> cvtInt base_

        let inline intHead s = pstring s <|> pstring (s.ToUpper())
        let intHex = intBase (intHead "0x") (many1Chars hexDigit) 16
        let intOct = intBase (pchar '0') (manyChars octDigit) 8
        let intBin = intBase (intHead "0b") (many1Chars binDigit) 2
        let intDec = intBase nonZeroDecDigit (manyChars digit) 10
        let intLiteral = choice [ intHex; intBin; intOct; intDec ] |>> makeConstInt

        let floatLiteral =
            let inline expBase s =
                skipAnyOf [ s; Char.ToUpper s ] >>. opt (anyOf [ '+'; '-' ])
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
                    (intHead "0x" >>. manyChars hexDigit .>> skipChar '.' .>>. many1Chars hexDigit
                     |>> fun struct (x, y) ->
                         float (cvtInt 16 x) + float (cvtInt 16 y) / Double.Exp2(float y.Length * 4.0))
                    floatHexExp

            let inline float2Base pHead pDigits = pipe2 (pHead |>> float) pDigits (*)
            let floatDec2 = float2Base (many1Chars digit) floatDecExp
            let floatHex2 = float2Base intHex floatHexExp

            choice [ floatHex1; floatHex2; floatDec1; floatDec2 ] |>> makeConstFloat

        choiceL [ floatLiteral; intLiteral ] "一个整数或浮点数" .>> ws

    let expr = Operator.parser literal operators

let parse path =
    let reader = Reader.ofString (IO.File.ReadAllText(path, Text.Encoding.UTF8)) ()
    Expressions.expr reader
