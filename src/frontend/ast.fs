// Copyright (C) 2025-2026 Elkeid Me
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

module AST

open System.Collections.Immutable

type Handler = uint

type Type =
    | Int
    | Float
    | Void
    | Pointer of Type
    | Array of Type * uint64
    | Function of Type * ImmutableArray<Type>

let rec typeCastable typeFrom typeTo =
    match typeFrom, typeTo with
    | Int, Int
    | Int, Float
    | Float, Int -> true
    | Pointer baseFrom, Pointer baseTo -> typeCastable baseFrom baseTo
    | Array(baseA, _), Pointer baseP -> baseA = baseP
    | _ -> false

type ValueCategory =
    | LValue
    | RValue

type ExprInner =
    | Mul of struct (Expr * Expr)
    | Div of struct (Expr * Expr)
    | Mod of struct (Expr * Expr)
    | Add of struct (Expr * Expr)
    | Sub of struct (Expr * Expr)

    | ShL of struct (Expr * Expr)
    | SaR of struct (Expr * Expr)
    | Xor of struct (Expr * Expr)
    | And of struct (Expr * Expr)
    | Or of struct (Expr * Expr)

    | Eq of struct (Expr * Expr)
    | Neq of struct (Expr * Expr)
    | Grt of struct (Expr * Expr)
    | Geq of struct (Expr * Expr)
    | Les of struct (Expr * Expr)
    | Leq of struct (Expr * Expr)

    | LogicAnd of struct (Expr * Expr)
    | LogicOr of struct (Expr * Expr)

    | LogicNot of Expr
    | Neg of Expr
    | Not of Expr

    | PostInc of Expr
    | PostDec of Expr
    | PreInc of Expr
    | PreDec of Expr

    | Assignment of struct (Expr * Expr)
    | AddAssign of struct (Expr * Expr)
    | SubAssign of struct (Expr * Expr)
    | MulAssign of struct (Expr * Expr)
    | DivAssign of struct (Expr * Expr)
    | ModAssign of struct (Expr * Expr)
    | AndAssign of struct (Expr * Expr)
    | OrAssign of struct (Expr * Expr)
    | XorAssign of struct (Expr * Expr)
    | ShLAssign of struct (Expr * Expr)
    | SaRAssign of struct (Expr * Expr)

    | Int of int
    | Float of single
    | Var of Handler
    | Func of Handler * ImmutableArray<Expr>
    | ArrayElem of Handler * ImmutableArray<Expr>

and Expr = { Inner: ExprInner; Type: Type; Category: ValueCategory; IsConst: bool }

type Statement =
    | Expr of Expr
    | If of struct (Expr * Block * Block)
    | While of struct (Expr * Block)
    | Return of Expr voption
    | Break
    | Continue
    | Empty

and BlockItem =
    | Statement of Statement
    | Def of Handler list
    | Block of Block

and Block = ImmutableArray<BlockItem>

type FunctionInfo = { Block: Block; ArgHandlers: Handler list }

type InitListItem =
    | Expr of Expr
    | InitList of InitList

and InitList = InitListItem list

type Init =
    | Function of FunctionInfo
    | Expr of Expr
    | List of InitList

type Definition = { Init: Init voption; Type: Type; ID: string; IsGlobal: bool; IsArg: bool; IsConst: bool }
type SymbolTableType = Map<Handler, Definition>
type TranslationUnit = { Ast: Handler list; SymbolTable: SymbolTableType }
