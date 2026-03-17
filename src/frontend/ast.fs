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

type Handler = uint

type Type =
    | Int
    | Float
    | Void
    | Pointer of Type
    | Array of Type * uint64
    | Function of Type * Type list

let rec typeCastable typeL typeR =
    match typeL, typeR with
    | Int, Int
    | Int, Float
    | Float, Int -> true
    | Pointer baseL, Pointer baseR -> typeCastable baseL baseR
    | Array(baseA, _), Pointer baseP -> baseA = baseP
    | _ -> false

type ValueCategory =
    | LValue
    | RValue

type ExprInner =
    | Mul of Expr * Expr
    | Div of Expr * Expr
    | Mod of Expr * Expr
    | Add of Expr * Expr
    | Sub of Expr * Expr

    | ShL of Expr * Expr
    | SaR of Expr * Expr
    | Xor of Expr * Expr
    | And of Expr * Expr
    | Or of Expr * Expr

    | Eq of Expr * Expr
    | Neq of Expr * Expr
    | Grt of Expr * Expr
    | Geq of Expr * Expr
    | Les of Expr * Expr
    | Leq of Expr * Expr

    | LogicAnd of Expr * Expr
    | LogicOr of Expr * Expr

    | LogicNot of Expr
    | Neg of Expr
    | Not of Expr

    | PostInc of Expr
    | PostDec of Expr
    | PreInc of Expr
    | PreDec of Expr

    | Assignment of Expr * Expr
    | AddAssign of Expr * Expr
    | SubAssign of Expr * Expr
    | MulAssign of Expr * Expr
    | DivAssign of Expr * Expr
    | ModAssign of Expr * Expr
    | AndAssign of Expr * Expr
    | OrAssign of Expr * Expr
    | XorAssign of Expr * Expr
    | ShLAssign of Expr * Expr
    | SaRAssign of Expr * Expr

    | Int of int
    | Float of single
    | Var of Handler
    | Func of Handler * Expr list
    | ArrayElem of Handler * Expr list

and Expr = { Inner: ExprInner; Type: Type; Category: ValueCategory; IsConst: bool }

type Statement =
    | Expr of Expr
    | If of Expr * Block * Block
    | While of Expr * Block
    | Return of Expr option
    | Break
    | Continue
    | Empty

and BlockItem =
    | Statement of Statement
    | Def of Handler list
    | Block of Block

and Block = BlockItem list

type FunctionInfo = { Block: Block; ArgHandlers: Handler list }

type InitListItem =
    | Expr of Expr
    | InitList of InitList

and InitList = InitListItem list

type Init =
    | Function of FunctionInfo
    | Expr of Expr
    | List of InitList

type Definition = { Init: Init option; Type: Type; ID: string; IsGlobal: bool; IsArg: bool; IsConst: bool }

type TranslationUnit = { Ast: Handler list; SymbolTable: Map<Handler, Definition> }
