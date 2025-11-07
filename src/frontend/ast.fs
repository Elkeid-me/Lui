module AST

type Handler = uint
type HashMap<'K, 'V> = System.Collections.Generic.Dictionary<'K, 'V>

type Type =
    | Int
    | Float
    | Void
    | Pointer of Type * uint64 list
    | Array of Type * uint64 list
    | Function of Type * Type list

let rec typeConvertible type_l type_r =
    match type_l, type_r with
    | Int, Int
    | Int, Float
    | Float, Int -> true
    | Pointer(base_l, dims_l), Pointer(base_r, dims_r) when dims_l = dims_r -> typeConvertible base_l base_r
    | Pointer(base_p, dims_p), Array(base_a, dims_a)
    | Array(base_a, dims_a), Pointer(base_p, dims_p) when dims_p = List.tail dims_a -> typeConvertible base_p base_a
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
    | Nega of Expr
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

type ConstInitListItem =
    | Int of int
    | Float of single
    | ConstInitList of ConstInitList

and ConstInitList = ConstInitListItem list

type Init =
    | Function of FunctionInfo
    | Expr of Expr
    | ConstInt of int
    | ConstFloat of single
    | List of InitList
    | ConstList of ConstInitList

type Definition = { Init: Init option; Type: Type; ID: string; IsGlobal: bool; IsArg: bool }

type TranslationUnit = { Ast: Handler list; SymbolTable: HashMap<Handler, Definition> }
