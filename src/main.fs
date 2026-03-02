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

open AST
type HashMap<'K, 'V> = System.Collections.Generic.Dictionary<'K, 'V>

[<EntryPoint>]
let main args =
    match args with
    | [| path |] ->
        match Parser.parse path with
        | Ok { Ast = ast; SymbolTable = symbolTable } ->
            printfn "AST: %A" ast
            printfn "Symbol Table: %A" symbolTable
        | Error err -> printfn "Error: %s" err
    | _ -> printfn "Please provide a file path."

    0
