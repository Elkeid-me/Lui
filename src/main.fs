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

open System.Threading

let runCompiler path () =
    match Parser.parse path with
    | Ok { Ast = ast; SymbolTable = symbolTable } ->
        printfn "AST: ["

        for handler in ast do
            printfn $"  {handler};"

        printfn "]\nSymbol Table: ["

        for symbol in symbolTable do
            printfn $"  {symbol};"

        printfn "]"
    | Error err ->
        printfn $"Error:\n{err}"
        exit 1

[<EntryPoint>]
let main args =
    match args with
    | [| path |] ->
        let stackSizeBytes = 16 * 1024 * 1024 // 4MB
        let thread = Thread(ThreadStart(runCompiler path), stackSizeBytes)
        thread.Start()
        thread.Join()
        0
    | _ ->
        printfn "Usage: lui <path>"
        exit 1
