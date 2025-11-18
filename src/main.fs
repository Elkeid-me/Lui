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

open FParsec
open AST

type HashMap<'K, 'V> = System.Collections.Generic.Dictionary<'K, 'V>

[<EntryPoint>]
let main args =
    match args with
    | [| path |] ->
        let testParser parser input =
            let result =
                runParserOnFile
                    (Parser.ws >>. parser .>> eof)
                    { Counter = Parser.createCounter ()
                      SymbolTable = HashMap()
                      RetType = Void
                      ParsingType = Type.Int
                      Blocks = [ { SymbolTable = HashMap(); InLoop = false } ] }
                    input
                    System.Text.Encoding.UTF8

            match result with
            | Success(ast, state, _) ->
                let translationUnit = { Ast = ast; SymbolTable = state.SymbolTable }
                printfn "Parse succeeded:\n%A" translationUnit
            | Failure(errMsg, _, _) -> printfn "%s" errMsg

        testParser Parser.translationUnit path
    | _ -> printfn "Please provide a file path."

    0
