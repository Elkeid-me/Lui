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

module Utils

open System.Runtime.CompilerServices

[<AutoOpen>]
type Impl =
    static member inline panic(?message: string, [<CallerFilePath>] ?file: string, [<CallerLineNumber>] ?line: int) =
        let message = defaultArg message "Unknown error."
        let file = defaultArg file "unknown"
        let line = defaultArg line 0
        printfn $"\"{message}\" happened at file {file}, line {line}"
        exit 1

    static member inline todo([<CallerFilePath>] ?file: string, [<CallerLineNumber>] ?line: int) =
        let file = defaultArg file "unknown"
        let line = defaultArg line 0
        printfn $"Not implemented at file {file}, line {line}"
        exit 1

    static member inline unreachable([<CallerFilePath>] ?file: string, [<CallerLineNumber>] ?line: int) =
        let file = defaultArg file "unknown"
        let line = defaultArg line 0
        printfn $"Unreachable code at file {file}, line {line}"
        exit 1

let inline structFst struct (a: ^a, _: ^b) = a
