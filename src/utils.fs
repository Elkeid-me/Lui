module Utils

open System.Runtime.CompilerServices

type private Detail =
    static member panic(?message: string, [<CallerFilePath>] ?file: string, [<CallerLineNumber>] ?line: int) =
        let message = defaultArg message "Unknown error."
        printfn "\"%s\" happened at file %s, line %d" message (defaultArg file "unknown") (defaultArg line 0)
        exit 1

let unreachable () = Detail.panic "Unreachable code."

let todo () = Detail.panic "Not implemented."
