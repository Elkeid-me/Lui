open FParsec
open AST

[<EntryPoint>]
let main args =
    match args with
    | [| path |] -> printfn "114514"
    | _ ->
        let result =
            runParserOnString
                (Parser.ifElse .>> eof)
                { retType = Void; Blocks = [ { InLoop = false } ] }
                ""
                @"if (1 + 114514 / 0) {
    break;
}"

        printfn "%A" result

    0
