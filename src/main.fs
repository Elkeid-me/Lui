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
