open FParsec
open AST

type HashMap<'K, 'V> = System.Collections.Generic.Dictionary<'K, 'V>

[<EntryPoint>]
let main args =
    match args with
    | [| path |] -> printfn "114514"
    | _ ->
        let testParser parser input =
            let result =
                runParserOnString
                    (Parser.ws >>. parser .>>. getUserState)
                    { Counter = Parser.createCounter ()
                      SymbolTable = HashMap()
                      RetType = Void
                      Blocks = [ { SymbolTable = HashMap(); InLoop = false } ] }
                    ""
                    input

            match result with
            | Success ((ast, state), _, _) ->
                printfn "Parse succeeded:"
                printfn "AST:\n%A" ast
                printfn "Symbol table:\n%A" state
            | Failure (errMsg, _, _) ->
                printfn "Parse failed: %s" errMsg

        testParser Parser.Definitions.funcDeclDef "int f(int return1, int [][2]) { return1 + 1; }"

    0
