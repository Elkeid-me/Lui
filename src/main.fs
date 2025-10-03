open FParsec
open AST

[<EntryPoint>]
let main args =
    match args with
    | [| path |] -> printfn "114514"
    | _ ->
        let result =
            match run Parser.operatorParser.ExpressionParser "- 1000.0/1.0/10.0" with
            | Success(a, _, _) ->
                let a =
                    match a.Inner with
                    | ExprInner.Float f -> f
                    | _ -> exit 1

                a
            | Failure(_, _, _) -> exit 1

        printfn "-1000.0/1.0/10.0 == %f" result

    0
