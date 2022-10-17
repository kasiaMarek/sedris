import Sedris.Lang

tenLastLines : IOFile -> Script [<] IO
tenLastLines fileName =
  [ |> CreateHold "lns" {t = List String} []
  , [fileName] *
    [ > HoldApp "lns" (\l,s => l ++ [s ++ "\n"])
    , Not (LineRange 1 10)
        ?> ExecOnHold "lns"
                      {t = List String}
                      (\case  []      => []
                              (x::xs) => xs)
    , LastLine ?> FromHold "lns" (const $ fastConcat)
    , LastLine ?> Print]
  ]