import Sedris.Lang

tenLastLines : String -> Script [<]
tenLastLines fileName
  = [ |> CreateHold "lines" {t = List String} []
    , [fileName] *
      [ > HoldApp "lines" (\list,str => list ++ [str ++ "\n"])
      , Not (LineRange 1 10)
          ?> ExecOnHold "lines"
                        {t = List String}
                        (\case  []      => []
                                (x::xs) => xs)
      , LastLine ?> FromHold "lines" (const $ fastConcat)
      , LastLine ?> Print]
    ]