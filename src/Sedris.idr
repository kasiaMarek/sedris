module Sedris

import public Sedris.Lang
import Sedris.Interpret
import public Data.Regex

export
interpret : (sc : Script [<] Local) -> String -> SnocList String
interpret sc str = interpretS (Just sc) (init str)

namespace SimpleUse
  export
  interpret : (sc : Script [<] Local) -> String
  interpret sc = unlines $ cast $ interpret sc ""

export
interpretIO : {st : FileScriptType} -> (sc : Script [<] st) -> String
            -> IO (Either String (SnocList String))
interpretIO sc str {st = Local} = pure $ Right $ interpret sc str
interpretIO sc str {st = IO}    = interpretS (Just sc) (init str)
interpretIO sc str {st = Std}   = interpretS (Just sc) (init str)
