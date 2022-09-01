module Sedris

import System.File
import public Data.Regex

public export
data SedCommand : Type where
  Substitute : (tyre: TyRE a) -> {auto 0 _ : IsConsuming tyre} -> (a -> String)
            -> SedCommand
  Delete : (tyre : TyRE a) -> {auto 0 _ : IsConsuming tyre} -> SedCommand

exec : SedCommand -> String -> String
exec (Substitute tyre f)  = substitute tyre f
exec (Delete tyre)        = substitute tyre (\_ => "")

runScript : List SedCommand -> String -> String
runScript xs str = foldl (\str,cm => exec cm str) "" xs

export
sed : List SedCommand -> String -> IO ()
sed cmds fileName = do  file <- readFile fileName -- for now, we read file as string
                        case file of
                            Right content => printLn $ runScript cmds content
                            Left err => printLn $ err