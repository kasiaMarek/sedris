module Sedris

import System.File
import public Data.Regex

public export
data SedCommand =
    Substitute (TyRE a) (a -> String)
  | Delete (TyRE a)

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