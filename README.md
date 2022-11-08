A GNU sed  inspired tool for text editing in Idris 2

There are two functions for executing serdis scripts:
```Idris
interpret   : (sc : Script [<] Local) -> String -> SnocList String
interpretIO : {st : FileScriptType} -> (sc : Script [<] st) -> String
            -> IO (Either FileError (SnocList String))
```
Both take a script and initial input (init pattern space content; in most cases this should be "") as arguments. The first one allows only for dealing with in-memory text.

A sedris script is executed from top to bottom only once. It can contain `file scripts`, which are executed per each line of: a file, std input, or in-memory file (list strings).

Example scripts can be found in the `test` folder and all available commands in `src/Sedris/Lang.idr`.

Sed manual: https://www.gnu.org/software/sed/manual/sed.html#sed-script-overview