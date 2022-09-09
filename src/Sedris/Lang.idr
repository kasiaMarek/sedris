module Sedris.Lang

import public Data.Regex
import public Data.SnocList
import public Data.SnocList.Elem

prefix  1 |>,>
infix   1 ?>,?:
infix   2 *,*>
prefix  2 |*>

public export
withOut : (xs : SnocList a) -> (x `Elem` xs) -> SnocList a
withOut (sx :< _) Here = sx
withOut (sx :< x) (There pos) = (withOut sx pos) :< x

public export
LocalFile : Type
LocalFile = List String

public export
IOFile : Type
IOFile = (String, String, String)

public export
data FileScriptType = Local | IO | Std

public export
chooseFileIn : FileScriptType -> Type
chooseFileIn Local = LocalFile
chooseFileIn IO    = IOFile
chooseFileIn Std   = ()

public export
chooseFileOut : FileScriptType -> Type
chooseFileOut Local = LocalFile
chooseFileOut IO    = IOFile
chooseFileOut Std   = IOFile

public export
data VarType
  = HoldSpace Type
  | Label

public export
data NeedsIO : FileScriptType -> Type where
  IsIO  : NeedsIO IO
  IsStd : NeedsIO Std

||| Address is a condition for the command.
||| Only for the lines that satisfy the address, the command will be executed.
public export
data Address
  = ||| Line number
    Line Nat
  | ||| Line numbers
    Lines (List Nat)
  |  ||| Range of lines
    LineRange Nat Nat
  | ||| If the line as a whole matches the regex
    RegexWhole (TyRE a)
  | ||| If the line's prefix matches the regex
    RegexPrefix (TyRE a)
  | ||| If there exists a substring in the line that matches the regex
    RegexExists (TyRE a)
  | ||| Condition negation
    Not Address
  | ||| Last line of the text
    LastLine
  | ||| When we start working with a new file
    OnNewFile

public export
data ReplaceCommand : Type where
  ||| Replace all `pattern` with `substitution`
  All : (pattern : String) -> (substitution : String) -> ReplaceCommand
  ||| String substitusions for a list of: pattern, destination.
  AllMulti : List (String, String) -> ReplaceCommand
  ||| String substitusions for a list of patterns and vector of destinations.
  AllMulti' : (xs : List String) -> (Vect (length xs) String) -> ReplaceCommand
  ||| String substitusion for the line prefix.
  Prefix : String -> String -> ReplaceCommand
  ||| String substitusion for the line suffix.
  Suffix : String -> String -> ReplaceCommand
  ||| Regex replace for all matches.
  AllRe : (TyRE a) -> (a -> String) -> ReplaceCommand
  ||| Regex replace for a prefix match.
  PrefixRe : (TyRE a) -> (a -> String) -> ReplaceCommand
  ||| Regex replace for a suffix match.
  SuffixRe : (TyRE a) -> (a -> String) -> ReplaceCommand -- in tyre we need to revert the regex and the string to do a prefix match
  ||| Character substitusions for a list of: pattern, destination.
  CharSubst : List (Char, Char) -> ReplaceCommand
  ||| Character substitusions for a list of patterns and vector of destinations.
  CharSubst' : (xs : List Char) -> (Vect (length xs) Char) -> ReplaceCommand

mutual
  public export
  data LineCommand : SnocList (VarType, String) -> List (VarType, String)
                  -> FileScriptType -> Type where
    |||Delete the contents of the pattern space and start a new cycle
    Zap : LineCommand sx [] t
    |||Delete the contents of the pattern space up to the `\n`
    |||and start the new cycle without reading the next line.
    |||If no `\n` in the pattern space treat as `Zap`.
    ZapFstLine : LineCommand sx [] t
    |||Append a newline and the next line from input to the pattern space
    ReadApp : LineCommand sx [] t
    |||Read the next line into the pattern space (deleting what was previously stored)
    Put : LineCommand sx [] t
    |||Print the line number
    LineNumber : LineCommand sx [] t
    |||Start new cycle
    NewCycle : LineCommand sx [] t
    |||Start reading from a new file
    ReadFrom : {t : FileScriptType} -> (chooseFileOut t) -> LineCommand sx [] t
    |||Queue next file to read
    QueueRead : {t : FileScriptType} -> (chooseFileOut t) -> LineCommand sx [] t
    ||| Create a routine
    LineRoutine : (label : String) -> FileScript sx t
                -> LineCommand sx [(Label, label)] t
    LineIfThenElse : (String -> Bool) -> FileScript sx t -> FileScript sx t
                   -> LineCommand sx [] t
    ||| Allows for executing code with value from a chosen holdspace.
    ||| This holdspace does not exist inside that scope.
    ||| For simplicity global definitions are not allowed in routines.
    LineWithHoldContent : (holdSpace : String)
                        -> {ty : Type}
                        -> {auto pos : (HoldSpace ty, holdSpace) `Elem` sx}
                        -> (ty -> FileScript (withOut sx pos) t)
                        -> LineCommand sx [] t
    --- other IO commands ---
    |||Print content of the pattern space
    PrintStd : {t : FileScriptType} -> {auto _ : NeedsIO t} -> LineCommand sx [] t
    ||| Append contents of the pattern space to a file
    ||| which names depends on current file name - (path, name, extension)
    WriteTo : {t : FileScriptType} -> {auto _ : NeedsIO t}
            -> (chooseFileIn t -> chooseFileOut t) -> LineCommand sx [] t
    ||| Append contents of the pattern space up to `\n` to a file
    ||| which names depends on current file name - (path, name, extension)
    WriteLineTo : {t : FileScriptType} -> {auto _ : NeedsIO t}
                -> (chooseFileIn t -> chooseFileOut t) -> LineCommand sx [] t
    ||| Delete file contents
    ||| which names depends on current file name - (path, name, extension)
    ClearFile : {t : FileScriptType} -> {auto _ : NeedsIO t}
              -> (chooseFileIn t -> chooseFileOut t) -> LineCommand sx [] t
    |||Print the file name
    FileName : {t : FileScriptType} -> {auto _ : NeedsIO t}
            -> LineCommand sx [] t

  public export
  data Command : SnocList (VarType, String) -> List (VarType, String)
              -> Type where
  --- pattern space operation commands
    ||| Replace command
    Replace : ReplaceCommand -> Command sx []
    |||Execute function on the pattern space
    Exec : (String -> String) -> Command sx []
  --- read/write commands ---
    |||Print content of the pattern space to the result space
    Print : Command sx []
  --- commands for hold spaces ---
    |||Copy contents of pattern space to a named hold space (local)
    CreateHold  : (holdSpace : String)
                -> {t : Type} -> t
                -> Command sx [(HoldSpace t, holdSpace)]
    |||Append a newline and contents of pattern space to a named hold space
    HoldApp : (holdSpace : String)
            -> {t : Type} -> (t -> String -> t)
            -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
            -> Command sx []
    |||Copy contents of a named hold space to pattern space
    FromHold  : (holdSpace : String)
              -> {t : Type} -> (String -> t -> String)
              -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
              -> Command sx []
    |||Execute a function on a hold space contents
    ExecOnHold : (holdSpace : String)
              -> {t : Type} -> (t -> t)
              -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
              -> Command sx []
  --- flow control commands ---
    ||| Create a routine
    Routine : (label : String) -> Script sx -> Command sx [(Label, label)]
    ||| Go to routine with named `label`
    Call : (label : String) -> {auto pos : (Label, label) `Elem` sx}
              -> Command sx []
    ||| If then else contruction
    IfThenElse : (String -> Bool) -> Script sx -> Script sx
              -> Command sx []
    ||| Allows for executing code with value from a chosen holdspace.
    ||| This holdspace does not exist inside that scope.
    ||| For simplicity global definitions are not allowed in routines.
    WithHoldContent : (holdSpace : String)
                    -> {t : Type}
                    -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
                    -> (t -> Script (withOut sx pos))
                    -> Command sx []
  --- other ---
    |||Quit
    Quit : Command sx [] -- q;Q

  public export
  data AnyCommand : SnocList (VarType, String) -> List (VarType, String)
                  -> FileScriptType -> Type where
    LC : LineCommand sx ys t -> AnyCommand sx ys t
    NC : Command sx ys       -> AnyCommand sx ys t

  public export
  data CommandWithAddress : SnocList (VarType, String)
                          -> List (VarType, String)
                          -> FileScriptType
                          -> Type where
    (>)  : AnyCommand sx ys t -> CommandWithAddress sx ys t
    (?>) : Address -> AnyCommand sx ys t -> CommandWithAddress sx [] t
    (?:) : Address -> FileScript sx t -> CommandWithAddress sx [] t
    --^ this allows to group multiple commands with the same address, but the 

  ||| A file script is executed on each line of the file
  public export
  data FileScript : SnocList (VarType, String) -> FileScriptType -> Type where
    Nil : FileScript sx t
    (::) : CommandWithAddress sx ys t -> FileScript (sx <>< ys) t
        -> FileScript sx t

  public export
  data ScriptCommand : SnocList (VarType, String) -> List (VarType, String)
                    -> Type where
    (*)   : List1 String -> FileScript sx IO -> ScriptCommand sx [] -- IO
    (|*>) : FileScript sx Std -> ScriptCommand sx [] -- IO
    ||| Line by line processing for in program data
    (*>)  : List String -> FileScript sx Local -> ScriptCommand sx []
    (|>)  : Command sx ys -> ScriptCommand sx ys

  namespace Script
    public export
    data Script : SnocList (VarType, String) -> Type where
      Nil : Script sx
      (::) : ScriptCommand sx ys -> Script (sx <>< ys) -> Script sx

--- smart constucturs ---
namespace SmartConstructorsLineCommand
  public export
  (?>) : Address -> LineCommand sx ys t -> CommandWithAddress sx [] t
  addr ?> cmd = addr ?> (LC cmd)
  public export
  (>) : LineCommand sx ys t -> CommandWithAddress sx ys t
  (>) cmd = > (LC cmd)

namespace SmartConstructorsCommand
  public export
  (?>) : Address -> Command sx ys -> CommandWithAddress sx [] t
  addr ?> cmd = addr ?> (NC cmd)
  public export
  (>) : Command sx ys -> CommandWithAddress sx ys t
  (>) cmd = > (NC cmd)
