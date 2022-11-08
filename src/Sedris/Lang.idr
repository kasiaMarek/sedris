module Sedris.Lang

import public Data.Regex
import public Data.SnocList
import public Data.SnocList.Elem
import public Data.DPair

%default total

prefix  1 |>,>
infix   1 ?>,?:
infix   2 *,*>
prefix  2 |*>

||| We have two types of scripts
||| 1) normal, total script
||| 2) scripts executed line by line for files
public export
data ScriptType = Total | LineByLine

||| A file loaded into memory, represented as a list of lines
public export
LocalFile : Type
LocalFile = List String

||| A file stored on the OS
public export
IOFile : Type
IOFile = String

public export
data FileScriptType = Local | IO | Std

public export
chooseFileSrc : FileScriptType -> Type
chooseFileSrc Local = LocalFile
chooseFileSrc _ = Either IOFile LocalFile


public export
data MatchesFileScriptType : FileScriptType -> FileScriptType -> Type where
  Matches : MatchesFileScriptType io io
  AreLocalStd : MatchesFileScriptType Local Std
  AreLocalIO : MatchesFileScriptType Local IO
  AreStdIO : MatchesFileScriptType Std IO

public export
data VarType
  = HoldSpace Type
  | Label ScriptType FileScriptType

public export
data NeedsIO : FileScriptType -> Type where
  IsIO  : NeedsIO IO
  IsStd : NeedsIO Std

public export
Variable : Type
Variable = (VarType, String)

public export
Variables : Type
Variables = SnocList Variable

||| Address is a condition for the command.
||| Only for the lines that satisfy the address, the command will be executed.
public export
data Address : Type where
    ||| Line number
    Line : Nat -> Address
    ||| Line numbers
    Lines : (List Nat) -> Address
    ||| Range of lines
    LineRange : Nat -> Nat -> Address
    ||| If the line as a whole matches the regex
    RegexWhole : TyRE a -> Address
    ||| If the line's prefix matches the regex
    RegexPrefix : (re : TyRE a) -> Address
    ||| If there exists a substring in the line that matches the regex
    RegexExists : (re : TyRE a) -> {auto 0 _ : IsConsuming re}-> Address
    ||| Condition negation
    Not : Address -> Address
    ||| Last line of the text
    LastLine : Address

public export
data ReplaceCommand : Type where
  ||| Replace all `pattern` with `substitution`
  All : (pattern : String) -> (substitution : String) -> ReplaceCommand
  ||| String substitusion for the line prefix.
  Prefix : String -> String -> ReplaceCommand
  ||| String substitusion for the line suffix.
  Suffix : String -> String -> ReplaceCommand
  ||| Regex replace for all matches.
  AllRe : (re : TyRE a) -> {auto 0 consuming : IsConsuming re}
        -> (a -> String) -> ReplaceCommand
  ||| Regex replace for a prefix match.
  PrefixRe : (re : TyRE a) -> {auto 0 consuming : IsConsuming re}
          -> (a -> String) -> ReplaceCommand
  ||| Character substitusions for a list of patterns and vector of destinations.
  CharSubst : List (Char, Char) -> ReplaceCommand

mutual
  public export
  data Command : Variables -> List Variable
              -> ScriptType -> FileScriptType -> Type where
  --- pattern space operation commands
    ||| Replace command
    Replace : ReplaceCommand -> Command sx [] st io
    |||Execute function on the pattern space
    Exec : (String -> String) -> Command sx [] st io
  --- read/write commands ---
    |||Print content of the pattern space to the result space
    Print : Command sx [] st io
  --- commands for hold spaces ---
    |||Copy contents of pattern space to a named hold space (local)
    CreateHold  : (holdSpace : String)
                -> {t : Type} -> t
                -> Command sx [(HoldSpace t, holdSpace)] st io
    |||Append a newline and contents of pattern space to a named hold space
    HoldApp : (holdSpace : String)
            -> {t : Type} -> (t -> String -> t)
            -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
            -> Command sx [] st io
    |||Copy contents of a named hold space to pattern space
    FromHold  : (holdSpace : String)
              -> {t : Type} -> (String -> t -> String)
              -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
              -> Command sx [] st io
    |||Execute a function on a hold space contents
    ExecOnHold : (holdSpace : String)
              -> {t : Type} -> (t -> t)
              -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
              -> Command sx [] st io
  --- flow control commands ---
    ||| Create a routine
    Routine : (label : String)
            -> {st : ScriptType}
            -> {io : FileScriptType}
            -> {default io io' : FileScriptType}
            -> {auto mol : MatchesFileScriptType io' io}
            -> getScriptByType st sx io'
            -> Command sx [(Label st io', label)] st io
    ||| Go to routine with named `label`
    Call : (label : String)
        -> {io : FileScriptType}
        -> {default io io' : FileScriptType}
        -> {auto mol : MatchesFileScriptType io' io}
        -> {auto pos : (Label st io', label) `Elem` sx}
        -> Command sx [] st io
    -- ||| If then else contruction
    IfThenElse : (String -> Bool)
              -> {st : ScriptType}
              -> getScriptByType st sx io -> getScriptByType st sx io
              -> Command sx [] st io
    ||| Allows for executing code with value from a chosen holdspace.
    ||| This holdspace does not exist inside that scope.
    ||| For simplicity global definitions are not allowed in routines.
    WithHoldContent : (holdSpace : String)
                    -> {t : Type}
                    -> {st : ScriptType}
                    -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
                    -> (t -> getScriptByType st sx io)
                    -> Command sx [] st io
  --- other ---
    |||Quit
    Quit : Command sx [] st io -- q;Q
  --- line by line commands
    |||Delete the contents of the pattern space and start a new cycle
    Zap : Command sx [] LineByLine t
    |||Delete the contents of the pattern space up to the `\n`
    |||and start the new cycle without reading the next line.
    |||If no `\n` in the pattern space treat as `Zap`.
    ZapFstLine : Command sx [] LineByLine t
    |||Append a newline and the next line from input to the pattern space
    ReadApp : Command sx [] LineByLine t
    |||Read the next line into the pattern space (deleting what was previously stored)
    Put : Command sx [] LineByLine t
    |||Print the line number
    LineNumber : Command sx [] LineByLine t
    |||Start new cycle
    NewCycle : Command sx [] LineByLine t
    |||Start reading from a new file
    ReadFrom : (chooseFileSrc t) -> Command sx [] LineByLine t
    |||Queue next file to read
    QueueRead : (chooseFileSrc t) -> Command sx [] LineByLine t
    --- other IO commands ---
    |||Print content of the pattern space
    PrintStd : {0 t : FileScriptType} -> {auto isIO : NeedsIO t}
            -> Command sx [] st t
    ||| Append contents of the pattern space to a file
    ||| which names depends on current file name - (path, name, extension)
    WriteTo : {0 t : FileScriptType} -> {auto isIO : NeedsIO t}
            -> IOFile -> Command sx [] LineByLine t
    ||| Append contents of the pattern space up to `\n` to a file
    ||| which names depends on current file name - (path, name, extension)
    WriteLineTo : {0 t : FileScriptType} -> {auto isIO : NeedsIO t}
                -> IOFile -> Command sx [] LineByLine t
    ||| Delete file contents
    ||| which names depends on current file name - (path, name, extension)
    ClearFile : {0 t : FileScriptType} -> {auto isIO : NeedsIO t}
              -> IOFile -> Command sx [] LineByLine t
    |||Print the file name
    FileName : (holdSpace : String)
            -> {auto pos : (HoldSpace IOFile, holdSpace) `Elem` sx}
            -> Command sx [] LineByLine IO

  public export
  data CommandWithAddress : Variables
                          -> List Variable
                          -> FileScriptType
                          -> Type where
    (>)  : Command sx ys LineByLine t -> CommandWithAddress sx ys t
    (?>) : Address -> Command sx [] LineByLine t -> CommandWithAddress sx [] t

  ||| A file script is executed on each line of the file
  public export
  data FileScript : Variables -> FileScriptType -> Type where
    Nil : FileScript sx t
    (::) : CommandWithAddress sx ys t -> FileScript (sx <>< ys) t
        -> FileScript sx t

  public export
  data ScriptCommand : Variables -> List Variable
                    -> FileScriptType -> Type where
    ||| Line by line processing for files
    (*)   : List IOFile -> FileScript sx IO -> ScriptCommand sx [] IO -- IO
    ||| Line by line processing for stdin
    (|*>) : FileScript sx Std -> ScriptCommand sx [] IO -- IO
    ||| Line by line processing for in program data
    (*>)  : List String -> FileScript sx Local -> ScriptCommand sx [] t
    (|>)  : Command sx ys Total t -> ScriptCommand sx ys t

  namespace Script
    public export
    data Script : Variables -> FileScriptType -> Type where
      Nil : Script sx t
      (::) : ScriptCommand sx ys t -> Script (sx <>< ys) t -> Script sx t

  public export
  getScriptByType : ScriptType -> Variables -> FileScriptType -> Type
  getScriptByType Total = Script
  getScriptByType LineByLine = FileScript
