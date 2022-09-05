module Sedris.Lang

import public Data.Regex
import public Data.SnocList
import public Data.SnocList.Elem

prefix  1 >
infix   1 ?>

public export
withOut : (xs : SnocList a) -> (x `Elem` xs) -> SnocList a
withOut (sx :< _) Here = sx
withOut (sx :< x) (There pos) = (withOut sx pos) :< x

public export
data VarType
  = HoldSpace Type
  | Label

-- public export
-- record State (sx : SnocList (VarType, String)) where
--   constructor MkState
--   patternSpace : String
--   holdSpaces
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
  All : String -> String -> ReplaceCommand
  AllMulti : List (String, String) -> ReplaceCommand
  Prefix : String -> String -> ReplaceCommand
  AllRe : (TyRE a) -> (a -> String) -> ReplaceCommand
  PrefixRe : (TyRE a) -> (a -> String) -> ReplaceCommand
  CharSubst : (xs : List Char) -> (Vect (length xs) Char) -> ReplaceCommand

mutual
  public export
  data Command : SnocList (VarType, String)
              -> List (VarType, String) -- local variables
              -> List (VarType, String) -- global variables
              -> Type where
--- pattern space operation commands
    ||| Replace command
    Replace : ReplaceCommand -> Command sx [] []
    |||Execute function on the pattern space
    Exec : (String -> String) -> Command sx [] []
    |||Delete the contents of the pattern space and start a new cycle
    Zap : Command sx [] []
    |||Delete the contents of the pattern space up to the `\n`
    |||and start the new cycle without reading the next line.
    |||If no `\n` in the pattern space treat as `Zap`.
    ZapFstLine : Command sx [] []
--- read/write commands ---
    |||Print contenst of the pattern space
    Print : Command sx [] []
    |||Append a newline and the next line from input to the pattern space
    ReadApp : Command sx [] []
    |||Read the next line into the pattern space (deleting what was previously stored)
    Put : Command sx [] []
    |||Write contents of the pattern space to a file
    Write : String -> Command sx [] []
    |||Write contents of the pattern space up to `\n` to a file
    WriteToN : String -> Command sx [] []
--- commands for hold spaces ---
    |||Copy contents of pattern space to a named hold space (global)
    HoldGlobal : (holdSpace : String)
              -> {t : Type} -> (String -> t)
              -> Command sx [] [(HoldSpace t, holdSpace)]
    |||Copy contents of pattern space to a named hold space (local)
    Hold  : (holdSpace : String)
          -> {t : Type} -> (String -> t)
          -> Command sx [(HoldSpace t, holdSpace)] []
    |||Append a newline and contents of pattern space to a named hold space
    HoldApp : (holdSpace : String)
            -> {t : Type} -> (t -> String -> t)
            -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
            -> Command sx [] []
    |||Copy contents of a named hold space to pattern space
    FromHold  : (holdSpace : String)
              -> {t : Type} -> (String -> t -> String)
              -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
              -> Command sx [] []
    |||Execute a function on a hold space contents
    ExecOnHold : (holdSpace : String)
              -> {t : Type} -> (t -> t)
              -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
              -> Command sx [] []
--- flow control commands ---
    ||| Create a routine
    ||| For simplicity global definitions are not allowed in routines
    Routine : (label : String) -> SubScript sx [] -> Command sx [(Label, label)] []
    ||| Go to routine with named `label`
    Call : (label : String) -> {auto pos : (Label, label) `Elem` sx}
              -> Command sx [] []
    ||| If then else contruction
    IfThenElse : (String -> Bool) -> SubScript sx ys -> SubScript sx ys
              -> Command sx [] ys
    ||| Allows for executing code with value from a chosen holdspace.
    ||| This holdspace does not exist inside that scope.
    ||| For simplicity global definitions are not allowed in routines.
    WithHoldContent : (holdSpace : String)
                    -> {t : Type}
                    -> {auto pos : (HoldSpace t, holdSpace) `Elem` sx}
                    -> (t -> SubScript (withOut sx pos) [])
                    -> Command sx [] []
--- file control commands ---
    |||Start reading from a new file
    ReadFrom : String -> Command sx [] [] --r
    |||Queue next file to read
    QueueRead : String -> Command sx [] [] -- R
--- other ---
    |||Print the line number
    LineNumber : Command sx [] [] -- =
    |||Print the file name
    FileName : Command sx [] []
    |||Quit
    Quit : Command sx [] [] -- q;Q
    -- |||Start new cycle
    -- NewCycle : Command sx []
    
    -- Group -- { cmd ; cmd ... }

  public export
  data CommandWithAddress : SnocList (VarType, String)
                          -> List (VarType, String)
                          -> List (VarType, String)
                          -> Type where
    (>)  : Command sx ys zs -> CommandWithAddress sx ys zs
    (?>) : Address -> Command sx ys zs -> CommandWithAddress sx ys zs

  ||| The source is processed line by line.
  ||| A line is read in and the whole subscript is executed.
  ||| (Note that in contrast to GNU sed we don't print anything by default)
  public export
  data SubScript : SnocList (VarType, String) -> List (VarType, String) -> Type where
    Nil : SubScript sx []
    (::) : CommandWithAddress sx ys zs -> SubScript (sx <>< ys <>< zs) ys' -> SubScript sx (zs ++ ys')

||| If no input files are given the input in taken from std input.
||| If multiple files are given as the source they are concatenated into one big source.
public export
data SubScriptWithFiles : SnocList (VarType, String) -> List (VarType, String) -> Type where
  (*) : (List String) -> SubScript sx ys -> SubScriptWithFiles sx ys

||| Having multiple subsctipts that operate on multiple files allows to
||| share global hold spaces.
public export
data Script : SnocList (VarType, String) -> Type where
  End : Script sx
  (++) : SubScriptWithFiles sx ys -> Script (sx <>< ys) -> Script sx