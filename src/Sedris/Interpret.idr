module Sedris.Interpret

import public Sedris.Lang
import Sedris.Replace
import Sedris.Thinnings
import Sedris.VariableStore

import public Data.Regex
import public System.File
import Data.DPair
import Syntax.WithProof

infix 1 >>==

%hide TyRE.Text.Parser.Core.(>>=)

public export
IOEither : Type -> Type
IOEither a = PrimIO.IO (Either FileError a)

public export
defaultFile : IOFile
defaultFile = ""

public export
Result : FileScriptType -> Type
Result Local  = SnocList String
Result _      = IOEither (SnocList String)

public export
IOFilesStore : Type
IOFilesStore = (Either File LocalFile, IOFile, List (Either IOFile LocalFile))

public export
File' : FileScriptType -> Type
File' Local = LocalFile
File' _     = IOFilesStore

swap : Either a (IO  b) -> IO (Either a b)
swap (Left x) = pure (Left x)
swap (Right x) = map Right x

(>>==) : IOEither a -> (a -> IOEither b) -> IOEither b
(>>==) m f = do m' <- m
                (map join . swap) (map f m')

mapp : (a -> b) -> IOEither a -> IOEither b
mapp f m = m >>== (\e => pure $ Right $ f e)

record VMState (sx : Variables) where
  constructor MkVMState
  patternSpace : String
  resultSpace : SnocList String
  store : LinkedListStore sx

export
init : String -> VMState [<]
init str = MkVMState str [<] empty

lift : (LinkedListStore sx -> LinkedListStore sx')
    -> (VMState sx -> VMState sx')
lift f (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = f store }

put : String -> VMState sx -> VMState sx
put str (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = str
              , resultSpace
              , store }

dropNewLine : String -> String
dropNewLine str = fastPack $ go $ fastUnpack str where
  go : List Char -> List Char
  go [] = []
  go ['\n'] = []
  go (x::xs) = x :: (go xs)

deletePrefixLine : String -> String
deletePrefixLine str
  = case (lines str) of
      [] => ""
      (h :: tail) => unlines tail

getPrefixLine : String -> String
getPrefixLine str
  = case (lines str) of
    [] => ""
    (h :: tail) => h

namespace Scripts
  public export
  data Scripts : Variables -> FileScriptType -> Type where
    Just : Script sx io -> Scripts sx io
    Then : Script sx io -> {sy : Variables} -> Weakening sy sx
        -> Scripts sy io -> Scripts sx io

namespace FileScripts
  public export
  data FileScripts : Variables -> Variables -> FileScriptType -> Type where
    Just : FileScript sx io -> {sy : Variables} -> Weakening sy sx
        -> Scripts sy io -> FileScripts sx sy io
    Then : FileScript sx io -> {sy : Variables} -> Weakening sy sx
        -> FileScripts sy sy' io -> FileScripts sx sy' io

getScript : FileScripts sx sy io
          -> (sy' : Variables ** (sy' = sy, Weakening sy' sx, Scripts sy' io))
getScript (Just fsc tau sc) = (sy ** (Refl, tau, sc))
getScript (Then fsc tau fscs) =
  let (sy' ** (Refl, tau', sc)) := getScript fscs
  in (sy' ** (Refl, tau . tau', sc))

nextLineOfFile : Either File LocalFile
        -> IOEither (Maybe (String, Either File LocalFile))
nextLineOfFile (Left handle) =
  do end <- fEOF handle
     if end
      then map (\_ => Right Nothing) (closeFile handle)
      else mapp (\l => Just (l, Left handle)) (fGetLine handle)
nextLineOfFile (Right []) = pure $ Right Nothing
nextLineOfFile (Right (l :: lns)) = pure $ Right $ Just (l, Right lns)

nextFile : List (Either IOFile LocalFile)
        -> IOFile
        -> IOEither (Maybe (String, IOFilesStore))
nextFile [] fname = pure $ Right Nothing
nextFile (Left  file :: fl) fname =
  openFile file Read >>==
    (\handle =>
        do end <- fEOF handle
           if end
            then do closeFile handle
                    nextFile fl fname
            else mapp (\l => Just (l, (Left handle, file, fl))) (fGetLine handle))
nextFile (Right [] :: fl) fname = nextFile fl fname
nextFile (Right (l :: lns)  :: fl) fname
  = pure $ Right $ Just (l, (Right lns, fname, fl))

nextLine : IOFilesStore -> IOEither (Maybe (String, IOFilesStore))
nextLine (h, fname, rest) =
  nextLineOfFile h >>==
    (\case
      Nothing => nextFile rest fname
      Just (l, curr) => pure $ Right $ Just (l, (curr, fname, rest)))

isLastLine : IOFilesStore -> IOEither Bool
isLastLine (curr, _, rest)
  = foldr (\case
            (Right lns) => mapp (&& isNil lns)
            (Left f) => (\acc =>
              openFile f Read >>==
                (\file =>
                  do end <- fEOF file {io = IO}
                     closeFile file
                     mapp (&& end) acc)))
          isLastForCurr rest where
  isLastForCurr : IOEither Bool
  isLastForCurr =
    case curr of
      Right lns => pure $ Right $ isNil lns
      Left f => map Right (fEOF f)

record LineInfo where
  constructor MkLineInfo
  line : String
  lineNumber : Nat
  isLastLine : Bool

from : LineInfo -> String -> List String -> LineInfo
from (MkLineInfo _ lineNumber _) name []
  = MkLineInfo name (S lineNumber) True
from (MkLineInfo _ lineNumber _) name (x :: xs)
  = MkLineInfo name (S lineNumber) False

from' : LineInfo -> String -> IOFilesStore -> IOEither LineInfo
from' (MkLineInfo _ lineNumber _) str fs =
  mapp (MkLineInfo str (S lineNumber)) (isLastLine fs)

initLI : LineInfo
initLI = MkLineInfo "" 0 False

close : Either File LocalFile -> IO ()
close (Left handle) = closeFile handle
close (Right _)     = pure ()

addrCheck : Address -> LineInfo -> Bool
addrCheck (Line n)         (MkLineInfo _ lineNum _)  = (n == lineNum)
addrCheck (Lines ns)       (MkLineInfo _ lineNum _)  = isJust $ find (== lineNum) ns
addrCheck (LineRange s l)  (MkLineInfo _ lineNum _)  = lineNum >= s && lineNum <= l
addrCheck (RegexWhole re)  (MkLineInfo line _ _)     = match re line
addrCheck (RegexPrefix re) (MkLineInfo line _ _)     = isJust $ fst $ parsePrefix re line True
addrCheck (RegexExists re) (MkLineInfo line _ _)     =
  case asDisjointMatches re line True of
    (Suffix _)   => False
    (Cons _ _ _) => True
addrCheck (Not addr)       li                        = not (addrCheck addr li)
addrCheck LastLine         (MkLineInfo _ _ lastLine) = lastLine

data SimpleCommand : Command sx ys st io -> Type where
    IsReplace : SimpleCommand (Replace t)
    IsExec : SimpleCommand (Exec f)
    IsPrint : SimpleCommand (Print)
    IsCreateHold : SimpleCommand (CreateHold name v)
    IsHoldApp : SimpleCommand (HoldApp name {pos} f)
    IsFromHold : SimpleCommand (FromHold name f {pos})
    IsExecOnHold : SimpleCommand (ExecOnHold name f {pos})
    IsRoutine : SimpleCommand (Routine name routine {mol} {io'})
    IsZap : SimpleCommand (Zap)
    IsZapFstLine : SimpleCommand (ZapFstLine)

isSimpleCommand : (cmd : Command sx ys st io)
                -> Either (SimpleCommand cmd) (Not $ SimpleCommand cmd)
isSimpleCommand (Replace x) = Left IsReplace
isSimpleCommand (Exec f) = Left IsExec
isSimpleCommand Print = Left IsPrint
isSimpleCommand (CreateHold holdSpace x) = Left IsCreateHold
isSimpleCommand (HoldApp holdSpace f) = Left IsHoldApp
isSimpleCommand (FromHold holdSpace f) = Left IsFromHold
isSimpleCommand (ExecOnHold holdSpace f) = Left IsExecOnHold
isSimpleCommand (Routine label x) = Left IsRoutine
isSimpleCommand (Call label) = Right (\case _ impossible)
isSimpleCommand (IfThenElse f x y) = Right (\case _ impossible)
isSimpleCommand (WithHoldContent holdSpace f) = Right (\case _ impossible)
isSimpleCommand Quit = Right (\case _ impossible)
isSimpleCommand Zap = Left IsZap
isSimpleCommand ZapFstLine = Left IsZapFstLine
isSimpleCommand ReadApp = Right (\case _ impossible)
isSimpleCommand Put = Right (\case _ impossible)
isSimpleCommand LineNumber = Right (\case _ impossible)
isSimpleCommand NewCycle = Right (\case _ impossible)
isSimpleCommand (ReadFrom x) = Right (\case _ impossible)
isSimpleCommand (QueueRead x) = Right (\case _ impossible)
isSimpleCommand PrintStd = Right (\case _ impossible)
isSimpleCommand (WriteTo f) = Right (\case _ impossible)
isSimpleCommand (WriteLineTo f) = Right (\case _ impossible)
isSimpleCommand (ClearFile f) = Right (\case _ impossible)
isSimpleCommand (FileName hs) = Right (\case _ impossible)

execSimpleCommand : (cmd : Command sx ys st io) -> VMState sx
                  -> {auto 0 prf : SimpleCommand cmd}
                  -> VMState (sx <>< ys)
execSimpleCommand (Replace replace) {prf = IsReplace}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = performReplace patternSpace replace
              , resultSpace
              , store }
execSimpleCommand (Exec f) {prf = IsExec}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = f patternSpace
              , resultSpace
              , store }
execSimpleCommand Print {prf = IsPrint}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = ""
              , resultSpace = resultSpace :< patternSpace
              , store }
execSimpleCommand (CreateHold hs initVal) {prf = IsCreateHold}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = holdSpace hs initVal store }
execSimpleCommand (HoldApp name f {pos}) {prf = IsHoldApp}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = execOnHoldSpace pos store (\v => f v patternSpace) }
execSimpleCommand (FromHold name f {pos}) {prf = IsFromHold}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = f patternSpace (getHoldSpace pos store)
              , resultSpace
              , store }
execSimpleCommand (ExecOnHold name f {pos}) {prf = IsExecOnHold}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = execOnHoldSpace pos store f }
execSimpleCommand (Routine name routine {st}) {prf = IsRoutine}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = label name routine store}
execSimpleCommand Zap {prf = IsZap}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = ""
              , resultSpace
              , store }
execSimpleCommand ZapFstLine {prf = IsZapFstLine}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = deletePrefixLine patternSpace
              , resultSpace
              , store }

mutual
  newCycle : {io : FileScriptType}
          -> (curr : FileScripts sx sy io)
          -> (full : FileScript sy io)
          -> File' io
          -> VMState sx
          -> LineInfo
          -> Result io
  newCycle curr full store vm li with (getScript curr)
    newCycle curr full store vm li | (_ ** (Refl, tau, sc)) =
      case io of
        Local =>
          case store of
            []       => interpretS sc (lift (\s => weaken s tau) vm)
            l :: lns => interpretFS (Just full id sc) full lns
                                    (put l (lift (\s => weaken s tau) vm))
                                    (from li l lns)
        IO   => continue
        Std  => continue where
      continue : {auto 0 prf1 : File' io = IOFilesStore}
              -> {auto 0 prf2 : Result io = IOEither (SnocList String)}
              -> Result io
      continue = rewrite prf2 in
        nextLine (rewrite (sym prf1) in store) >>==
          (\case
            Nothing =>
              rewrite (sym prf2) in
              interpretS sc (lift (\s => weaken s tau) vm)
            Just (l, store) =>
              let l' = dropNewLine l
              in (from' li l' store >>==
                 rewrite (sym prf2) in
                 (interpretFS (Just full id sc) full
                              (rewrite prf1 in store)
                              (put l' (lift (\s => weaken s tau) vm)))))

  export
  interpretFSCmd : {sx : Variables}
                -> {ys : List Variable}
                -> {0 sy : Variables}
                -> {io : FileScriptType}
                -> (cmd : Command sx ys LineByLine io)
                -> (curr : FileScripts (sx <>< ys) sy io)
                -> (full : FileScript sy io)
                -> File' io
                -> VMState sx
                -> LineInfo
                -> Result io
  interpretFSCmd cmd curr full lines vm li {io} with (isSimpleCommand cmd)
    interpretFSCmd cmd curr full lines vm li | Left prf =
      interpretFS curr full lines (execSimpleCommand cmd vm) li
    interpretFSCmd (Replace _)      _ _ _ _ _ | Right f = absurd (f IsReplace)
    interpretFSCmd (Exec _)         _ _ _ _ _ | Right f = absurd (f IsExec)
    interpretFSCmd Print            _ _ _ _ _ | Right f = absurd (f IsPrint)
    interpretFSCmd (CreateHold _ _) _ _ _ _ _ | Right f = absurd (f IsCreateHold)
    interpretFSCmd (HoldApp _ _)    _ _ _ _ _ | Right f = absurd (f IsHoldApp)
    interpretFSCmd (FromHold _ _)   _ _ _ _ _ | Right f = absurd (f IsFromHold)
    interpretFSCmd (ExecOnHold _ _) _ _ _ _ _ | Right f = absurd (f IsExecOnHold)
    interpretFSCmd (Routine _ _)    _ _ _ _ _ | Right f = absurd (f IsRoutine)
    interpretFSCmd Zap              _ _ _ _ _ | Right f = absurd (f IsZap)
    interpretFSCmd ZapFstLine       _ _ _ _ _ | Right f = absurd (f IsZapFstLine)
    interpretFSCmd Quit curr full lines vm li {io = Local}  | _ = vm.resultSpace
    interpretFSCmd Quit curr full (h, y) vm li {io = IO}    | _ =
      map (\_ => Right $ vm.resultSpace) (close h)
    interpretFSCmd Quit curr full (h, y) vm li {io = Std}   | _ =
      map (\_ => Right $ vm.resultSpace) (close h)
    interpretFSCmd (IfThenElse f sc1 sc2) curr full lines vm li | _ =
      if f vm.patternSpace
      then interpretFS (Then sc1 id curr) full lines vm li
      else interpretFS (Then sc2 id curr) full lines vm li
    interpretFSCmd (Call _ {pos} {mol}) curr full lines vm li | _ =
      let r := getRoutine sx pos vm.store
      in case mol of
          Matches     => interpretFS (Then r id curr) full lines vm li
          AreLocalStd => interpretFS (Then (liftFileScript r) id curr)
                                     full lines vm li
          AreLocalIO  => interpretFS (Then (liftFileScript r) id curr)
                                     full lines vm li
          AreStdIO    => interpretFS (Then (liftFileScriptStd r) id curr)
                                     full lines vm li
    interpretFSCmd (WithHoldContent _ f {pos}) curr full lines vm li | _
      = interpretFS
          (Then (f $ getHoldSpace pos vm.store) id curr)
          full lines vm li
    interpretFSCmd ReadApp curr full store vm li | _ =
      case io of
        Local =>
          case store of
            [] =>
              let (sy ** (Refl, tau, sc)) = getScript curr
              in interpretS sc (lift (\s => weaken s tau) vm)
            (l :: ln) =>
                  interpretFS curr full ln
                  (put (l ++ "\n" ++ vm.patternSpace) vm)
                  (from li l ln)
        IO => continue
        Std => continue where
      continue : {auto 0 prf1 : File' io = IOFilesStore}
              -> {auto 0 prf2 : Result io = IOEither (SnocList String)}
              -> Result io
      continue = rewrite prf2 in
        nextLine (rewrite (sym prf1) in store) >>==
          (\case
            Nothing =>
              rewrite (sym prf2) in
              let (sy ** (Refl, tau, sc)) = getScript curr
              in interpretS sc (lift (\s => weaken s tau) vm)
            Just (l, store) =>
              from' li l store >>==
              rewrite (sym prf2) in
              interpretFS curr full (rewrite prf1 in store)
                          (put (l ++ "\n" ++ vm.patternSpace) vm))
    interpretFSCmd Put curr full store vm li | _ =
      case io of
        Local =>
          case store of
            [] =>
              let (sy ** (Refl, tau, sc)) = getScript curr
              in interpretS sc (lift (\s => weaken s tau) vm)
            (l :: ln) => interpretFS curr full ln (put l vm) (from li l ln)
        IO => continue
        Std => continue where
      continue : {auto 0 prf1 : File' io = IOFilesStore}
              -> {auto 0 prf2 : Result io = IOEither (SnocList String)}
              -> Result io
      continue = rewrite prf2 in
        nextLine (rewrite (sym prf1) in store) >>==
          (\case
            Nothing =>
              rewrite (sym prf2) in
              let (sy ** (Refl, tau, sc)) = getScript curr
              in interpretS sc (lift (\s => weaken s tau) vm)
            Just (l, store) =>
              from' li l store >>==
              rewrite (sym prf2) in
              interpretFS curr full (rewrite prf1 in store) (put l vm))
    interpretFSCmd LineNumber curr full lines vm
                   li@(MkLineInfo _ lineNum _) | _ =
      interpretFS curr full lines
                  (put (show lineNum) vm) li
    interpretFSCmd NewCycle curr full ln vm li {io} | _
      = newCycle curr full ln vm li
    interpretFSCmd (ReadFrom lns) curr full lines vm li {io = Local} | _
      = interpretFS curr full lns vm li
    interpretFSCmd (ReadFrom fl') curr full (fl, flname, rest) vm li {io = IO} | _
      = case fl' of
        Left file => (do close fl
                         openFile file Read) >>==
            (\f => do res <- interpretFS curr full (Left f, file, rest) vm li
                      map (\_ => res) (closeFile f))
        Right lns => interpretFS curr full (Right lns, flname, rest) vm li
    interpretFSCmd (ReadFrom fl') curr full (fl, flname, rest) vm li {io = Std} | _
      = case fl' of
        Left file => (do close fl
                         openFile file Read) >>==
            (\f => do res <- interpretFS curr full (Left f, file, rest) vm li
                      map (\_ => res) (closeFile f))
        Right lns => interpretFS curr full (Right lns, flname, rest) vm li
    interpretFSCmd (QueueRead lns) curr full lines vm li {io = Local} | _
      = interpretFS curr full (lines ++ lns) vm li
    interpretFSCmd (QueueRead lns) curr full (fl, flname, rest) vm li {io = IO} | _
      = interpretFS curr full (fl, flname, rest ++ [lns]) vm li
    interpretFSCmd (QueueRead lns) curr full (fl, flname, rest) vm li {io = Std} | _
      = interpretFS curr full (fl, flname, rest ++ [lns]) vm li
    interpretFSCmd (PrintStd {isIO}) curr full lines vm li | _ =
      case io of
        Std =>  map Right (putStrLn vm.patternSpace) >>==
                (\_ => interpretFS curr full lines vm li)
        IO  =>  map Right (putStrLn vm.patternSpace) >>==
                (\_ => interpretFS curr full lines vm li)
    interpretFSCmd (WriteTo f {isIO}) curr full store vm li | _
      = case io of
          Local => case isIO of _ impossible
          IO =>
            ((openFile f Append) >>==
            (\h => do res <- fPutStrLn h vm.patternSpace
                      map (\_ => res) (closeFile h))) >>==
            (\_ => interpretFS curr full store vm li)
          Std =>
            ((openFile f Append) >>==
            (\h => do res <- fPutStrLn h vm.patternSpace
                      map (\_ => res) (closeFile h))) >>==
            (\_ => interpretFS curr full store vm li)
    interpretFSCmd (WriteLineTo f {isIO}) curr full store vm li | _
      = case io of
          Local => case isIO of _ impossible
          IO =>
            ((openFile f Append) >>==
            (\h => do res <- fPutStrLn h (getPrefixLine vm.patternSpace)
                      map (\_ => res) (closeFile h))) >>==
            (\_ => interpretFS curr full store vm li)
          Std =>
            ((openFile f Append) >>==
            (\h => do res <- fPutStrLn h (getPrefixLine vm.patternSpace)
                      map (\_ => res) (closeFile h))) >>==
            (\_ => interpretFS curr full store vm li)
    interpretFSCmd (ClearFile f {isIO}) curr full store vm li | _ =
      case io of
        Local => case isIO of _ impossible
        IO  => ((openFile f WriteTruncate) >>==
               (\h => do res <- fPutStr h ""
                         map (\_ => res) (closeFile h))) >>==
               (\_ => interpretFS curr full store vm li)
        Std => ((openFile f WriteTruncate) >>==
               (\h => do res <- fPutStr h ""
                         map (\_ => res) (closeFile h))) >>==
               (\_ => interpretFS curr full store vm li)
    interpretFSCmd (FileName hs {pos}) curr full store vm li {io = IO} | _ =
      let (_, fname, _) := store
          vm' : VMState sx
          vm' = execSimpleCommand {io = IO} {st = LineByLine} {prf = IsExecOnHold}
                                  (ExecOnHold hs (\_ => fname) {pos}) vm
      in interpretFS curr full store vm' li

  interpretFS :  {sx : Variables}
              -> {io : FileScriptType}
              -> (curr : FileScripts sx sy io)
              -> (full : FileScript sy io)
              -> File' io
              -> VMState sx
              -> LineInfo
              -> Result io
  interpretFS (Just [] tau sc) full ln vm li
    = newCycle (Just [] tau sc) full ln vm li
  interpretFS (Just ((> cmd) :: fsc') tau sc)
                          full strs vm li with (extractNewVars cmd)
    interpretFS (Just ((> cmd) :: fsc') tau sc)
                            full strs vm li | (ys ** Refl)
      = interpretFSCmd
          cmd (Just fsc' (Weaken ys . tau) sc) full strs vm li
  interpretFS (Just ((addr ?> cmd) :: fsc') tau sc)
                          full strs vm li
    = if (addrCheck addr li)
      then interpretFSCmd
            cmd (Just fsc' tau sc) full strs vm li
      else interpretFS
            (Just fsc' tau sc) full strs vm li
  interpretFS (Then [] tau' fsc {sy = sy'}) full lines vm li
    = interpretFS fsc full lines (lift (\s => weaken s tau') vm) li
  interpretFS (Then ((> cmd) :: fsc') tau' fsc)
                          full strs vm li with (extractNewVars cmd)
    interpretFS (Then ((> cmd) :: fsc') tau' fsc)
                            full strs vm li | (ys ** Refl)
      = interpretFSCmd
          cmd (Then fsc' (Weaken ys . tau') fsc)
          full strs vm li
  interpretFS (Then ((addr ?> cmd) :: fsc') tau' fsc)
                          full strs vm li
    = if (addrCheck addr li)
      then interpretFSCmd
            cmd (Then fsc' tau' fsc) full strs vm li
      else interpretFS (Then fsc' tau' fsc) full strs vm li

  export
  interpretCmd : {sx : Variables}
              -> {ys : List Variable}
              -> {io : FileScriptType}
              -> (cmd : Command sx ys Total io)
              -> (sc : Scripts (sx <>< ys) io)
              -> VMState sx
              -> Result io
  interpretCmd cmd sc vm {sx} with (isSimpleCommand cmd)
    interpretCmd cmd sc vm | (Left prf)
      = interpretS sc (execSimpleCommand cmd vm)
    interpretCmd (Replace x) sc vm    | (Right f) = absurd (f IsReplace)
    interpretCmd (Exec _) _ _         | (Right f) = absurd (f IsExec)
    interpretCmd Print _ _            | (Right f) = absurd (f IsPrint)
    interpretCmd (CreateHold _ _) _ _ | (Right f) = absurd (f IsCreateHold)
    interpretCmd (Routine _ _) _ _    | (Right f) = absurd (f IsRoutine)
    interpretCmd (HoldApp _ _) _ _    | (Right f) = absurd (f IsHoldApp)
    interpretCmd (FromHold _ _) _ _   | (Right f) = absurd (f IsFromHold)
    interpretCmd (ExecOnHold _ _) _ _ | (Right f) = absurd (f IsExecOnHold)
    interpretCmd Quit _ vm | _ =
      case io of
        Local => vm.resultSpace
        IO => pure $ Right vm.resultSpace
        Std => pure $ Right vm.resultSpace
    interpretCmd (IfThenElse f sc1 sc2) sc vm {sx} | _
      = if (f vm.patternSpace)
        then interpretS (Then sc1 id sc) vm
        else interpretS (Then sc2 id sc) vm
    interpretCmd (Call _ {pos} {mol = Matches}) sc vm {sx} | _
      = let r := getRoutine sx pos vm.store
        in interpretS (Then r id sc) vm
    interpretCmd (Call _ {pos} {mol = AreLocalStd}) sc vm {sx} | _
      = let r := getRoutine sx pos vm.store
        in interpretS (Then (liftScript r) id sc) vm
    interpretCmd (Call _ {pos} {mol = AreLocalIO}) sc vm {sx} | _
      = let r := getRoutine sx pos vm.store
        in interpretS (Then (liftScript r) id sc) vm
    interpretCmd (Call _ {pos} {mol = AreStdIO}) sc vm {sx} | _
      = let r := getRoutine sx pos vm.store
        in interpretS (Then (liftScriptStd r) id sc) vm
    interpretCmd (WithHoldContent _ f {pos}) sc vm {sx} | _
    = interpretS (Then (f $ getHoldSpace pos vm.store) id sc) vm
    interpretCmd (PrintStd {isIO}) sc vm | _ =
      case io of
        Std =>  map Right (putStrLn vm.patternSpace) >>==
                (\_ => interpretS sc vm)
        IO  =>  map Right (putStrLn vm.patternSpace) >>==
                (\_ => interpretS sc vm)

  export
  interpretS : {sx : Variables} -> {io : FileScriptType} -> (sc : Scripts sx io)
            -> VMState sx -> Result io
  interpretS (Just []) vm {io} =
    case io of
      Local => vm.resultSpace
      IO    => pure $ Right vm.resultSpace
      Std   => pure $ Right vm.resultSpace
  interpretS {sx} (Just ((ln *> fsc) :: sc)) vm
    = case io of
        Local => interpretFS (Just [] id (Just sc)) fsc ln vm initLI
        IO    => interpretFS (Just [] id (Just sc)) (liftFileScript fsc)
                             (Right ln, defaultFile, []) vm initLI
        Std   => interpretFS (Just [] id (Just sc)) (liftFileScript fsc)
                             (Right ln, defaultFile, []) vm initLI
  interpretS (Just ((|> cmd) :: sc)) vm {sx} with (extractNewVars cmd)
    interpretS (Just ((|> cmd) :: sc)) vm {sx} | (ys ** Refl)
      = interpretCmd cmd (Just sc) vm
  interpretS (Then [] tau scCont) vm
    = interpretS scCont (lift (\s => weaken s tau) vm)
  interpretS {sx} (Then ((ln *> fsc) :: sc) tau scCont) vm
    = case io of
        Local => interpretFS (Just [] id (Then sc tau scCont)) fsc ln vm initLI
        IO    => interpretFS  (Just [] id (Then sc tau scCont))
                              (liftFileScript fsc) (Right ln, defaultFile, [])
                              vm initLI
        Std   => interpretFS  (Just [] id (Then sc tau scCont))
                              (liftFileScript fsc) (Right ln, defaultFile, [])
                              vm initLI
  interpretS (Then ((|> cmd) :: sc) tau scCont) vm {sx} with (extractNewVars cmd)
    interpretS (Then ((|> cmd) :: sc) tau scCont) vm {sx} | (ys ** Refl)
      = interpretCmd cmd (Then sc (Weaken ys . tau) scCont) vm
  interpretS (Just ((fls * fsc) :: sc)) vm
    = case fls of
        [] => interpretS (Just sc) vm
        (f :: fls) =>
          openFile f Read {io = IO}
          >>== (\h => interpretFS (Just [] id (Just sc)) fsc
                                  (Left h, f, map Left fls) vm initLI)
  interpretS (Just ((|*> fsc) :: sc)) vm =
    interpretFS (Just [] id (Just sc))
                (liftFileScriptStd fsc)
                (Left stdin, defaultFile, []) vm initLI
  interpretS (Then ((fls * fsc) :: sc) tau sc') vm
    = case fls of
        [] => interpretS (Just sc) vm
        (f :: fls) =>
          openFile f Read {io = IO}
          >>== (\h => interpretFS (Just [] id (Then sc tau sc'))
                                  fsc (Left h, f, map Left fls) vm initLI)
  interpretS (Then ((|*> fsc) :: sc) tau sc') vm
    = interpretFS (Just [] id (Then sc tau sc'))
                  (liftFileScriptStd fsc)
                  (Left stdin, defaultFile, []) vm initLI
