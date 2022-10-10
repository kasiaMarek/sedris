module Sedris.Thinnings

import Sedris.Lang
import Data.Void

%default total

export
extractNewVars : Command sx ys st io -> (vars : List Variable ** vars = ys)
extractNewVars (Replace x) = ([] ** Refl)
extractNewVars (Exec f) = ([] ** Refl)
extractNewVars Print = ([] ** Refl)
extractNewVars (CreateHold holdSpace {t} value)
  = ([(HoldSpace t, holdSpace)] ** Refl)
extractNewVars (HoldApp holdSpace f) = ([] ** Refl)
extractNewVars (FromHold holdSpace f) = ([] ** Refl)
extractNewVars (ExecOnHold holdSpace f) = ([] ** Refl)
extractNewVars (Routine {st} {io,io'} label sc) = ([(Label st io', label)] ** Refl)
extractNewVars (Call label) = ([] ** Refl)
extractNewVars (IfThenElse f x y) = ([] ** Refl)
extractNewVars (WithHoldContent holdSpace f) = ([] ** Refl)
extractNewVars Quit = ([] ** Refl)
extractNewVars Zap = ([] ** Refl)
extractNewVars ZapFstLine = ([] ** Refl)
extractNewVars ReadApp = ([] ** Refl)
extractNewVars Put = ([] ** Refl)
extractNewVars LineNumber = ([] ** Refl)
extractNewVars NewCycle = ([] ** Refl)
extractNewVars (ReadFrom x) = ([] ** Refl)
extractNewVars (QueueRead x) = ([] ** Refl)
extractNewVars PrintStd = ([] ** Refl)
extractNewVars (WriteTo f) = ([] ** Refl)
extractNewVars (WriteLineTo f) = ([] ** Refl)
extractNewVars (ClearFile f) = ([] ** Refl)
extractNewVars FileName = ([] ** Refl)

public export
data Thinning : Variables -> Variables -> Type where
  Lin : Thinning [<] sx
  (.Keep) : Thinning sx sy -> Thinning (sx :< y) (sy :< y)
  (.Drop) : Thinning sx sy -> Thinning  sx       (sy :< y)

0 uninhabited' : {sx, sy : Variables} -> {y : Variable}
              -> Thinning (sx ++ (sy :< y)) sx -> Void
uninhabited' {sx = _, sy = [<], y} tau.Keep = uninhabited' tau {sy = [<]}
uninhabited' {sx = _, sy = [<], y} (tau.Drop {sy = sy', y = y'}) = uninhabited' tau {sy = [< y'],y, sx = sy'}
uninhabited' {sx = _, sy = (sy :< x), y} (tau.Keep {sy = sy'}) =
  uninhabited'  (replace {p = (\e => Thinning (e :< x) sy')} 
                          (sym $ appendAssociative _ _ _)
                          tau)
                {sx = sy', sy = ([< y] ++ sy), y = x}
uninhabited' {sx = _, sy = (sy :< x), y} (tau.Drop {sy = sy', y = y'}) =
  uninhabited'  (replace {p = (\e => Thinning (e :< x :< y) sy')} 
                          (sym $ appendAssociative _ _ _)
                          tau)
                {sx = sy', sy = ([< y'] ++ sy) :< x}

export
Uninhabited (Thinning (sx :< x) sx) where
  uninhabited tau = absurdity (uninhabited' tau {sy = [<]})

export
id : (sx : Variables) -> Thinning sx sx
id [<] = [<]
id (sx :< x) = (id sx).Keep

export
(.) : Thinning sy sz -> Thinning sx sy -> Thinning sx sz
(.) tau [<]                     {sy = sy,        sz = sz,        sx = [<]      }
  = Lin
(.) tau.Keep tau'.Keep          {sy = (sy :< y), sz = (sy :< y), sx = (sx :< y)}
  = (tau . tau').Keep
(.) tau.Drop tau'.Keep          {sy = (sy :< y), sz = (sy :< y), sx = (sx :< y)}
  = (tau . (tau'.Drop)).Keep
(.) tau.Keep tau'.Drop          {sy = (sy :< y), sz = (sy :< y), sx = sx       }
  = (tau . tau').Drop
(.) tau.Drop tau'.Drop          {sy = (sy :< y), sz = (sy :< y), sx = sx       }
  = (tau . (tau'.Drop)).Drop

keepLast : (ys : List Variable)
            -> Thinning sx sx'
            -> Thinning (sx <>< ys) (sx' <>< ys)
keepLast [] tau = tau
keepLast (y :: ys) tau = keepLast ys tau.Keep

dropLast : (ys : List Variable) -> Thinning sx sy -> Thinning sx (sy <>< ys)
dropLast [] tau = tau
dropLast (y :: ys) tau = dropLast ys (tau.Drop)

-- id is neutral, (.) associative, i.e. a category whose objects are
-- Variables values and morphisms are thinnings

namespace Position
  export
  thin : x `Elem` sx -> Thinning sx sy -> x `Elem` sy
  thin _ [<] impossible
  thin Here (tau.Keep) = Here
  thin (There pos) (tau.Keep) = There (pos `thin` tau)
  thin pos (tau .Drop) = There (pos `thin` tau)

mutual
  namespace Cmd
    export
    thin : Command sx zs st io -> Thinning sx sy -> Command sy zs st io
    thin (Replace x) tau = Replace x
    thin (Exec f) tau = Exec f
    thin Print tau = Print
    thin (CreateHold hs x) tau = CreateHold hs x
    thin (HoldApp hs f {pos}) tau = HoldApp hs f {pos = pos `thin` tau}
    thin (FromHold hs f {pos}) tau = FromHold hs f {pos = pos `thin` tau}
    thin (ExecOnHold hs f {pos}) tau = ExecOnHold hs f {pos = pos `thin` tau}
    thin (Routine label r {st = Total} {io'}) tau = Routine label {io'} (r `thin` tau)
    thin (Routine label r {st = LineByLine} {io'}) tau = Routine label {io'} (r `thin` tau)
    thin (Call label {pos} {io'}) tau = Call {io'} label {pos = pos `thin` tau}
    thin (IfThenElse f sc1 sc2 {st = Total}) tau =
      IfThenElse f (sc1 `thin` tau) (sc2 `thin` tau)
    thin (IfThenElse f sc1 sc2 {st = LineByLine}) tau =
      IfThenElse f (sc1 `thin` tau) (sc2 `thin` tau)
    thin (WithHoldContent holdSpace f {pos = pos} {st = Total}) tau =
      WithHoldContent holdSpace (\v => (f v) `thin` tau) {pos = pos `thin` tau}
    thin (WithHoldContent holdSpace f {pos = pos} {st = LineByLine}) tau =
      WithHoldContent holdSpace (\v => (f v) `thin` tau) {pos = pos `thin` tau}
    thin Quit tau = Quit
    thin Zap tau = Zap
    thin ZapFstLine tau = ZapFstLine
    thin ReadApp tau = ReadApp
    thin Put tau = Put
    thin LineNumber tau = LineNumber
    thin NewCycle tau = NewCycle
    thin (ReadFrom fl) tau = ReadFrom fl
    thin (QueueRead fl) tau = QueueRead fl
    thin PrintStd tau = PrintStd
    thin (WriteTo fl) tau = WriteTo fl
    thin (WriteLineTo fl) tau = WriteLineTo fl
    thin (ClearFile fl) tau = ClearFile fl
    thin FileName tau = FileName

  namespace FileScript
    public export
    thin : FileScript xs io -> Thinning xs ys -> FileScript ys io
    thin [] tau = []
    thin ((> cmd) :: fsc) tau =
      let (ys' ** Refl) := extractNewVars cmd
      in ((> (cmd `thin` tau)) :: (fsc `thin` (keepLast ys' tau)))
    thin ((addr ?> cmd) :: fsc) tau
      = ((addr ?> (cmd `thin` tau)) :: (fsc `thin` tau))

  namespace Script
    public export
    thin : Script xs io -> Thinning xs ys -> Script ys io
    thin [] tau = []
    thin ((fl * fsc) :: cmds) tau
      = ((fl * (fsc `thin` tau)) :: (cmds `thin` tau))
    thin ((|*> fsc) :: cmds) tau
      = ((|*> (fsc `thin` tau)) :: (cmds `thin` tau))
    thin ((strs *> fsc) :: cmds) tau
      = ((strs *> (fsc `thin` tau)) :: (cmds `thin` tau))
    thin ((|> cmd) :: cmds) tau =
      let (ys' ** Refl) := extractNewVars cmd
      in ((|> (cmd `thin` tau)) :: (cmds `thin` (keepLast ys' tau)))

namespace Weaken
  public export
  data Weakening : Variables -> Variables -> Type where
    Weaken : (xs : List Variable) -> {auto 0 ford : sy = sx <>< xs}
          -> Weakening sx sy

  export
  weaken : {xs : Variables} -> Script xs io -> Weakening xs ys -> Script ys io
  weaken sc (Weaken ys {ford = Refl}) {xs} = thin sc (dropLast ys (id xs))

  export
  id : Weakening sx sx
  id = Weaken []

  export
  (.) : Weakening sy sz -> Weakening sx sy -> Weakening sx sz
  (Weaken xs {ford = Refl} ) . (Weaken ys {ford = Refl})
    = Weaken (ys ++ xs) {ford = fishConcat} where
      fishConcat : {sx : SnocList a} -> {ys, zs : List a}
           -> (sx <>< ys) <>< zs = sx <>< (ys ++ zs)
      fishConcat {sx = sx, zs = zs, ys = []} = Refl
      fishConcat {sx = sx, zs = zs, ys = (y :: ys)} = fishConcat

mutual
  liftCommand : Command sx ys st Local -> {io : FileScriptType}
              -> Command sx ys st io
  liftCommand (Replace r) = (Replace r)
  liftCommand (Exec f) = (Exec f)
  liftCommand Print = Print
  liftCommand (CreateHold hs v) = (CreateHold hs v)
  liftCommand (HoldApp hs f) = (HoldApp hs f)
  liftCommand (FromHold hs f) = (FromHold hs f)
  liftCommand (ExecOnHold hs f) = (ExecOnHold hs f)
  liftCommand (Routine l r {mol = Matches}) = Routine l r {io' = Local}
  liftCommand (Routine l r {mol = IsLocal}) = Routine l r {io' = Local}
  liftCommand (Call l {mol = Matches} {pos}) = Call l {pos} {io' = Local}
  liftCommand (Call l {mol = IsLocal} {pos}) = Call l {pos} {io' = Local}
  liftCommand (IfThenElse f sc1 sc2 {st = LineByLine})
    = IfThenElse f (liftFileScript sc1) (liftFileScript sc2)
  liftCommand (IfThenElse f sc1 sc2 {st = Total})
    = IfThenElse f (liftScript sc1) (liftScript sc2)
  liftCommand (WithHoldContent hs f) = (WithHoldContent hs f)
  liftCommand Quit = Quit
  liftCommand Zap = Zap
  liftCommand ZapFstLine = ZapFstLine
  liftCommand ReadApp = ReadApp
  liftCommand Put = Put
  liftCommand LineNumber = LineNumber
  liftCommand NewCycle = NewCycle
  liftCommand (ReadFrom f {isIO}) impossible
  liftCommand (QueueRead x {isIO}) impossible
  liftCommand (PrintStd {isIO}) impossible
  liftCommand (WriteTo f {isIO}) impossible
  liftCommand (WriteLineTo f {isIO}) impossible
  liftCommand (ClearFile f {isIO}) impossible
  liftCommand (FileName {isIO}) impossible
  
  export
  liftFileScript : FileScript sx Local -> {io : FileScriptType}
                -> FileScript sx io
  liftFileScript [] = []
  liftFileScript ((> cmd) :: fsc) = (> liftCommand cmd) :: liftFileScript fsc
  liftFileScript ((addr ?> cmd) :: fsc)
    =  (addr ?> liftCommand cmd) :: liftFileScript fsc

  export
  liftScript : Script sx Local -> {io : FileScriptType} -> Script sx io
  liftScript [] = []
  liftScript ((strs *> x) :: sc) = (strs *> x) :: liftScript sc
  liftScript ((|> cmd) :: sc) = (|> liftCommand cmd) :: liftScript sc

