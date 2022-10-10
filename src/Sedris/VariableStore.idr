module Sedris.VariableStore

import Sedris.Lang
import Sedris.Thinnings

%default total

public export
interface VariableStore (Store : Variables -> Type) where
  --- adding variables
  holdSpace : (name : String) -> {t : Type} -> (value : t) -> Store sx
            -> Store (sx :< (HoldSpace t, name))
  label : (name : String) -> {st : ScriptType} -> {io : FileScriptType}
        -> (getScriptByType st sx io)
        -> Store sx -> Store (sx :< (Label st io, name))
  --- getting variables
  getHoldSpace : {0 name : String} -> {0 t : Type} -> {0 sx : Variables}
              -> (pos : (HoldSpace t, name) `Elem` sx)
              -> Store sx -> t
  getRoutine : {0 name : String}
            -> (sx : Variables)
            -> {st : ScriptType}
            -> {io : FileScriptType}
            -> (pos : (Label st io, name) `Elem` sx)
            -> Store sx
            -> getScriptByType st sx io
  --- variable mutation
  execOnHoldSpace : {0 name : String} -> {0 t : Type}
                  -> {0 sx : Variables} -> (pos : (HoldSpace t, name) `Elem` sx)
                  -> Store sx -> (t -> t)
                  -> Store sx
  --- thinning
  weaken : Store sy -> Weakening sx sy -> Store sx
  --- empty store
  empty : Store [<]

namespace LinkedListStore
  public export
  data LinkedListStore : Variables -> Type where
    Empty : LinkedListStore [<]
    HS : (name : String) -> {t : Type} -> (value : t) -> LinkedListStore sx
      -> LinkedListStore (sx :< (HoldSpace t, name))
    LB : (name : String) -> {st : ScriptType} -> {io : FileScriptType}
      -> (getScriptByType st sx io)
      -> LinkedListStore sx
      -> LinkedListStore (sx :< (Label st io, name))
  
  getHoldSpace : {0 name : String} -> {0 t : Type}
              -> {0 xs : SnocList (VarType, String)}
              -> (pos : (HoldSpace t, name) `Elem` xs)
              -> LinkedListStore xs
              -> t
  getHoldSpace Here (HS _ value _) = value
  getHoldSpace (There pos) (HS str value tail) = getHoldSpace pos tail
  getHoldSpace (There pos) (LB str sc tail) = getHoldSpace pos tail

  getRoutineAux : {0 name : String}
                -> (sx : Variables)
                -> {st : ScriptType}
                -> {io : FileScriptType}
                -> (pos : (Label st io, name) `Elem` sx)
                -> LinkedListStore sx
                -> Exists (\sy => (getScriptByType st sy io, Thinning sy sx))
  getRoutineAux (sx :< (Label st io, name))   Here (LB name sc store)
    = Evidence sx (sc, (id sx).Drop)
  getRoutineAux (sx :< (HoldSpace t, str)) (There pos) (HS str value store)
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in Evidence sy (sc, tau.Drop)
  getRoutineAux (sx :< (Label st io, str))    (There pos) (LB str x store)
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in Evidence sy (sc, tau.Drop)

  getRoutine : {0 name : String}
            -> (sx : Variables)
            -> {st : ScriptType}
            -> {io : FileScriptType}
            -> (pos : (Label st io, name) `Elem` sx)
            -> LinkedListStore sx
            -> getScriptByType st sx io
  getRoutine sx pos store {st}
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in case st of
          Total => thin sc tau
          LineByLine => thin sc tau

  execOnHoldSpace : {0 name : String} -> {0 t : Type}
                  -> {0 xs : SnocList (VarType, String)}
                  -> (pos : (HoldSpace t, name) `Elem` xs)
                  -> LinkedListStore xs
                  -> (t -> t)
                  -> LinkedListStore xs
  execOnHoldSpace Here (HS name value hs) f = HS name (f value) hs
  execOnHoldSpace (There pos) (HS str value hs) f
    = HS str value (execOnHoldSpace pos hs f)
  execOnHoldSpace (There pos) (LB str name hs) f
    = LB str name (execOnHoldSpace pos hs f)

  weaken : LinkedListStore sy -> Weakening sx sy -> LinkedListStore sx
  weaken store (Weaken ys {ford = Refl})
    = weaken' (cast ys) (replace  {p = (LinkedListStore)}
                                  prf
                                  store) where
      prf : {sx, sy : SnocList a} -> {ys : List a}
          -> ((sx ++ sy) <>< ys = sx ++ (sy <>< ys))
      prf {sx, sy, ys = []} = Refl
      prf {sx, sy, ys = (y :: ys)} = prf {sx, sy = sy :< y, ys}
      weaken' : (sy : Variables) -> LinkedListStore (sx ++ sy)
              -> LinkedListStore sx
      weaken' [<] store = store
      weaken' (sy :< (HoldSpace _, _))  (HS _ _ store) = weaken' sy store
      weaken' (sy :< (Label _ _, _))      (LB _ _ store) = weaken' sy store

  public export
  VariableStore LinkedListStore where
    getHoldSpace = LinkedListStore.getHoldSpace
    getRoutine = LinkedListStore.getRoutine
    execOnHoldSpace = LinkedListStore.execOnHoldSpace
    empty = Empty
    weaken = LinkedListStore.weaken
    holdSpace = HS
    label = LB