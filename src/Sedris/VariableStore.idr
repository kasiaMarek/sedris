module Sedris.VariableStore

import Sedris.Lang
import Sedris.Thinnings

%default total

public export
interface VariableStore (Store : Variables -> FileScriptType -> Type) where
  --- adding variables
  holdSpace : (name : String) -> {t : Type} -> (value : t) -> Store sx st
            -> Store (sx :< (HoldSpace t, name)) st
  label : (name : String) -> {st : ScriptType} -> (getScriptByType st sx io)
        -> Store sx io -> Store (sx :< (Label st, name)) io
  --- getting variables
  getHoldSpace : {0 name : String} -> {0 t : Type} -> {0 sx : Variables}
              -> (pos : (HoldSpace t, name) `Elem` sx)
              -> Store sx st -> t
  getRoutine : {0 name : String}
            -> (sx : Variables)
            -> {st : ScriptType}
            -> (pos : (Label st, name) `Elem` sx)
            -> Store sx io
            -> getScriptByType st sx io
  --- variable mutation
  execOnHoldSpace : {0 name : String} -> {0 t : Type}
                  -> {0 sx : Variables} -> (pos : (HoldSpace t, name) `Elem` sx)
                  -> Store sx st -> (t -> t)
                  -> Store sx st
  --- thinning
  weaken : Store sy st -> Weakening sx sy -> Store sx st
  --- empty store
  empty : Store [<] st

namespace LinkedListStore
  public export
  data LinkedListStore : Variables -> FileScriptType -> Type where
    Empty : LinkedListStore [<] st
    HS : (name : String) -> {t : Type} -> (value : t) -> LinkedListStore sx st
      -> LinkedListStore (sx :< (HoldSpace t, name)) st
    LB : (name : String) -> {st : ScriptType} -> (getScriptByType st sx io)
      -> LinkedListStore sx io
      -> LinkedListStore (sx :< (Label st, name)) io
  
  getHoldSpace : {0 name : String} -> {0 t : Type}
              -> {0 xs : SnocList (VarType, String)}
              -> (pos : (HoldSpace t, name) `Elem` xs)
              -> LinkedListStore xs st
              -> t
  getHoldSpace Here (HS _ value _) = value
  getHoldSpace (There pos) (HS str value tail) = getHoldSpace pos tail
  getHoldSpace (There pos) (LB str sc tail) = getHoldSpace pos tail

  getRoutineAux : {0 name : String}
                -> (sx : Variables)
                -> {st : ScriptType}
                -> (pos : (Label st, name) `Elem` sx)
                -> LinkedListStore sx io
                -> Exists (\sy => (getScriptByType st sy io, Thinning sy sx))
  getRoutineAux (sx :< (Label st, name))   Here (LB name sc store)
    = Evidence sx (sc, (id sx).Drop)
  getRoutineAux (sx :< (HoldSpace t, str)) (There pos) (HS str value store)
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in Evidence sy (sc, tau.Drop)
  getRoutineAux (sx :< (Label st, str))    (There pos) (LB str x store)
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in Evidence sy (sc, tau.Drop)

  getRoutine : {0 name : String}
            -> (sx : Variables)
            -> {st : ScriptType}
            -> (pos : (Label st, name) `Elem` sx)
            -> LinkedListStore sx io
            -> getScriptByType st sx io
  getRoutine sx pos store {st}
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in case st of
          Total => thin sc tau
          LineByLine => thin sc tau

  execOnHoldSpace : {0 name : String} -> {0 t : Type}
                  -> {0 xs : SnocList (VarType, String)}
                  -> (pos : (HoldSpace t, name) `Elem` xs)
                  -> LinkedListStore xs st
                  -> (t -> t)
                  -> LinkedListStore xs st
  execOnHoldSpace Here (HS name value hs) f = HS name (f value) hs
  execOnHoldSpace (There pos) (HS str value hs) f
    = HS str value (execOnHoldSpace pos hs f)
  execOnHoldSpace (There pos) (LB str name hs) f
    = LB str name (execOnHoldSpace pos hs f)

  weaken : LinkedListStore sy st -> Weakening sx sy -> LinkedListStore sx st
  weaken store (Weaken ys {ford = Refl})
    = weaken' (cast ys) (replace  {p = (\vars => LinkedListStore vars st)}
                                  prf
                                  store) where
      prf : {sx, sy : SnocList a} -> {ys : List a}
          -> ((sx ++ sy) <>< ys = sx ++ (sy <>< ys))
      prf {sx, sy, ys = []} = Refl
      prf {sx, sy, ys = (y :: ys)} = prf {sx, sy = sy :< y, ys}
      weaken' : (sy : Variables) -> LinkedListStore (sx ++ sy) st
              -> LinkedListStore sx st
      weaken' [<] store = store
      weaken' (sy :< (HoldSpace _, _))  (HS _ _ store) = weaken' sy store
      weaken' (sy :< (Label _, _))      (LB _ _ store) = weaken' sy store

  public export
  VariableStore LinkedListStore where
    getHoldSpace = LinkedListStore.getHoldSpace
    getRoutine = LinkedListStore.getRoutine
    execOnHoldSpace = LinkedListStore.execOnHoldSpace
    empty = Empty
    weaken = LinkedListStore.weaken
    holdSpace = HS
    label = LB