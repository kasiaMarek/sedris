module Sedris.Extra

%default total

export
positiveLengthImpNonEmpty : (sx : SnocList t)
                          -> {0 n : Nat}
                          -> (length sx = S n)
                          -> (tail : t ** (neck : SnocList t ** neck :< tail = sx))
positiveLengthImpNonEmpty [<] Refl impossible
positiveLengthImpNonEmpty (sx :< x) Refl = (x ** sx ** Refl)

export
fishConcat : {sx : SnocList a} -> {ys, zs : List a}
          -> (sx <>< ys) <>< zs = sx <>< (ys ++ zs)
fishConcat {sx = sx, zs = zs, ys = []} = Refl
fishConcat {sx = sx, zs = zs, ys = (y :: ys)} = fishConcat

