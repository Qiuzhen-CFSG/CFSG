module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.NormalizedMatrices.Encoding
open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
/-!
# Changes of basis for the seven surviving matrices

Each row specifies a normalized transposition and double-transposition matrix,
a published target action, and inverse binary basis matrices. Their two inverse
identities construct an actual `MulAut BinaryFour`. Kernel checks verify the
three labelled generator intertwining equations on the four basis vectors.
Automorphism extensionality proves the equations on every vector, and
`equivalent_of_generators` extends them to the whole S₄ action.

The matrices are explicit auxiliary computations for the action problem used
in Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
@[expose] public def rowT (i : Fin 7) : Cols := if i.val < 3 then t else u
@[expose] public def rowK (i : Fin 7) : Cols := match i.val with
  | 0 => ![2,1,8,4]
  | 1 => ![2,1,15,8]
  | 2 => ![6,5,4,12]
  | 3 => ![2,1,8,4]
  | 4 => ![6,10,11,8]
  | 5 => ![9,5,11,8]
  | _ => ![14,13,4,8]
@[expose] public def rowAction (i : Fin 7) : SymmetricFour →* MulAut BinaryFour :=
  if i.val < 3 then permutationAction else if i.val = 3 then twistedAction
  else if i.val < 6 then twelveOrbitAction else sixOrbitAction
private def basisColumns (i : Fin 7) : Cols := match i.val with
  | 0 => ![1,2,4,8]
  | 1 => ![1,2,4,15]
  | 2 => ![9,10,12,7]
  | 3 => ![1,2,4,8]
  | 4 => ![14,1,11,12]
  | 5 => ![6,9,3,4]
  | _ => ![7,11,5,1]
private def inverseColumns (i : Fin 7) : Cols := match i.val with
  | 0 => ![1,2,4,8]
  | 1 => ![1,2,4,15]
  | 2 => ![14,13,11,15]
  | 3 => ![1,2,4,8]
  | 4 => ![2,9,7,15]
  | 5 => ![13,9,8,15]
  | _ => ![8,5,12,15]
private theorem inverse_left : ∀ i : Fin 7, comp (inverseColumns i) (basisColumns i) = ident := by decide +kernel
private theorem inverse_right : ∀ i : Fin 7, comp (basisColumns i) (inverseColumns i) = ident := by decide +kernel
private def basisAut (i : Fin 7) : MulAut BinaryFour where
  toFun := lin (basisColumns i)
  invFun := lin (inverseColumns i)
  left_inv := fun v => by rw [← lin_comp, inverse_left, lin_ident]
  right_inv := fun v => by rw [← lin_comp, inverse_right, lin_ident]
  map_mul' := lin_mul (basisColumns i)
private theorem intertwines_x : ∀ (i : Fin 7) (j : Fin 4),
    basisAut i (lin x (binaryBasis j)) =
      rowAction i threeCycle (basisAut i (binaryBasis j)) := by decide +kernel
private theorem intertwines_t : ∀ (i : Fin 7) (j : Fin 4),
    basisAut i (lin (rowT i) (binaryBasis j)) =
      rowAction i transposition (basisAut i (binaryBasis j)) := by decide +kernel
private theorem intertwines_k : ∀ (i : Fin 7) (j : Fin 4),
    basisAut i (lin (rowK i) (binaryBasis j)) =
      rowAction i doubleTransposition (basisAut i (binaryBasis j)) := by decide +kernel
private theorem intertwines_of_basis (e f g : MulAut BinaryFour)
    (h : ∀ j, e (f (binaryBasis j)) = g (e (binaryBasis j))) :
    ∀ v, e (f v) = g (e v) := by
  have he : e * f = g * e := mulAut_ext _ _ h
  exact fun v => congrArg (fun a : MulAut BinaryFour => a v) he

/-- The row's actual basis automorphism intertwines every labelled actor. -/
public theorem equivalent_row (β : SymmetricFour →* MulAut BinaryFour) (i : Fin 7)
    (hx : columns (β threeCycle) = x) (ht : columns (β transposition) = rowT i)
    (hk : columns (β doubleTransposition) = rowK i) : ActionEquivalent β (rowAction i) := by
  apply equivalent_of_generators β (rowAction i) (basisAut i)
  · apply intertwines_of_basis
    intro j
    rw [← lin_columns (β threeCycle) (binaryBasis j), hx]
    exact intertwines_x i j
  · apply intertwines_of_basis
    intro j
    rw [← lin_columns (β transposition) (binaryBasis j), ht]
    exact intertwines_t i j
  · apply intertwines_of_basis
    intro j
    rw [← lin_columns (β doubleTransposition) (binaryBasis j), hk]
    exact intertwines_k i j
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
