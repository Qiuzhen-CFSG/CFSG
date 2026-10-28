module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.Data

/-!
# The dihedral subgroup in an arbitrary long Leech frame

The block SL₂ fixes coordinates 0 and 5 and acts identically on (1,2) and
(3,4). Testing its action on single-coordinate vectors proves that its lift
through any `LongFrame` is injective. The matrices `[[0,1],[1,τ]]` and the
flip embed D₁₀ over `GoldenFour`; a field isomorphism transports them to the
actual coordinate field and then into the literal Leech central quotient.

The two factors of `LocalA5.pairRepresentation` commute with this action.
These are the precise dihedral placement and linear conventions consumed by
`SourceConstruction.Inputs`. This does not yet construct the centralizing A₅.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
with the D₁₀ centralizer from Lemmas 47.2 and 48.8. The block formula
extends the calculation in `LocalA5.DiagonalAmbiguity` to the actual field.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

/-- The coordinate field comparison used only to specify the order-five matrix. -/
def fieldEquiv : GoldenFour ≃+* F := by
  letI : Fintype F := Fintype.ofFinite F
  exact (FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide), goldenFour_card]
    norm_num) : F ≃+* GoldenFour).symm

def slEquiv : SL(2,GoldenFour) ≃* SL(2,F) where
  toFun := Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom
  invFun := Matrix.SpecialLinearGroup.map fieldEquiv.symm.toRingHom
  left_inv a := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change fieldEquiv.symm (fieldEquiv (a.val i j)) = a.val i j
    exact fieldEquiv.symm_apply_apply _
  right_inv a := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change fieldEquiv (fieldEquiv.symm (a.val i j)) = a.val i j
    exact fieldEquiv.apply_symm_apply _
  map_mul' := map_mul _

def alternatingEquiv : SL(2,F) ≃* alternatingGroup (Fin 5) :=
  slEquiv.symm.trans goldenFourSLAlternatingFive

def blockMatrix (a : SL(2,F)) : SL(3,F) := ⟨!![1,0,0;0,a.val 0 0,a.val 0 1;0,a.val 1 0,a.val 1 1], by
    have hd := a.property
    rw [Matrix.det_fin_two] at hd
    simpa [Matrix.det_fin_three] using hd⟩

def block : SL(2,F) →* SL(3,F) where
  toFun := blockMatrix
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMatrix]
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMatrix, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_three, Fin.sum_univ_two]

def blockAction (a : SL(2,F)) (v : Fin 6 → F) : Fin 6 → F :=
  ![v 0, a.val 0 0 * v 1 + a.val 0 1 * v 2,
    a.val 1 0 * v 1 + a.val 1 1 * v 2,
    a.val 0 0 * v 3 + a.val 0 1 * v 4,
    a.val 1 0 * v 3 + a.val 1 1 * v 4, v 5]

theorem blockAction_eq (a : SL(2,F)) (v : Fin 6 → F) :
    action (BlockRealization.blockHom (block a)) v = blockAction a v := by
  rw [action_block]
  have hd : a.val 0 0 * a.val 1 1 - a.val 0 1 * a.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using a.property
  funext i
  fin_cases i <;>
    simp [blockAction, block, blockMatrix, BlockRealization.cofactor,
      Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      CharTwo.neg_eq, hd, CharTwo.sub_eq_add] <;> ring_nf at *

def longTwo (L : LongFrame) : SL(2,F) →* LeechCentralQuotient := L.long.comp block

theorem longTwo_action (L : LongFrame) (a : SL(2,F)) (v : Fin 6 → F) :
    quotientModTwoRepresentation (longTwo L a) (L.coordinates v) =
      L.coordinates (blockAction a v) := by
  rw [← blockAction_eq]
  exact L.intertwines_long (block a) v

theorem longTwo_injective (L : LongFrame) : Function.Injective (longTwo L) := by
  intro a b h
  have he (v : Fin 6 → F) : blockAction a v = blockAction b v := by
    apply L.coordinates_injective
    rw [← longTwo_action, ← longTwo_action, h]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blockAction] using congrFun (he (Pi.single 1 1)) 1
  · simpa [blockAction] using congrFun (he (Pi.single 2 1)) 1
  · simpa [blockAction] using congrFun (he (Pi.single 1 1)) 2
  · simpa [blockAction] using congrFun (he (Pi.single 2 1)) 2

theorem pairAction_commutes_block (p : SL(2,F) × SL(2,F)) (a : SL(2,F))
    (v : Fin 6 → F) :
    pairAction p (blockAction a v) = blockAction a (pairAction p v) := by
  funext i
  fin_cases i <;> simp [pairAction, blockAction] <;> ring

local instance : CharP GoldenFour 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) GoldenFour).injective 2

def rotation : SL(2,GoldenFour) :=
  ⟨!![0,1;1,goldenFourTau], by decide +kernel⟩

def dihedralValue : DihedralGroup 5 → SL(2,GoldenFour)
  | .r i => rotation ^ i.val
  | .sr i => flip * rotation ^ i.val

def dihedralModel : DihedralGroup 5 →* SL(2,GoldenFour) where
  toFun := dihedralValue
  map_one' := rfl
  map_mul' := by decide +kernel

theorem dihedralModel_injective : Function.Injective dihedralModel := by decide +kernel

/-- The actual marked D₁₀ in the chosen long subgroup of the Leech quotient. -/
def dihedralLift (L : LongFrame) : DihedralGroup 5 →* LeechCentralQuotient :=
  (longTwo L).comp (slEquiv.toMonoidHom.comp dihedralModel)

theorem dihedralLift_injective (L : LongFrame) : Function.Injective (dihedralLift L) :=
  (longTwo_injective L).comp (slEquiv.injective.comp dihedralModel_injective)

theorem dihedralLift_mem (L : LongFrame) (d : DihedralGroup 5) :
    dihedralLift L d ∈ centralizerI := L.long_mem _

theorem dihedralLift_action (L : LongFrame) (d : DihedralGroup 5) (v : Fin 6 → F) :
    quotientModTwoRepresentation (dihedralLift L d) (L.coordinates v) =
      L.coordinates (blockAction (slEquiv (dihedralModel d)) v) :=
  longTwo_action L _ v

theorem dihedralLift_card (L : LongFrame) : Nat.card (dihedralLift L).range = 10 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (dihedralLift_injective L)).toEquiv]
  exact DihedralGroup.nat_card

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
