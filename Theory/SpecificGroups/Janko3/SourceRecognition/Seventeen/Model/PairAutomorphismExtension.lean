module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.PairFieldAutomorphism
public import Theory.SpecificGroups.Janko3.SourceRecognition.PairAutomorphisms

/-!
# Every full pair marking extends to the sixteen-field model

The order-sixty pair has only two outer automorphism classes. Its inner
automorphisms extend by the same inner elements of PSL₂(16):2, and coefficient
square Frobenius realizes the other class. Thus any chosen isomorphism on
the full pair intersection can be matched pointwise by changing the model
marking of the sixteen-field subgroup.
-/

public noncomputable section
open Subgroup
open Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

private def pairCoordinates : CyclicCoordinates.Normalizer ≃* pair :=
  (MonoidHom.ofInjective pairLift_injective).trans (MulEquiv.subgroupCongr pairLift_range)

private theorem coordinateSquare_dihedral (x : CyclicCoordinates.Normalizer) :
    CyclicCoordinates.dihedralEquiv (coordinateSquare x) =
      PairAutomorphisms.delta (CyclicCoordinates.dihedralEquiv x) := by
  revert x
  decide +kernel

/-- Any automorphism of the full literal pair subgroup extends to the actual
PSL₂(16):2 model, with equality on every element of that subgroup. -/
theorem pair_automorphism_extends (φ : MulAut pair) :
    ∃ Φ : MulAut Model, ∀ x : pair, Φ x = (φ x : Model) := by
  let E : pair ≃* PairAutomorphisms.H := pairCoordinates.symm.trans CyclicCoordinates.dihedralEquiv
  let a : MulAut PairAutomorphisms.H := (MulAut.congr E) φ
  obtain ⟨h,ε,he⟩ := PairAutomorphisms.exists_inner_mul_delta a
  let c : pair := E.symm h
  let Φ : MulAut Model := MulAut.conj (c : Model) * (if ε then squareModel else 1)
  refine ⟨Φ,?_⟩
  intro x
  let z : pair := pairCoordinates (coordinateSquare (pairCoordinates.symm x))
  have hz : (z : Model) = squareModel x := by
    have hp : pairLift (pairCoordinates.symm x) = (x : Model) :=
      congrArg Subtype.val (pairCoordinates.apply_symm_apply x)
    change pairLift (coordinateSquare (pairCoordinates.symm x)) = squareModel x
    rw [←squareModel_pairLift,hp]
  have hEz : E z = PairAutomorphisms.delta (E x) := by
    change CyclicCoordinates.dihedralEquiv
      (pairCoordinates.symm (pairCoordinates (coordinateSquare (pairCoordinates.symm x)))) = _
    rw [pairCoordinates.symm_apply_apply,coordinateSquare_dihedral]
    rfl
  have hx : φ x = c * (if ε then z else x) * c⁻¹ := by
    apply E.injective
    have hh := congrArg (fun b : MulAut PairAutomorphisms.H => b (E x)) he
    change E (φ (E.symm (E x))) = _ at hh
    rw [E.symm_apply_apply] at hh
    rw [map_mul,map_mul,map_inv,E.apply_symm_apply]
    cases ε <;> simpa only [Bool.false_eq_true, ↓reduceIte, MulAut.mul_apply,
      MulAut.one_apply,MulAut.conj_apply,hEz] using hh
  rw [hx]
  cases ε
  · rfl
  · change (c : Model) * squareModel x * (c : Model)⁻¹ =
      (c : Model) * (z : Model) * (c : Model)⁻¹
    rw [hz]

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
