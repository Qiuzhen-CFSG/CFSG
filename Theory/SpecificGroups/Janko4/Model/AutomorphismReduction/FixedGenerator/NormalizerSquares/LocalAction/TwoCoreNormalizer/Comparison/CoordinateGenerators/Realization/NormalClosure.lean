module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.RawAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison.CoordinateConstruction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.IntrinsicCenter


/-!
# The intrinsic center and column action of the max2 normal closure

The certified commutator pairing identifies the intrinsic center of the
actual seed normal closure N with the powers of its distinguished involution.
Its center therefore has order two. The previously constructed coordinates
on N/<t> now give coordinates on N/Z(N), proving that N is extraspecial.
No structure of the ambient two-core is assumed in these conclusions.

The published right-row conjugation matrices become the required left-column
matrices by inverse transpose. Transporting the proved coordinate-action
identities gives both raw actions on N/<t>. When H is the whole literal
involution centralizer, normality and the proved two-group property also put
the image of N inside O₂(H). Equality with that two-core is a separate step.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. Actual coordinates and conjugation
certificates are reused from `OuterImageComparison.CoordinateConstruction`;
the intrinsic-center calculation is reused from `NormalClosureControl.IntrinsicCenter`.
-/

@[expose] public section

open scoped Matrix
set_option maxRecDepth 4000

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators
open TwoCoreCentralizerData
namespace Realization

/-- Full local generation puts the actual seed normal closure in the two-core. -/
theorem normalClosureImage_le_twoCore (hgen : localSubgroup = ⊤) :
    localNormalClosure.map localSubgroup.subtype ≤ involutionTwoCore := by
  have hs : Function.Surjective localSubgroup.subtype := by
    intro c
    exact ⟨⟨c, by rw [hgen]; trivial⟩, rfl⟩
  exact le_sSup ⟨localNormalClosure_normal.map localSubgroup.subtype hs,
    localNormalClosure_isPGroup.map localSubgroup.subtype⟩

private theorem center_coe_centralizes {G : Type*} [Group G] (N : Subgroup G)
    {n : N} (hn : n ∈ Subgroup.center N) :
    (n : G) ∈ Subgroup.centralizer (N : Set G) := by
  intro m hm
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hn ⟨m, hm⟩)

/-- The intrinsic center is exactly the distinguished involution subgroup. -/
theorem normalClosure_center :
    Subgroup.center localNormalClosure = OuterImageComparison.centralPowers := by
  apply le_antisymm
  · intro n hn
    have hz : (n : localSubgroup) ∈ Subgroup.zpowers subgroupInvolution :=
      localNormalClosure_inf_centralizer_le_zpowers
        ⟨n.property, center_coe_centralizes localNormalClosure hn⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
  · exact Subgroup.zpowers_le.mpr OuterImageComparison.centralWord_mem_center

/-- The distinguished element has order two also inside the normal closure. -/
theorem normalClosure_center_card : Nat.card (Subgroup.center localNormalClosure) = 2 := by
  rw [normalClosure_center, OuterImageComparison.centralPowers, Nat.card_zpowers]
  rw [← orderOf_injective localNormalClosure.subtype Subtype.val_injective]
  exact orderOf_subgroupInvolution

/-- The published coordinates, now on the quotient by the intrinsic center. -/
noncomputable def normalClosureCentralCoordinates :
    (localNormalClosure ⧸ Subgroup.center localNormalClosure) ≃*
      Multiplicative (Fin 12 → ZMod 2) :=
  (QuotientGroup.congr (Subgroup.center localNormalClosure) OuterImageComparison.centralPowers
    (MulEquiv.refl _) (by
      change (Subgroup.center localNormalClosure).map (MonoidHom.id _) = _
      rw [Subgroup.map_id]
      exact normalClosure_center)).trans
    OuterImageComparison.coordinates

/-- Extraspeciality follows from the actual center and quotient calculations. -/
theorem normalClosure_extraspecial : IsExtraspecial 2 localNormalClosure := by
  let e := normalClosureCentralCoordinates
  refine ⟨normalClosure_center_card, ?_, e.surjective.nontrivial⟩
  refine { toIsMulCommutative := ⟨⟨fun x y => e.injective (by simp [mul_comm])⟩⟩
           exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply e.injective
  rw [map_pow, map_one]
  change (2 : ℕ) • (e x).toAdd = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  exact zero_smul (ZMod 2) (e x).toAdd

/-- The raw X matrix is the inverse transpose of the right-row matrix. -/
theorem rawMatrixX_eq_inverse_transpose :
    rawMatrixX = (↑OuterImageComparison.actionUnitX⁻¹ : LowerBound.QuotientMatrix).transpose := by
  decide +kernel

/-- The raw Y matrix is the inverse transpose of the right-row matrix. -/
theorem rawMatrixY_eq_inverse_transpose :
    rawMatrixY = (↑OuterImageComparison.actionUnitY⁻¹ : LowerBound.QuotientMatrix).transpose := by
  decide +kernel

/-- Left conjugation by X on the literal normal closure quotient. -/
theorem normalClosure_actionX (n : localNormalClosure) :
    rawMatrixX *ᵥ (OuterImageComparison.coordinates (OuterImageComparison.projection n)).toAdd =
      (OuterImageComparison.coordinates
        (OuterImageComparison.projection (localNormalClosureAction subgroupX n))).toAdd := by
  have h := congrArg (fun a : MulAut (Multiplicative OuterImageComparison.BinaryVector) =>
      (a (OuterImageComparison.coordinates (OuterImageComparison.projection n))).toAdd)
    (OuterImageComparison.coordinateAction_x OuterImageComparison.coordinates
      OuterImageComparison.coordinates_respectsBasis)
  change (OuterImageComparison.coordinates
      (OuterImageComparison.quotientAction subgroupX
        (OuterImageComparison.coordinates.symm
          (OuterImageComparison.coordinates (OuterImageComparison.projection n))))).toAdd = _ at h
  rw [MulEquiv.symm_apply_apply, OuterImageComparison.quotientAction_projection,
    OuterImageComparison.rowAction_apply] at h
  rw [rawMatrixX_eq_inverse_transpose, Matrix.mulVec_transpose]
  exact h.symm

/-- Left conjugation by Y on the literal normal closure quotient. -/
theorem normalClosure_actionY (n : localNormalClosure) :
    rawMatrixY *ᵥ (OuterImageComparison.coordinates (OuterImageComparison.projection n)).toAdd =
      (OuterImageComparison.coordinates
        (OuterImageComparison.projection (localNormalClosureAction subgroupY n))).toAdd := by
  have h := congrArg (fun a : MulAut (Multiplicative OuterImageComparison.BinaryVector) =>
      (a (OuterImageComparison.coordinates (OuterImageComparison.projection n))).toAdd)
    (OuterImageComparison.coordinateAction_y OuterImageComparison.coordinates
      OuterImageComparison.coordinates_respectsBasis)
  change (OuterImageComparison.coordinates
      (OuterImageComparison.quotientAction subgroupY
        (OuterImageComparison.coordinates.symm
          (OuterImageComparison.coordinates (OuterImageComparison.projection n))))).toAdd = _ at h
  rw [MulEquiv.symm_apply_apply, OuterImageComparison.quotientAction_projection,
    OuterImageComparison.rowAction_apply] at h
  rw [rawMatrixY_eq_inverse_transpose, Matrix.mulVec_transpose]
  exact h.symm

end Realization
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators
