module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.ClassicalModel.Coordinates
public import Mathlib.Tactic.FinCases

/-!
# Comparison with the canonical minus orthogonal space

The columns (1,4), (2,12), (26,41) give two hyperbolic pairs and an
anisotropic pair for the form of `Coordinates`. The resulting linear
isometry conjugates the full orthogonal groups and their actual commutator
subgroups. Over the binary field the scalar subgroup is trivial, so this
also identifies the latter with the canonical projective Omega model.
No generation or simplicity assertion enters these comparisons.

Source: GLS3, section 2.7, and the canonical definitions in
`ClassicalOrthogonal.Minus`.
-/

@[expose] public section

open ClassicalOrthogonal.Minus Theory.AlgebraicGroup
namespace Sporadic.LeechRelated.Suz.CentralizerSection.ClassicalModel

abbrev CanonicalSpace := Space K 2
noncomputable abbrev CanonicalO := Orthogonal K CanonicalSpace (quadraticForm K 3)

theorem binary_parameter : parameter K = 1 := by
  have h := parameter_spec K 0
  have hn : parameter K ≠ 0 := by simpa using Ne.symm h
  have htwo : ∀ a : K, a ≠ 0 → a = 1 := by decide +kernel
  exact htwo _ hn

def pack : V ≃ₗ[K] CanonicalSpace where
  toFun v := (![(v 0, v 1), (v 2, v 3)], (v 4, v 5))
  invFun v := ![(v.1 0).1, (v.1 0).2, (v.1 1).1, (v.1 1).2, v.2.1, v.2.2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by
    intro v w
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_smul' := by
    intro a v
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

/-- Columns are a hyperbolic pair, another hyperbolic pair, and an anisotropic pair. -/
def wittMatrix := columns ![1,4,2,12,26,41]
def fromWittMatrix := columns ![1,4,2,10,30,43]
private theorem witt_inverse :
    wittMatrix * fromWittMatrix = 1 ∧ fromWittMatrix * wittMatrix = 1 := by
  decide +kernel

def canonicalLinear : V ≃ₗ[K] CanonicalSpace :=
  (Matrix.toLin'OfInv (M := wittMatrix) (M' := fromWittMatrix) (by exact witt_inverse.1) (by exact witt_inverse.2)).trans pack

theorem canonicalLinear_form (v : V) : quadraticForm K 3 (canonicalLinear v) = form v := by
  unfold quadraticForm
  rw [binary_parameter]
  exact (show ∀ v : V, ClassicalOrthogonal.Minus.form K 2 1 (canonicalLinear v) = form v by
    decide +kernel) v

noncomputable def orthogonalEquiv : O ≃* CanonicalO where
  toFun g := ⟨canonicalLinear.symm.trans (g.val.trans canonicalLinear), by
    apply (mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    have hg := (mem_quadraticIsometrySubgroup form _).mp g.property
    change quadraticForm K 3 (canonicalLinear (g.val (canonicalLinear.symm v))) = _
    rw [canonicalLinear_form, hg, ← canonicalLinear_form]
    rw [canonicalLinear.apply_symm_apply]⟩
  invFun g := ⟨canonicalLinear.trans (g.val.trans canonicalLinear.symm), by
    apply (mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    have hg := (mem_quadraticIsometrySubgroup _ _).mp g.property
    change form (canonicalLinear.symm (g.val (canonicalLinear v))) = _
    rw [← canonicalLinear_form, canonicalLinear.apply_symm_apply, hg,
      canonicalLinear_form]⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp

noncomputable def omegaEquiv : commutator O ≃* commutator CanonicalO :=
  (orthogonalEquiv.subgroupMap (commutator O)).trans
    (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr orthogonalEquiv.surjective]
      rfl))

theorem binary_scalarSubgroup :
    scalarSubgroup K CanonicalSpace (quadraticForm K 3) = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro g ⟨c,hc⟩
  rw [Subgroup.mem_bot]
  have hc1 : (c : K) = 1 := by
    exact (show ∀ a : K, a ≠ 0 → a = 1 by decide +kernel) _ c.ne_zero
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change g.val.val v = v
  simpa only [hc1, one_smul] using hc v

noncomputable def canonicalProjectiveEquiv :
    commutator CanonicalO ≃* ClassicalGroup.POmegaMinus 3 K :=
  QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq binary_scalarSubgroup.symm)

noncomputable def omegaProjectiveEquiv : commutator O ≃* ClassicalGroup.POmegaMinus 3 K :=
  omegaEquiv.trans canonicalProjectiveEquiv

end Sporadic.LeechRelated.Suz.CentralizerSection.ClassicalModel
