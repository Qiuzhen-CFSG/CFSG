/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/LeechCentralQuotient.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechCenter
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Coset.Card
/-!
Central signs, antipodal geometry, and faithful quotient actions for the Leech isometry group.
The proofs identify the actual kernels and transport the concrete actions through the central quotient.

Source: Gerald Höhn, `Atlas/Conway/LeechCentralQuotient.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem central_rational_scalar (g : LeechIsometryGroup)
    (hg : g ∈ Subgroup.center LeechIsometryGroup) :
    ∃ r : ℚ, (r = 1 ∨ r = -1) ∧ ∀ x : RationalCoordinates, rationalExtension g.val x = r • x := by
  rcases central_eq_one_or_negation g hg with rfl | rfl
  · refine ⟨1,Or.inl rfl,?_⟩
    have he := rationalExtension_unique (1 : LeechIsometryGroup).val
      (LinearMap.id : RationalCoordinates →ₗ[ℚ] RationalCoordinates) (fun x => rfl)
    intro x
    have hx := congrArg (fun f : RationalCoordinates →ₗ[ℚ] RationalCoordinates => f x) he
    simpa using hx.symm
  · refine ⟨-1,Or.inr rfl,?_⟩
    have he := rationalExtension_unique negationIsometry.val
      (-LinearMap.id : RationalCoordinates →ₗ[ℚ] RationalCoordinates) (by
        intro x; rw [negationIsometry_apply]; simp)
    intro x
    have hx := congrArg (fun f : RationalCoordinates →ₗ[ℚ] RationalCoordinates => f x) he
    simpa using hx.symm

def leechCentralSigns : Subgroup LeechIsometryGroup := Subgroup.zpowers negationIsometry

theorem leechCentralSigns_eq_center : leechCentralSigns = Subgroup.center LeechIsometryGroup := by
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr negation_mem_center
  · intro g hg
    rcases central_eq_one_or_negation g hg with rfl | rfl
    · exact leechCentralSigns.one_mem
    · exact Subgroup.mem_zpowers _

theorem leechCentralSigns_mem (g : LeechIsometryGroup) :
    g ∈ leechCentralSigns ↔ g = 1 ∨ g = negationIsometry := by
  rw [leechCentralSigns_eq_center,leech_center_iff]

theorem leechCentralSigns_card : Nat.card leechCentralSigns = 2 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [leechCentralSigns,Nat.card_zpowers]
  exact orderOf_eq_prime (by simpa [pow_two] using negationIsometry_sq) negationIsometry_ne_one

instance : leechCentralSigns.Normal := by
  rw [leechCentralSigns_eq_center]
  infer_instance

/-- The actual central quotient; its Conway order and simplicity are separate obligations. -/
abbrev LeechCentralQuotient := LeechIsometryGroup ⧸ leechCentralSigns

def leechCentralProjection : LeechIsometryGroup →* LeechCentralQuotient :=
  QuotientGroup.mk' leechCentralSigns

theorem leechCentralProjection_kernel : leechCentralProjection.ker = leechCentralSigns :=
  QuotientGroup.ker_mk' _

theorem leechCentralProjection_surjective : Function.Surjective leechCentralProjection :=
  QuotientGroup.mk'_surjective _

instance : Finite LeechCentralQuotient := inferInstance

theorem leechCentralQuotient_card_relation :
    2 * Nat.card LeechCentralQuotient = Nat.card LeechIsometryGroup := by
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup leechCentralSigns
  rw [leechCentralSigns_card] at he
  simpa [Nat.mul_comm] using he.symm

end Atlas.Conway
