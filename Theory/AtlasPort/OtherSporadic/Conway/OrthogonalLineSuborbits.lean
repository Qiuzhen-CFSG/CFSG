/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalLineSuborbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLineStabilizer
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalClassOrbits

/-!
The five suborbits of the full orthogonal-line stabilizer.
Class-profile transport and antipodal descent prove transitivity on each explicit fiber.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalLineSuborbits.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

theorem orthogonalClassIndex_neg (i : Omega) (x : leech) :
    orthogonalClassIndex i (-x) = orthogonalClassIndex i x := by
  have h (k u : ℕ) : (-x.val) ∈ twoFourFamily k u ↔ x.val ∈ twoFourFamily k u := by
    have hh := monomial_twoFour_iff monomialCentralElement x k u
    rw [monomialCentralElement_image,negationIsometry_apply] at hh
    exact hh
  simp only [orthogonalClassIndex,h,Submodule.coe_neg,Pi.neg_apply,neg_eq_zero]

theorem orthogonal_class_orbit_neg_closed (i j : Omega) (hij : i ≠ j)
    (t : Fin 5) (x : OrthogonalClassType i j t) (y : leech)
    (hy : y ∈ MulAction.orbit (leechVectorStabilizer monomialSubgroup (minimumPairPlus i j))
      (orthogonalClassValue i j t x)) :
    -y ∈ MulAction.orbit (leechVectorStabilizer monomialSubgroup (minimumPairPlus i j))
      (orthogonalClassValue i j t x) := by
  obtain ⟨z,rfl⟩ := (orthogonalClass_monomial_orbit i j hij t x y).mp hy
  have hg := orthogonalClass_good i j hij t z
  have hn : integerDot (- (orthogonalClassValue i j t z).val)
      (- (orthogonalClassValue i j t z).val) = 32 := by simpa [integerDot] using hg.1
  have ho : integerDot (minimumPairPlus i j).val (-(orthogonalClassValue i j t z).val) = 0 := by
    simpa [integerDot,Finset.sum_neg_distrib] using congrArg Neg.neg hg.2
  obtain ⟨s,w,hw⟩ := orthogonalClass_exhaustive i j hij (-(orthogonalClassValue i j t z)) hn ho
  have hi := congrArg (orthogonalClassIndex i) hw
  rw [orthogonalClassIndex_neg,orthogonalClassIndex_value i j hij,
    orthogonalClassIndex_value i j hij] at hi
  subst s
  exact (orthogonalClass_monomial_orbit i j hij t x _).mpr ⟨w,hw⟩

def orthogonalLineOrbitEquiv (i j : Omega) (hij : i ≠ j) (y : leech) :
    MulAction.orbit (orthogonalLineStabilizer i j) (antipodalLine y) ≃
    AntipodalImage (MulAction.orbit
      (leechVectorStabilizer monomialSubgroup (minimumPairPlus i j)) y) :=
  Equiv.subtypeEquivRight (fun l => by
    constructor
    · rintro ⟨g,rfl⟩
      let m := orthogonalLineMonomialEquiv i j hij g
      refine ⟨m.val.val.val y,⟨m,rfl⟩,?_⟩
      exact (projection_antipodalLine g.val.val y).symm
    · rintro ⟨v,⟨m,hm⟩,he⟩
      let g := (orthogonalLineMonomialEquiv i j hij).symm m
      refine ⟨g,?_⟩
      change leechCentralProjection m.val.val • antipodalLine y = l
      exact (projection_antipodalLine m.val.val y).trans ((congrArg antipodalLine hm).trans he))

theorem orthogonal_line_suborbit_card (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) :
    Nat.card (MulAction.orbit (orthogonalLineStabilizer i j)
      (antipodalLine (orthogonalClassValue i j t x))) = ![1,462,21120,2464,22528] t := by
  let S := MulAction.orbit (leechVectorStabilizer monomialSubgroup (minimumPairPlus i j))
    (orthogonalClassValue i j t x)
  have hz (y : leech) (hy : y ∈ S) : y ≠ 0 := by
    obtain ⟨z,rfl⟩ := (orthogonalClass_monomial_orbit i j hij t x y).mp hy
    exact minimum_vector_ne_zero ⟨_,(orthogonalClass_good i j hij t z).1⟩
  let : Finite S := Nat.finite_of_card_ne_zero (by
    change Nat.card (MulAction.orbit _ _) ≠ 0
    rw [orthogonalClass_monomial_orbit_card i j hij t x]
    fin_cases t <;> decide)
  have h := antipodalImage_card S (orthogonal_class_orbit_neg_closed i j hij t x) hz
  rw [← Nat.card_congr (orthogonalLineOrbitEquiv i j hij _)] at h
  change 2 * Nat.card (MulAction.orbit (orthogonalLineStabilizer i j)
    (antipodalLine (orthogonalClassValue i j t x))) = Nat.card S at h
  have hc : Nat.card S = ![2,924,42240,4928,45056] t :=
    orthogonalClass_monomial_orbit_card i j hij t x
  rw [hc] at h
  fin_cases t <;> norm_num at h ⊢ <;> omega

/-- Sixteen subset sums only; no geometric orbit enumeration. -/
theorem co2_block_arithmetic (S : Finset (Fin 4))
    (h : 1 + ∑ i ∈ S, (![462,2464,21120,22528] i : ℕ) ∣ 46575) :
    S = ∅ ∨ S = Finset.univ := by
  have hc : ∀ T : Finset (Fin 4),
      1 + ∑ i ∈ T, (![462,2464,21120,22528] i : ℕ) ∣ 46575 →
      T = ∅ ∨ T = Finset.univ := by decide
  exact hc S h

end Atlas.Conway
