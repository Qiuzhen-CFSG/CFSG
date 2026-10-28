module
public import ABG.Recognition.ThreeCharacterTheory

/-!
# Initial character consequences for Wong's order-7920 branch

The order selects the degree vector of the supplied seven-character catalog.
Every other nontrivial irreducible has positive degree divisible by sixteen,
so every nontrivial irreducible has degree at least ten. The only characters
of degree ten are the first, third and fourth members of this same catalog.
The first character's values on the five local root classes are computed
from the actual GL₂(3) table.

These are the initial character inputs to the subgroup and permutation-action
construction in Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Appendix, Theorem 6(a), pp.107–108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open BenderGlauberman Matrix.GeneralLinearGroup
open scoped BigOperators
noncomputable section

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

/-- The order-7920 branch selects the degrees of the supplied witnesses. -/
public theorem ThreeGlobalDegreeData.mathieu_degrees (hG : Nat.card G = 7920) :
    c.decomposition.degree = ![10,11,10,10,55,44,45] := by
  rcases c.degree_alternatives with h | h
  · exact h.1
  · omega

/-- The seven distinguished characters and the trivial character leave 512
in the sum of squared irreducible degrees. -/
public theorem ThreeGlobalDegreeData.mathieu_degree_square_remainder
    (hG : Nat.card G = 7920) :
    Nat.card G - (1 + ∑ i : Fin 7, c.decomposition.degree i ^ 2) = 512 := by
  rw [hG, c.mathieu_degrees hG]
  norm_num [Fin.sum_univ_succ]

/-- Outside the distinguished catalog, every nontrivial irreducible has
degree at least sixteen. -/
public theorem ThreeGlobalDegreeData.remaining_degree_ge_sixteen
    {θ : ClassFunction G} (hθ : IsIrreducibleCharacter θ) (h1 : θ ≠ 1)
    (hχ : ∀ i, θ ≠ c.decomposition.χ i) : 16 ≤ (θ 1).re := by
  obtain ⟨n, hn, hd⟩ := c.remaining_degree θ hθ h1 hχ
  have hp := irreducible_degree_ge_one hθ
  rw [hn] at hp ⊢
  have hnpos : 0 < n := by
    have : 1 ≤ n := by exact_mod_cast hp
    omega
  exact_mod_cast Nat.le_of_dvd hnpos hd

include c in
/-- The least possible nontrivial irreducible degree in this branch is ten. -/
public theorem ThreeGlobalDegreeData.mathieu_degree_ge_ten
    (hG : Nat.card G = 7920) {θ : ClassFunction G}
    (hθ : IsIrreducibleCharacter θ) (h1 : θ ≠ 1) : 10 ≤ (θ 1).re := by
  classical
  by_cases hχ : ∃ i, θ = c.decomposition.χ i
  · obtain ⟨i, rfl⟩ := hχ
    rw [c.decomposition.degree_eq, c.mathieu_degrees hG]
    fin_cases i <;> norm_num [Matrix.cons_val]
  · have h := c.remaining_degree_ge_sixteen hθ h1 (by simpa using hχ)
    linarith

/-- There are exactly three choices for a degree-ten irreducible, all in
the original seven-character catalog. -/
public theorem ThreeGlobalDegreeData.mathieu_degree_ten_iff
    (hG : Nat.card G = 7920) {θ : ClassFunction G}
    (hθ : IsIrreducibleCharacter θ) :
    θ 1 = 10 ↔ θ = c.decomposition.χ 0 ∨
      θ = c.decomposition.χ 2 ∨ θ = c.decomposition.χ 3 := by
  classical
  constructor
  · intro hd
    have h1 : θ ≠ 1 := by intro h; simp [h] at hd
    have hχ : ∃ i, θ = c.decomposition.χ i := by
      by_contra hn
      have h := c.remaining_degree_ge_sixteen hθ h1 (by simpa using hn)
      norm_num [hd] at h
    obtain ⟨i, rfl⟩ := hχ
    rw [c.decomposition.degree_eq, c.mathieu_degrees hG] at hd
    fin_cases i <;> simp_all [Matrix.cons_val]
  · rintro (rfl | rfl | rfl) <;>
      rw [c.decomposition.degree_eq, c.mathieu_degrees hG] <;>
      change (10 : ℂ) = 10 <;> rfl

/-- The first character on the five root classes in the supplied centralizer.
The unused entries of the displayed vector are zero and make no assertion
about the complementary classes. -/
public theorem ThreeGlobalDegreeData.first_root_class_values
    (j : Fin 8) (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7) :
    c.decomposition.χ 0
      ((threeCentralizerEquiv c.involution c.centralizerEquiv).symm (threeClassRepr j)) =
      (![0,2,2,0,-1,0,0,0] j : ℂ) := by
  have ha : c.involution ∈ Subgroup.zpowers
      (((threeCentralizerEquiv c.involution c.centralizerEquiv).symm
        (threeClassRepr j)) : G) := by
    apply (threeCentralizerEquiv_root_iff c.involution c.order_involution
      c.centralizerEquiv _).mp
    simpa only [MulEquiv.apply_symm_apply] using
      (glTwoThreeRootSupport_class j).mpr hj
  rw [c.first_restriction _ ha]
  simp only [threeCentralizerCharacter_values]
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · change (1 : ℂ) - 3 - (-2) - (-2) = 2
    norm_num
  · change (1 : ℂ) - (-1) - 0 - 0 = 2
    norm_num
  · change (1 : ℂ) - 0 - 1 - 1 = -1
    norm_num
  · change (1 : ℂ) - 1 - glTwoThreeOmega - (-glTwoThreeOmega) = 0
    ring
  · change (1 : ℂ) - 1 - (-glTwoThreeOmega) - glTwoThreeOmega = 0
    ring

end
end ABG
