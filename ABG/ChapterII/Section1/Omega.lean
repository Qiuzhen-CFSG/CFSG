module
public import ABG.ChapterII.Section1.OmegaIdentification
public import ABG.ChapterII.Section1.MaximalModels

/-!
# The dihedral first omega subgroup

For a semidihedral presentation of order `2^n`, with `n ≥ 4`, the subgroup
`omega₁ (G := G) (p := 2)` is dihedral of order `2^(n-1)`. The proof uses
the exact identification with `⟨a²,b⟩` from `OmegaIdentification`, then
imports that subgroup's standard dihedral model and index-two formula
from `MaximalModels`.

This assembles ABG Chapter II, §1, Lemma 1(vi), article page 9 of
`refs/latex/alperin-brauer-gorenstein.tex`. The explicit order parameter is
Stellmacher's, one larger than the article's parameter.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
/-- The first omega subgroup is dihedral of half the ambient order (ABG II.1.1(vi)). -/
public theorem omega_one_dihedral {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (hcard : Nat.card G = 2 ^ n) (ha : orderOf a = 2 ^ (n - 1))
    (hb : orderOf b = 2) (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Stellmacher.IsDihedralGroup (omega₁ (G := G) (p := 2)) ∧
      Nat.card (omega₁ (G := G) (p := 2)) = 2 ^ (n - 1) := by
  rw [omega_one_eq hn a b ha hb hconj hgen]
  obtain ⟨_, hindex, _, _, hmodel, _⟩ := explicit_subgroup_models hn a b hcard ha hb hconj hgen
  refine ⟨⟨2 ^ (n - 2), hmodel⟩, ?_⟩
  have hh := (Subgroup.closure ({a ^ 2, b} : Set G)).card_mul_index
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hindex, hcard, hpow] at hh
  omega
end ABG.QuasiDihedral
