module

public import CFSG.Quasithin.Chapter6.Defs
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import CFSG.Quasithin.Chapter6.Section01.EscapeDefs
public import Theory.Representation.BinaryEightPrimeObstruction

/-!
# Reducing `L₂(2ⁿ)` to `L₂(4)`

The legacy `ReductionCertificate` supplies the natural-layer conclusion,
centralizer triviality, unproved field bounds, and arbitrary subgroups called
`W₀` and `W₁`. Its arithmetic assembly is valid as a conditional helper,
but does not establish source Theorem 6.1.27. In particular the source uses
`N_G(W₀(T,V_L))`, whereas the legacy conclusion tests `W₀` itself.
Public names and statements are retained for compatibility.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed
pp.663–679 (including the terminal proof on PDF page 696).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Chapter6.Section01

open Subgroup

variable {G : Type*} [Group G] [Finite G]

abbrev VL (h : Hypothesis61 (G := G)) : Subgroup G := ⁅h.V, h.L⁆

abbrev TL (h : Hypothesis61 (G := G)) : Subgroup G :=
  (h.T : Subgroup G) ⊓ h.L

abbrev ZS (h : Hypothesis61 (G := G)) : Subgroup G :=
  VL h ⊓ centralizer (TL h : Set G)

/-- Extra premises for the legacy conditional assembly. No construction of
this record from Hypothesis 6.1.1 has been proved. Its subgroup fields are
arbitrary and do not define the book's weak closures. -/
public structure ReductionCertificate (h : Hypothesis61 (G := G)) where
  natural_layer : IsNaturalL2Layer h.L (VL h) h.n
  centralizer_trivial : (h.T : Subgroup G) ⊓ centralizer (h.L : Set G) = ⊥
  n_even : Even h.n
  n_le_four : h.n ≤ 4
  n_ne_four : h.n ≠ 4
  /- These supplied arithmetic premises do not construct the chief factor
  or prove the representation bounds used in the source's final paragraph. -/
  exceptional_prime : ¬ centralizer (ZS h : Set G) ≤ h.M →
    ∃ p : ℕ, p = 11 ∨ p = 13
  exceptional_dimension : ¬ centralizer (ZS h : Set G) ≤ h.M →
    ∀ p : ℕ, (p = 11 ∨ p = 13) → 19 ≤ p
  W₀ : Subgroup G
  W₁ : Subgroup G
  weak_closure_escape : W₀ ≤ h.M → ¬ W₁ ≤
    (h.T : Subgroup G) ⊓ centralizer (ZS h : Set G)

namespace ReductionCertificate

variable {h : Hypothesis61 (G := G)} (c : ReductionCertificate h)

omit [Finite G] in
public theorem n_eq_two (c : ReductionCertificate h) : h.n = 2 := by
  have hnlow : 1 < h.n := h.n_gt_one
  rcases c.n_even with ⟨k, hk⟩
  have hle := c.n_le_four
  have hne := c.n_ne_four
  omega

omit [Finite G] in
public theorem centralizer_in_M (c : ReductionCertificate h) : centralizer (ZS h : Set G) ≤ h.M := by
  by_contra hnot
  obtain ⟨p, hp⟩ := c.exceptional_prime hnot
  have hdim := c.exceptional_dimension hnot p hp
  omega

omit [Finite G] in
public theorem weak_closure_alternative (c : ReductionCertificate h) :
    ¬ c.W₀ ≤ h.M ∨ ¬ c.W₁ ≤
      (h.T : Subgroup G) ⊓ centralizer (ZS h : Set G) := by
  by_cases hw : c.W₀ ≤ h.M
  · exact Or.inr (c.weak_closure_escape hw)
  · exact Or.inl hw

omit [Finite G] in
public theorem natural_layer_at_four (c : ReductionCertificate h) :
    IsNaturalL2Layer h.L (VL h) 2 := by
  rw [← n_eq_two c]
  exact c.natural_layer

end ReductionCertificate

/-- Legacy conditional assembly, not source Theorem 6.1.27. -/
theorem theorem_6_1_27
    {h : Hypothesis61 (G := G)} (c : ReductionCertificate h) :
    h.n = 2 ∧
      IsNaturalL2Layer h.L (VL h) 2 ∧
      (h.T : Subgroup G) ⊓ centralizer (h.L : Set G) = ⊥ ∧
      centralizer (ZS h : Set G) ≤ h.M ∧
      (¬ c.W₀ ≤ h.M ∨ ¬ c.W₁ ≤
        (h.T : Subgroup G) ⊓ centralizer (ZS h : Set G)) := by
  refine ⟨ReductionCertificate.n_eq_two c,
    ReductionCertificate.natural_layer_at_four c, c.centralizer_trivial,
    ReductionCertificate.centralizer_in_M c,
    ReductionCertificate.weak_closure_alternative c⟩

/-- Compatibility alias for the legacy conditional assembly. -/
theorem lemma_6_1_27
    {h : Hypothesis61 (G := G)} (c : ReductionCertificate h) :
    h.n = 2 ∧
      IsNaturalL2Layer h.L (VL h) 2 ∧
      (h.T : Subgroup G) ⊓ centralizer (h.L : Set G) = ⊥ ∧
      centralizer (ZS h : Set G) ≤ h.M ∧
      (¬ c.W₀ ≤ h.M ∨ ¬ c.W₁ ≤
        (h.T : Subgroup G) ⊓ centralizer (ZS h : Set G)) :=
  theorem_6_1_27 c

end CFSG.Quasithin.Chapter6.Section01

end
