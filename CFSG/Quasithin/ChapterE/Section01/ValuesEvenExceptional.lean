module

public import CFSG.Quasithin.ChapterE.Section01.Basic

/-!
# Lower-bound assembly for the exceptional even-characteristic values

E.1.14(1)--(2) of Aschbacher--Smith, *The Classification of Quasithin
Groups*, printed p.214, asserts values for the whole group `G = F*(G) T`,
not just its simple generalized Fitting subgroup. The exceptional values are
the field exponent for Suzuki, derived Ree-four and derived G₂ groups, and
three times that exponent for the genuine graph-field triality group.

The lemmas here give the lower-bound step needed in those calculations. A
conjugation-invariant elementary family obstructs generation if its weak-closure
normalizer and every eligible E-member lie in one proper subgroup. Monotonicity
then excludes every smaller positive bound from a single predecessor-bound
obstruction. Together with an independently proved upper generation bound this
determines the minimum, including the separate value-one endpoint.

These are conditional assembly lemmas, not proofs of the exceptional values.
The concrete families, proper subgroups and upper generation proofs must still
be constructed from actual model equivalences and the source hypotheses.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A proper overgroup containing the normalizer and all eligible E-members
prevents E-generation at the specified Sylow subgroup. -/
theorem not_isEGeneratedAt_of_confined_members {i : ℕ} (T : Sylow 2 G)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (M : Subgroup G) (hM : M ≠ ⊤)
    (hnorm : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M)
    (hmembers : ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
      ∀ K : Subgroup G, IsEMemberAt i (T : Subgroup G) A K → K ≤ M) :
    ¬ IsEGeneratedAt i T := by
  intro hgen
  obtain ⟨A, hA, hAT, K, hK, hKM⟩ :=
    hgen.exists_member_not_le Ω hΩ M hM hnorm
  exact hKM (hmembers A hA hAT K hK)

/-- A concrete obstruction at one Sylow subgroup excludes every smaller bound.
No conjugacy transfer or assertion about a simple model alone is used. -/
theorem not_isEGenerated_of_confined_members {i j : ℕ} (hji : j ≤ i)
    (T : Sylow 2 G) (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (M : Subgroup G) (hM : M ≠ ⊤)
    (hnorm : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M)
    (hmembers : ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
      ∀ K : Subgroup G, IsEMemberAt i (T : Subgroup G) A K → K ≤ M) :
    ¬ IsEGenerated j G := by
  intro hgen
  exact not_isEGeneratedAt_of_confined_members T Ω hΩ M hM hnorm hmembers
    ((hgen T).mono hji)

/-- The value-one endpoint needs an upper generation proof and even order;
the infimum convention alone supplies no positivity. -/
theorem generationParameter_eq_one_of_upper
    (heven : ¬ Odd (Nat.card G)) (hupper : IsEGenerated 1 G) :
    generationParameter G = 1 := by
  have hpos := (generationParameter_spec heven ⟨1, by omega, hupper⟩).1
  have hle := generationParameter_le (by omega : 0 < 1) hupper
  omega

/-- Determine a positive bound from genuine upper generation and a concrete
proper-subgroup obstruction at its predecessor. All witnesses concern `G`,
so callers must also handle its almost-simple outer 2-extension. -/
theorem generationParameter_eq_of_confined_members {n : ℕ} (hn : 0 < n)
    (heven : ¬ Odd (Nat.card G)) (hupper : IsEGenerated n G)
    (T : Sylow 2 G) (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (M : Subgroup G) (hM : M ≠ ⊤)
    (hnorm : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M)
    (hmembers : ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
      ∀ K : Subgroup G, IsEMemberAt (n - 1) (T : Subgroup G) A K → K ≤ M) :
    generationParameter G = n := by
  have hspec := generationParameter_spec heven ⟨n, hn, hupper⟩
  apply Nat.le_antisymm (generationParameter_le hn hupper)
  by_contra h
  have hle : generationParameter G ≤ n - 1 := by omega
  exact not_isEGenerated_of_confined_members hle T Ω hΩ M hM hnorm hmembers
    hspec.2

end CFSG.Quasithin.ChapterE.ExceptionalValues
