module

public import CFSG.Quasithin.ChapterE.Section01.Basic

/-!
# Assembly tools for the classical cases of E.1.14(1)

The source statement concerns a finite SQTK-group `G`, with `L = F*(G)`
simple and `G = LT` for a Sylow 2-subgroup `T`. Its classical alternatives
are PSL₂(2^f), PSU₃(2^f), PSL₃(2^f), and Sp₄(2^f)', with value `f`,
and PSL₄(2), PSL₅(2), with value one. The unitary matrix field has order
2^(2f). The derived subgroup in Sp₄(2)' must be retained.

This module proves only the common minimum and obstruction arguments, not
the model calculations. For `f > 1`, trap every E-member at rank `f - 1`
and the weak-closure normalizer in a proper subgroup. Monotonicity then
excludes every smaller positive generation bound. For value one, an upper
generation bound and even order suffice. Existence of the upper bound is
essential because the natural-number infimum of the empty set is zero.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.5--6 and E.1.14(1), printed pp.210--211, 214. The latter cites
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.7.
The concrete upper bounds and lower-obstruction witnesses remain to be proved.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A concrete proper overgroup traps the E-family and its normalizer,
so generation at this rank fails. -/
theorem not_isEGenerated_of_members_le {i : ℕ} (T : Sylow 2 G)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (M : Subgroup G) (hM : M ≠ ⊤)
    (hnorm : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M)
    (hmembers : ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
      ∀ K : Subgroup G, IsEMemberAt i (T : Subgroup G) A K → K ≤ M) :
    ¬ IsEGenerated i G := by
  intro hgen
  obtain ⟨A, hA, hAT, K, hK, hKM⟩ :=
    (hgen T).exists_member_not_le Ω hΩ M hM hnorm
  exact hKM (hmembers A hA hAT K hK)

/-- A positive upper bound and failure at its predecessor determine the
minimum. At value one no rank-zero failure is needed. -/
theorem parameter_eq_of_upper_and_predecessor {f : ℕ}
    (hf : 0 < f) (heven : ¬ Odd (Nat.card G))
    (hupper : IsEGenerated f G)
    (hlower : 1 < f → ¬ IsEGenerated (f - 1) G) :
    generationParameter G = f := by
  have hspec := generationParameter_spec heven ⟨f, hf, hupper⟩
  apply Nat.le_antisymm (generationParameter_le hf hupper)
  by_contra h
  have hlt : generationParameter G < f := Nat.lt_of_not_ge h
  have hf' : 1 < f := by omega
  exact hlower hf' (hspec.2.mono (by omega))

/-- The value-one cases require actual generation and even order. -/
theorem parameter_eq_one_of_upper (heven : ¬ Odd (Nat.card G))
    (hupper : IsEGenerated 1 G) : generationParameter G = 1 :=
  parameter_eq_of_upper_and_predecessor (by decide) heven hupper (by omega)

/-- Assembly from an upper bound and an explicit proper-subgroup obstruction.
The family and all trapping hypotheses must be supplied by the local model
calculation for the ambient extension `G`, not just for its simple subgroup. -/
theorem parameter_eq_of_upper_and_members_le {f : ℕ} (hf : 1 < f)
    (heven : ¬ Odd (Nat.card G)) (hupper : IsEGenerated f G)
    (T : Sylow 2 G) (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (M : Subgroup G) (hM : M ≠ ⊤)
    (hnorm : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M)
    (hmembers : ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
      ∀ K : Subgroup G, IsEMemberAt (f - 1) (T : Subgroup G) A K → K ≤ M) :
    generationParameter G = f :=
  parameter_eq_of_upper_and_predecessor (by omega) heven hupper
    (fun _ => not_isEGenerated_of_members_le T Ω hΩ M hM hnorm hmembers)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical
