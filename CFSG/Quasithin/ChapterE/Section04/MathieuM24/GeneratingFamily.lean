module

public import CFSG.Quasithin.ChapterE.Section04.GenerationSetup
public import Theory.Mathieu.M24.ValueBoundParabolics.QuotientBounds

/-!
# Converting a symmetric-three triple to the E.4 generating family

Take the image of the three given overgroups as a finite family. Repetitions
can only decrease the budget. Each intrinsic two-core quotient has generalized
Fitting subgroup of prime order and two-rank at most one, so the budget is at
most three. No existence of the required overgroups is assumed implicitly.

Source: Aschbacher–Smith, E.4.2 and the M₂₄ case of E.4.3(2), printed
pp. 241–242 (PDF pp. 252–253).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound
variable {G : Type*} [Group G] [Finite G]

/-- Three proper generating Sylow overgroups with actual S₃ quotients give a family
whose intrinsic quotient-rank budget is at most three. The witnesses and
generation are inputs to this conversion, not asserted to exist here. -/
theorem generating_family_of_three_symmetric_quotients (T : Sylow 2 G) (P : Fin 3 → Subgroup G)
    (hT : ∀ i, (T : Subgroup G) ≤ P i) (hgen : ⨆ i, P i = ⊤)
    (hq : ∀ i, Nonempty ((P i ⧸ pCore 2 (P i)) ≃* Equiv.Perm (Fin 3)))
    (hproper : ∀ i, P i < ⊤) :
    ∃ Δ : Finset (Subgroup G), IsGeneratingFamily T Δ ∧ localRankBudget Δ ≤ 3 ∧
      ∀ H ∈ Δ, H < ⊤ := by
  classical
  let Δ := Finset.univ.image P
  have hmem (i : Fin 3) : P i ∈ Δ := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hrank : ∀ H ∈ Δ, primeRank 2 (H ⧸ pCore 2 H) ≤ 1 := by
    intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact (symmetricThree_generalizedFitting_card_and_primeRank (hq i).some).2
  refine ⟨Δ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact hT i
  · apply top_unique
    rw [← hgen]
    exact iSup_le fun i => le_sSup (hmem i)
  · intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    right
    rw [(symmetricThree_generalizedFitting_card_and_primeRank (hq i).some).1]
    decide
  · have hsum : localRankBudget Δ ≤ Δ.card := by
      calc
        localRankBudget Δ ≤ ∑ H ∈ Δ, 1 := Finset.sum_le_sum hrank
        _ = Δ.card := by simp
    exact hsum.trans (by simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := P)))

  · intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact hproper i

end CFSG.Quasithin.ChapterE.ValueBound
