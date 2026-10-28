module
public import Theory.GroupTheory.SymmetricThreeSylowNormalizer
public import Theory.GroupTheory.NormalSymmetricThreePairRank.TwoPerfect

/-!
# Selecting one symmetric-three factor with the original Sylow

In a finite group of three-rank at most two, a two-perfect {2,3}-actor
lies in any normal symmetric-three pair. If it also normalizes the
specified Sylow two-subgroup, self-normalization puts it in that
Sylow; two-perfectness then makes it trivial. Thus a nontrivial such
actor selects the single-factor alternative of a normal S₃ or S₃×S₃ span.
The proof keeps the actual ambient subgroup and its marked Sylow image.

Source: Aschbacher–Smith, the single-factor step of 13.4.8, printed p.905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace SymmetricThreeFactorSelection
local notation "S3" => Equiv.Perm (Fin 3)
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial two-perfect {2,3}-actor normalizing the marked Sylow excludes two factors. -/
theorem single_of_twoPerfect_actor
    (I J A : Subgroup G) [I.Normal]
    (hI : Nonempty (I ≃* S3) ∨ Nonempty (I ≃* (S3 × S3)))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = J)
    (hA : IsPPerfect 2 A) (hA1 : A ≠ ⊥)
    (horder : ∃ m n : ℕ, Nat.card A ∣ 2 ^ m * 3 ^ n)
    (hrank : primeRank 3 G ≤ 2) (hn : A ≤ normalizer (J : Set G)) :
    Nonempty (I ≃* S3) := by
  rcases hI with h | he
  · exact h
  obtain ⟨e⟩ := he
  have hAI := NormalSymmetricThreePairRank.le_pair_of_twoPerfect I e A hA hrank horder
  have hAP : A ≤ J := by
    intro a ha
    have haP : (⟨a, hAI ha⟩ : I) ∈ normalizer (P : Set I) := by
      have hJI : J ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
      have hJP : J.subgroupOf I = (P : Subgroup I) := by
        rw [← hP]
        ext x
        exact mem_map_iff_mem I.subtype_injective
      change (⟨a, hAI ha⟩ : I) ∈ normalizer ((P : Subgroup I) : Set I)
      rw [← hJP, ← subgroupOf_normalizer_eq hJI]
      exact hn ha
    rw [SymmetricThreeSylowNormalizer.of_models (Or.inr ⟨e⟩) P] at haP
    rw [← hP]
    exact mem_map_of_mem I.subtype haP
  have hp : IsPGroup 2 J := hP ▸ P.isPGroup'.map I.subtype
  have he := hA.hom_eq_one_of_isPGroup hp (inclusion hAP)
  apply (hA1 ?_).elim
  apply eq_bot_iff.mpr
  intro a ha
  have hh := DFunLike.congr_fun he (⟨a, ha⟩ : A)
  exact congrArg Subtype.val hh

end SymmetricThreeFactorSelection
