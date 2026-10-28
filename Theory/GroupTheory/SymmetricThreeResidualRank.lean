module
public import Theory.GroupTheory.SymmetricThreeFactorSelection
public import Theory.GroupTheory.NormalSymmetricThreeMarked
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Selecting one Thompson factor from the odd residual intersection

In ambient three-rank at most two, a two-perfect {2,3}-subgroup lies
inside any normal S₃ × S₃ subgroup. If it is disjoint from that subgroup's
odd residual, it is trivial. Thus a nontrivial actor disjoint from the odd
residual selects the S₃ alternative. The residual cubic commutes with the
actor, so their independent ranks bound the actor's three-rank by one.

Chapter13's CoveredResidual applies this to L₁ after lifting its actual
intersection and applying the earlier 13.3.9 source classification.
Source: Aschbacher–Smith 13.4.8, printed p.905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.SymmetricThreeCubicNormality
variable {G : Type*} [Group G] [Finite G]
local notation "S3" => Equiv.Perm (Fin 3)

/-- A nontrivial residual-disjoint actor selects one factor and has three-rank at most one. -/
theorem single_and_rank_of_residual_disjoint (I B : Subgroup G) [I.Normal]
    (hm : Nonempty (I ≃* S3) ∨ Nonempty (I ≃* (S3 × S3)))
    (hB : IsPPerfect 2 B) (hne : B ≠ ⊥)
    (horder : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n)
    (hrank : primeRank 3 G ≤ 2)
    (hd : Disjoint ((pResidual 2 I).map I.subtype) B) :
    Nonempty (I ≃* S3) ∧ primeRank 3 B ≤ 1 := by
  have he : Nonempty (I ≃* S3) := by
    rcases hm with he | he
    · exact he
    obtain ⟨e⟩ := he
    have hBI := NormalSymmetricThreePairRank.le_pair_of_twoPerfect I e B hB hrank horder
    have hBR : B ≤ (pResidual 2 I).map I.subtype := by
      have hh := embedded_pResidual_mono 2 hBI
      rwa [(pResidual_eq_top_iff 2 B).mpr hB,← MonoidHom.range_eq_map,range_subtype] at hh
    exact (hne (disjoint_self.mp (hd.mono_left hBR))).elim
  obtain ⟨e⟩ := he
  exact ⟨⟨e⟩,NormalSymmetricThreeMarked.rank_le_one_of_disjoint_cubic
    ((pResidual 2 I).map I.subtype) B (NormalSymmetricThreeMarked.residual_card I e)
    (NormalSymmetricThreeMarked.centralizes_residual I e B hB) (disjoint_iff.mp hd) hrank⟩
end Theory.GroupTheory.SymmetricThreeCubicNormality
