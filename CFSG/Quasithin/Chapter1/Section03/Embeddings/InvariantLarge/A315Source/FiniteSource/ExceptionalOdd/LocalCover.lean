module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.ProductCore
public import Theory.GroupTheory.QuasithinBasic

/-!
# The Sylow-local consumer of the nontrivial two-core

The actual product lies in a maximal two-local. Sylow conjugacy aligns this
overgroup with a given intrinsic catalogue, preserving its prime-square divisor.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511;
GLS3 Table 5.3m for the actual HS local normalizers.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
variable {G : Type*} [Group G] [Finite G]

theorem no_pair_of_twoCore_of_local_cover {p : ℕ}
    (T : Sylow 2 G)
    (hcover : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      ¬ p ^ 2 ∣ Nat.card M)
    (B : Subgroup G) (S : Sylow 2 G) (hB : XiOddQuotient p B)
    (hcore : pCore 2 (B ⊔ (S : Subgroup G) : Subgroup G) ≠ ⊥) : False := by
  obtain ⟨M,hM,hBS⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot _ hcore
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  let e := MulAut.conj g
  have hST : (S : Subgroup G).map e.toMonoidHom = T := by
    change ((g • S : Sylow 2 G) : Subgroup G) = _
    rw [hg]
  have hTM : (T : Subgroup G) ≤ M.map e.toMonoidHom := by
    rw [← hST]
    exact map_mono (le_sup_right.trans hBS)
  apply hcover _ (Theory.GroupTheory.isMaximalTwoLocal_map e hM) hTM
  rw [card_map_of_injective e.injective]
  exact (prime_square_dvd_complement hB).trans (card_dvd_of_le (le_sup_left.trans hBS))

theorem no_exceptional_pair_of_local_cover {p : ℕ} [Fact p.Prime]
    (hp : p = 5 ∨ p = 7 ∨ p = 11) (T : Sylow 2 G)
    (hT : 256 ∣ Nat.card T)
    (hcover : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      ¬ p ^ 2 ∣ Nat.card M)
    (B : Subgroup G) (S : Sylow 2 G) (hB : XiOddQuotient p B)
    (hperm : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G)) : False := by
  apply no_pair_of_twoCore_of_local_cover T hcover B S hB
  apply product_twoCore_ne_bot_of_exceptional_prime hp B S hB S.isPGroup' hperm
  rwa [Nat.card_congr (S.equiv T).toEquiv]
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
