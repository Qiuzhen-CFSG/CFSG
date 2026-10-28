module

public import Theory.GroupTheory.PerfectSmallNormalizer

/-!
# The native core normalizes the perfect original Held actor

The original elementary16 lies in both the perfect actor and the solvable
core of order64. The actor normalizer therefore has relative index at most
four in the core. The small-normalizer theorem makes the actor normal in
their join, hence normalized by the whole core.

This order argument retains both subgroups and does not require a catalogue
of A5 embeddings or a module restriction certificate.
Source: the Held row of Aschbacher--Smith C.3.1 and12.7.5, pp.151 and840.
-/

public section
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A common subgroup of order16 makes the actual solvable64 core normalize
the perfect actor that already normalizes that core. -/
theorem held_core_normalizes_perfect_actor
    (B Q E : Subgroup G) [Group.IsPerfect B] [Group.IsSolvable Q]
    (hBQ : B ≤ normalizer (Q : Set G)) (hEB : E ≤ B) (hEQ : E ≤ Q)
    (hQ : Nat.card Q = 64) (hE : Nat.card E = 16) :
    Q ≤ normalizer (B : Set G) := by
  have hi : E.relIndex Q = 4 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) E Q bot_le hEQ
    simp only [relIndex_bot_left,hE,hQ] at hh
    omega
  have hN : (normalizer (B : Set G)).relIndex Q ≤ 4 := by
    rw [←hi]
    exact relIndex_le_of_le_left (hEB.trans B.le_normalizer) index_ne_zero_of_finite
  have hn := normal_in_sup_of_perfect_of_solvable_of_small_normalizer B Q hBQ hN
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    (show B ≤ B ⊔ Q from le_sup_left)).mp hn)

end CFSG.Quasithin.ChapterC.OrdinaryPlacement
