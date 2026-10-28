module
public import Theory.GroupTheory.PrimeRankFixedJoin
/-!
# A central prime actor adds one rank

A centerless subgroup contains no nonidentity central actor of the ambient
group. Joining such an actor to an intrinsic elementary subgroup adds one
to the ambient prime rank. This is the rank step used in Aschbacher--Smith,
the secondary-centralizer inspection in 2.4.29, printed p.545.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem central_prime_actor_not_mem {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) (hZ : center K = ⊥) (u : G)
    (hu : u ∈ center G) (huo : orderOf u = p) : u ∉ K := by
  intro h
  have hz : (⟨u,h⟩ : K) ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (mem_center_iff.mp hu (k : G))
  rw [hZ] at hz
  have he : u = 1 := congrArg Subtype.val (mem_bot.mp hz)
  have hp := (Fact.out : p.Prime).one_lt
  rw [he,orderOf_one] at huo
  omega

theorem primeRank_ge_of_central_actor {p n : ℕ} [Fact p.Prime]
    (K : Subgroup G) (hZ : center K = ⊥)
    (E : Subgroup K) [IsElementaryAbelian p E] (hE : Nat.card E = p ^ n)
    (u : G) (hu : u ∈ center G) (huo : orderOf u = p) :
    n + 1 ≤ primeRank p G := by
  let B := E.map K.subtype
  let : IsElementaryAbelian p B := IsElementaryAbelian.map K.subtype
  have hnot : u ∉ B := fun h =>
    K.central_prime_actor_not_mem hZ u hu huo (map_subtype_le E h)
  have hfix : B ≤ centralizer ({u} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hu b)
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B u huo hnot hfix
    (by rw [card_map_of_injective K.subtype_injective,hE])
end Subgroup
