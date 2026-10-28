module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeHallRank

/-!
# Fermat actors in the degree-eight Cartan

The degree-eight left Cartan has order 255. Its prime factors 3, 5 and 17
all have two-group automorphism groups. The odd right Hall subgroup therefore
centralizes each such actor. A zero-core actor is disjoint from that Hall
subgroup, so quasithinness bounds its prime rank, and the rank of the literal
overlap, by one. This includes the order-seventeen factor not represented by
the source's later cubic/quintic actor contract.

Source: Aschbacher–Smith 5.1.6(4) and 5.2.2, printed pp.632–633,647–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The odd right Hall group fixes each prime-order actor occurring in degree eight. -/
theorem CartanPair.centralizes_fermat_actor {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hp : p = 3 ∨ p = 5 ∨ p = 17) (hDA : D ≤ A) (hcard : Nat.card D = p) :
    B ≤ centralizer (D : Set G) := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  let : IsCyclic D := isCyclic_of_prime_card hcard
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let f := D.normalizerMonoidHom.comp (inclusion (c.right_normalizes_left.trans
    (normalizer_le_normalizer_of_le_cyclic D A hDA)))
  have ho : Odd (Nat.card B) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hc : Nat.Coprime (Nat.card B) (Nat.card (MulAut D)) := by
    rw [IsCyclic.card_mulAut, hcard]
    rcases hp with rfl | rfl | rfl
    · rw [show Nat.totient 3 = 2 by decide]
      exact Nat.coprime_two_right.mpr ho
    · rw [show Nat.totient 5 = 2 ^ 2 by decide]
      exact (Nat.coprime_two_right.mpr ho).pow_right 2
    · rw [show Nat.totient 17 = 2 ^ 4 by decide]
      exact (Nat.coprime_two_right.mpr ho).pow_right 4
  have hc1 : Nat.card f.range = 1 := Nat.eq_one_of_dvd_coprimes hc
    (card_range_dvd f) f.range.card_subgroup_dvd_card
  have hf (b : B) : f b = 1 :=
    mem_bot.mp ((f.range.eq_bot_of_card_eq hc1) ▸ (show f b ∈ f.range from ⟨b,rfl⟩))
  intro b hb d hd
  have he := congrArg (fun z : MulAut D => (z (⟨d,hd⟩ : D) : G)) (hf ⟨b,hb⟩)
  change b * d * b⁻¹ = d at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

omit [Finite G] in
/-- A zero-core actor meets the right Hall group trivially, since B lies in H. -/
private theorem fermat_disjoint_right_cartan
    {T : Sylow 2 G} {L H A B D : Subgroup G} {p : ℕ}
    (hp : p = 3 ∨ p = 5 ∨ p = 17) (hcard : Nat.card D = p) (c : CartanPair T L H A B)
    (hzero : (D ⊔ H).pCoreIn 2 = ⊥) (hH : H.pCoreIn 2 ≠ ⊥) : Disjoint D B := by
  have hprime : (Nat.card D).Prime := by
    rw [hcard]
    rcases hp with rfl | rfl | rfl <;> decide
  let : Fact (Nat.card D).Prime := ⟨hprime⟩
  rcases (B.subgroupOf D).eq_bot_or_eq_top_of_prime_card with hb | ht
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hx' : (⟨x,hx.1⟩ : D) ∈ B.subgroupOf D := hx.2
    rw [hb] at hx'
    exact congrArg Subtype.val (mem_bot.mp hx')
  · have hDB := subgroupOf_eq_top.mp ht
    have hDH := hDB.trans (c.right_le.trans inf_le_right)
    exact (hH (by simpa only [sup_eq_right.mpr hDH] using hzero)).elim

/-- An escaping prime actor leaves at most one p-direction in the actual right Hall group. -/
theorem CartanPair.right_fermatRank_le_one {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hp : p = 3 ∨ p = 5 ∨ p = 17) (hDA : D ≤ A) (hcard : Nat.card D = p)
    (hzero : (D ⊔ H).pCoreIn 2 = ⊥) (hH : H.pCoreIn 2 ≠ ⊥) :
    primeRank p B ≤ 1 := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  have ho : Odd p := by rcases hp with rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  let : IsCyclic D := isCyclic_of_prime_card hcard
  let : CommGroup D := IsMulCommutative.instCommGroup
  have hrD : 1 ≤ primeRank p D := primeRank_ge_of_elementary_embedding
    (fun x : D => by simpa only [hcard] using pow_card_eq_one' (x := x))
    (by simpa using hcard) (MonoidHom.id D) Function.injective_id
  have he := D.primeRank_sup_eq_add_of_disjoint_commuting B
    (fermat_disjoint_right_cartan hp hcard c hzero hH)
    (le_centralizer_iff.mp (c.centralizes_fermat_actor h hp hDA hcard)) p
  have hJM : D ⊔ B ≤ normalizer (L : Set G) := sup_le
    ((hDA.trans c.left_le).trans (inf_le_left.trans L.le_normalizer))
    (c.right_le.trans inf_le_left)
  have hl := primeRank_mono p hJM
  have hu := isQuasithin_iff_twoLocal.mp h.qtke.quasithin
    (normalizer (L : Set G)) h.maximal.1 p hprime ho
  omega

/-- The Hall index is prime to p, so the same bound holds on the literal overlap. -/
theorem CartanPair.overlap_fermatRank_le_one {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hp : p = 3 ∨ p = 5 ∨ p = 17) (hDA : D ≤ A) (hcard : Nat.card D = p)
    (hzero : (D ⊔ H).pCoreIn 2 = ⊥) (hH : H.pCoreIn 2 ≠ ⊥) :
    primeRank p (normalizer (L : Set G) ⊓ H : Subgroup G) ≤ 1 := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have hne : p ≠ 2 := by rcases hp with rfl | rfl | rfl <;> decide
  have hi : ¬ p ∣ (B.subgroupOf (normalizer (L : Set G) ⊓ H)).index := by
    intro hi
    exact c.right_hall.p_in_pi_of_p_dvd_index ⟨p,hprime⟩ hi hne
  rw [← (B.subgroupOf (normalizer (L : Set G) ⊓ H)).primeRank_eq_of_not_dvd_index hi,
    primeRank_equiv p (subgroupOfEquivOfLe c.right_le)]
  exact c.right_fermatRank_le_one h hp hDA hcard hzero hH
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
