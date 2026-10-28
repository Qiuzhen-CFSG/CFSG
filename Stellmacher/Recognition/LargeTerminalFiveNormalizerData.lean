module

public import Stellmacher.Recognition.LargeTerminalFiveLocalAutomorphisms
public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Theory.GroupTheory.FiveSquaringPowers

/-!
# The small local five-normalizer and its squaring elements

Write P for the second local group, Q for its two-core and A for an
order-five subgroup. Inside Q, normalizing A is equivalent to centralizing
A, because their orders are coprime. When C_Q(A) has order four, the
normalizer in P therefore has order dividing 80. Its full order-four
automizer bounds the local centralizer by twenty.

The fifth power of the existing squaring element is a two-element, still
inducing squaring. Its order is 4, 8 or 16. This is a reduction of the
order-four lifting problem, not a splitting assertion.

Source: Thompson VI, pp.629–630; the full local automizer is proved in
`LargeTerminalFiveLocalAutomorphisms`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- The actual local five-normalizer has order dividing eighty. -/
public theorem LargeTerminalContext.five_local_normalizer_card_dvd_eighty
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hfixed : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4) :
    Nat.card (ctx.second ⊓ normalizer (A : Set G) : Subgroup G) ∣ 80 := by
  let M := ctx.second
  let Q := twoCoreIn M
  let N := M ⊓ normalizer (A : Set G)
  let C := centralizer (A : Set G)
  have hQp : IsPGroup 2 Q := pCore_isPGroup.map M.subtype
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hd : Disjoint Q A := hQp.disjoint_of_coprime hAp (by decide)
  have hAQ : A ≤ normalizer (Q : Set G) := hAP.trans
    ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le M)).mp (twoCoreIn_normal M))
  have hQN : Q ⊓ N = Q ⊓ C := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      rw [← commutator_eq_bot_iff_le_centralizer]
      apply bot_unique
      apply le_trans _ hd.le_bot
      exact le_inf ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hAQ))
        (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans inf_le_right))
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans (twoCoreIn_le M))
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
  have hQNcard : Nat.card (Q.subgroupOf N) = 4 := by
    rw [← card_map_of_injective N.subtype_injective, subgroupOf_map_subtype,
      hQN, inf_comm]
    rw [← card_map_of_injective Q.subtype_injective, subgroupOf_map_subtype] at hfixed
    exact hfixed
  have hQcard : Nat.card Q = 1024 := by
    obtain ⟨z, _, _, hcore, hc⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
    change Nat.card (twoCoreIn ctx.second) = 1024
    rw [← hcore]
    exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans hc
  have hQindex : Q.relIndex M = 20 := by
    have hc := (Q.subgroupOf M).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (twoCoreIn_le M)).toEquiv, hQcard,
      ctx.second_card_of_large_card hS] at hc
    change 1024 * Q.relIndex M = 20480 at hc
    omega
  have hindex : Q.relIndex N ∣ 20 := by
    let _ : (Q.subgroupOf M).Normal := twoCoreIn_normal M
    have hd := relIndex_dvd_index_of_normal (Q.subgroupOf M) (N.subgroupOf M)
    rw [relIndex_subgroupOf (show N ≤ M from inf_le_left)] at hd
    exact hQindex ▸ hd
  have hc := (Q.subgroupOf N).card_mul_index
  rw [hQNcard] at hc
  change 4 * Q.relIndex N = Nat.card N at hc
  change Nat.card N ∣ 80
  rw [← hc]
  exact Nat.mul_dvd_mul_left 4 hindex

/-- The full order-four automizer and the normalizer bound give a local
five-centralizer of order at most twenty, without ambient confinement. -/
public theorem LargeTerminalContext.five_local_centralizer_card_le_twenty
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4) :
    Nat.card (ctx.second ⊓ centralizer (A : Set G) : Subgroup G) ≤ 20 := by
  let N := ctx.second ⊓ normalizer (A : Set G)
  let C := ctx.second ⊓ centralizer (A : Set G)
  let f : N →* MulAut A := A.normalizerMonoidHom.comp (inclusion inf_le_right)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨b, hb⟩ := ctx.five_local_automorphisms_surjective hS A hA hAP a
    exact ⟨⟨b, b.property, b.val.property⟩, hb⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  have hi : f.ker.index = 4 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top, IsCyclic.card_mulAut, hA]
    decide
  have hn : Nat.card N ≤ 80 := Nat.le_of_dvd (by decide)
    (ctx.five_local_normalizer_card_dvd_eighty hS A hA hAP hcard)
  have hk := f.ker.card_mul_index
  rw [hi] at hk
  let j : C → f.ker := fun c => ⟨⟨c, c.property.1,
      Subgroup.centralizer_le_normalizer _ c.property.2⟩, by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change (c : G) * a * (c : G)⁻¹ = (a : G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp c.property.2 a a.property).symm⟩
  have hj : Function.Injective j := by
    intro c d h
    exact Subtype.ext (congrArg (fun x : f.ker => ((x : N) : G)) h)
  have hc := Nat.card_le_card_of_injective j hj
  change Nat.card C ≤ 20
  omega

/-- Removing the odd part gives an actual squaring element of order at most
sixteen. Orders eight and sixteen remain to be excluded by local geometry. -/
public theorem LargeTerminalContext.exists_two_power_five_squaring_element
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hfixed : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4) :
    ∃ b : G, b ∈ ctx.second ∧ b ∈ normalizer (A : Set G) ∧
      (orderOf b = 4 ∨ orderOf b = 8 ∨ orderOf b = 16) ∧
      ∀ c ∈ A, b * c * b⁻¹ = c ^ 2 := by
  obtain ⟨a, haP, haN, ha⟩ := ctx.exists_five_squaring_element hS A hA hAP
  let b := a ^ 5
  have hbP : b ∈ ctx.second := pow_mem haP 5
  have hbN : b ∈ normalizer (A : Set G) := pow_mem haN 5
  have hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2 := fifth_power_squares_five A hA a ha
  have hb4096 : b ^ 4096 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨a, haP⟩ : ctx.second))
    rw [ctx.second_card_of_large_card hS] at hh
    change (a ^ 5) ^ 4096 = 1
    rw [← pow_mul]
    exact congrArg Subtype.val hh
  have hd80 : orderOf b ∣ 80 := by
    have hd := orderOf_dvd_natCard
      (⟨b, hbP, hbN⟩ : (ctx.second ⊓ normalizer (A : Set G) : Subgroup G))
    rw [← Subgroup.orderOf_coe] at hd
    exact hd.trans (ctx.five_local_normalizer_card_dvd_eighty hS A hA hAP hfixed)
  have hd16 : orderOf b ∣ 16 := by
    have hh := Nat.dvd_gcd hd80 (orderOf_dvd_of_pow_eq_one hb4096)
    exact hh
  have hne := square_ne_one_of_squares_five A hA b hb
  have hcases : orderOf b = 4 ∨ orderOf b = 8 ∨ orderOf b = 16 := by
    have hsmall : orderOf b ≠ 1 ∧ orderOf b ≠ 2 := by
      constructor
      · intro he
        exact hne (orderOf_dvd_iff_pow_eq_one.mp (he ▸ one_dvd 2))
      · intro he
        exact hne (he ▸ pow_orderOf_eq_one b)
    have hle := Nat.le_of_dvd (by decide : 0 < 16) hd16
    have hpos := orderOf_pos b
    interval_cases h : orderOf b <;> norm_num at *
  exact ⟨b, hbP, hbN, hcases, hb⟩

end Stellmacher.Recognition
