module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalData
public import Theory.GroupTheory.PrimeOrderCentralizerSylow

/-!
# The two-part of the odd-prime centralizers

For an element of order three or five in `C_G(z)`, the common centralizer
with `z` has order `2p`. In the actual `A₅ × C₂` model, it suffices to
count the centralizers of one three-cycle and one five-cycle; Sylow
conjugacy transports the result to all elements of these orders.

Every ambient two-subgroup has exponent two. Thus a Sylow two-subgroup
of `C_G(x)` containing `z` lies in this common centralizer and has order
two. This prepares Burnside transfer in the full ambient centralizer,
without assuming the order or cyclicity of its odd complement.

Source: Bender, *Finite groups with large subgroups* (1974), §4, (4.1),
printed p.225, invoking the proof of Janko (1966), Lemma 3.1.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
private abbrev AF := alternatingGroup (Fin 5)
private abbrev M := AF × Multiplicative (ZMod 2)
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def repThree : AF :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by change Equiv.Perm.sign _ = 1; decide⟩
private def repFive : AF :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4, by change Equiv.Perm.sign _ = 1; decide⟩
private theorem repThree_order : orderOf repThree = 3 := by
  rw [orderOf_eq_prime_iff]
  decide +kernel
private theorem repFive_order : orderOf repFive = 5 := by
  rw [orderOf_eq_prime_iff]
  decide +kernel
private theorem repThree_centralizer_card :
    Nat.card (centralizer ({repThree} : Set AF)) = 3 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => mem_centralizer_singleton_iff))]
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem repFive_centralizer_card :
    Nat.card (centralizer ({repFive} : Set AF)) = 5 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => mem_centralizer_singleton_iff))]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem prime_centralizer_card_of_representative
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (r : K) (hr : orderOf r = p) (hC : Nat.card (centralizer ({r} : Set K)) = p)
    (x : K) (hx : orderOf x = p) :
    Nat.card (centralizer ({x} : Set K)) = p := by
  have hp := Fact.out (p := p.Prime)
  have hP : ∀ P : Sylow p K, Nat.card P = p :=
    sylow_card_eq_prime_of_centralizer r hr (by
      rw [hC]
      exact Nat.not_dvd_of_pos_of_lt hp.pos (by nlinarith [hp.two_le]))
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_card_eq_prime
    (zpowers r) r (mem_zpowers r) hr hP x hx
  let e := MulAut.conj g
  have hsub : zpowers (e x) = zpowers r :=
    eq_of_le_of_card_ge (zpowers_le.mpr hg) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, e.orderOf_eq, hx, hr])
  have heq : centralizer ({e x} : Set K) = centralizer ({r} : Set K) := by
    rw [← centralizer_closure, ← zpowers_eq_closure, hsub,
      zpowers_eq_closure, centralizer_closure]
  let ec : centralizer ({x} : Set K) ≃ centralizer ({e x} : Set K) :=
    e.toEquiv.subtypeEquiv (fun y => by
      rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      change y * x = x * y ↔ e y * e x = e x * e y
      rw [← map_mul, ← map_mul, e.injective.eq_iff])
  rw [Nat.card_congr ec, heq, hC]

private theorem alternating_three_centralizer_card
    (x : AF) (hx : x ^ 3 = 1) (hne : x ≠ 1) :
      Fintype.card {y : AF // y * x = x * y} = 3 := by
  have hc := prime_centralizer_card_of_representative repThree repThree_order
    repThree_centralizer_card x (orderOf_eq_prime_iff.mpr ⟨hx, hne⟩)
  simpa only [Nat.card_eq_fintype_card, mem_centralizer_singleton_iff] using hc

private theorem alternating_five_centralizer_card
    (x : AF) (hx : x ^ 5 = 1) (hne : x ≠ 1) :
      Fintype.card {y : AF // y * x = x * y} = 5 := by
  have hc := prime_centralizer_card_of_representative repFive repFive_order
    repFive_centralizer_card x (orderOf_eq_prime_iff.mpr ⟨hx, hne⟩)
  simpa only [Nat.card_eq_fintype_card, mem_centralizer_singleton_iff] using hc

private theorem model_centralizer_card (x : M) :
    Nat.card {y : M // y * x = x * y} =
      Nat.card {y : AF // y * x.1 = x.1 * y} * 2 := by
  let e : {y : M // y * x = x * y} ≃
      {y : AF // y * x.1 = x.1 * y} × Multiplicative (ZMod 2) := {
    toFun := fun y => (⟨y.val.1, congrArg Prod.fst y.property⟩, y.val.2)
    invFun := fun y => ⟨(y.1.val, y.2), Prod.ext y.1.property (mul_comm _ _)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod]
  simp [Nat.card_eq_fintype_card]

private theorem model_odd_prime_centralizer_card
    (p : ℕ) (hp : p = 3 ∨ p = 5) (x : M) (hx : x ^ p = 1) (hne : x ≠ 1) :
    Nat.card {y : M // y * x = x * y} = 2 * p := by
  have hfst : x.1 ^ p = 1 := congrArg Prod.fst hx
  have hsnd : x.2 = 1 := by
    have ht : x.2 ^ p = 1 := congrArg Prod.snd hx
    rcases hp with rfl | rfl
    · exact (by decide : ∀ t : Multiplicative (ZMod 2), t ^ 3 = 1 → t = 1) _ ht
    · exact (by decide : ∀ t : Multiplicative (ZMod 2), t ^ 5 = 1 → t = 1) _ ht
  have hfstne : x.1 ≠ 1 := fun hf => hne (Prod.ext hf hsnd)
  rw [model_centralizer_card, Nat.card_eq_fintype_card]
  rcases hp with rfl | rfl
  · rw [alternating_three_centralizer_card _ hfst hfstne]
  · rw [alternating_five_centralizer_card _ hfst hfstne]

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The common centralizer of `z` and a local odd prime-order element has order `2p`. -/
public theorem odd_prime_common_centralizer_card (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    Nat.card (centralizer ({h.z} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) =
      2 * p := by
  let C := centralizer ({h.z} : Set G)
  let xC : C := ⟨x, hxC⟩
  let e := h.alternatingCentralizerEquiv
  have hepow : (e xC) ^ p = 1 := by
    rw [← map_pow, show xC ^ p = 1 from Subtype.ext (hx ▸ pow_orderOf_eq_one x), map_one]
  have hene : e xC ≠ 1 := by
    intro he
    have hx1 : x = 1 := congrArg Subtype.val (e.injective (he.trans e.map_one.symm))
    rcases hp with rfl | rfl <;> simp_all
  let ec : centralizer ({xC} : Set C) ≃ {y : M // y * e xC = e xC * y} :=
    e.toEquiv.subtypeEquiv (fun y => by
      rw [mem_centralizer_singleton_iff]
      change y * xC = xC * y ↔ e y * e xC = e xC * e y
      rw [← map_mul, ← map_mul, e.injective.eq_iff])
  rw [← map_subtype_centralizer_singleton C xC, card_map_of_injective Subtype.val_injective,
    Nat.card_congr ec]
  exact model_odd_prime_centralizer_card p hp _ hepow hene

/-- Inside the full centralizer of an odd prime-order element, `⟨z⟩` is Sylow. -/
public theorem exists_centralizer_sylow_eq_zpowers (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    ∃ P : Sylow 2 (centralizer ({x} : Set G)),
      (P : Subgroup (centralizer ({x} : Set G))) =
        zpowers ⟨h.z, mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hxC).symm⟩ := by
  let C := centralizer ({x} : Set G)
  let zC : C := ⟨h.z, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp hxC).symm⟩
  have hz : orderOf zC = 2 := by
    exact (orderOf_injective C.subtype Subtype.val_injective zC).symm.trans h.involution
  have hzcard : Nat.card (zpowers zC) = 2 := (Nat.card_zpowers zC).trans hz
  obtain ⟨P, hP⟩ := (IsPGroup.of_card (G := zpowers zC) (p := 2) (n := 1) (by simpa using hzcard)).exists_le_sylow
  let R := (P : Subgroup C).map C.subtype
  obtain ⟨S, hS⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  have hzS : h.z ∈ (S : Subgroup G) :=
    hS (mem_map_of_mem C.subtype (hP (mem_zpowers zC)))
  have hR : R ≤ centralizer ({h.z} : Set G) ⊓ C := by
    rintro y ⟨yC, hyP, rfl⟩
    refine ⟨?_, yC.property⟩
    apply mem_centralizer_singleton_iff.mpr
    have hyS := hS (mem_map_of_mem C.subtype hyP)
    exact congrArg Subtype.val (Commute.of_orderOf_dvd_two
      (fun a => orderOf_dvd_of_pow_eq_one (h.any_sylow_square S a))
      (⟨yC, hyS⟩ : S) ⟨h.z, hzS⟩).eq
  have hdiv : Nat.card P ∣ 2 * p := by
    have hd := card_dvd_of_le hR
    rw [card_map_of_injective Subtype.val_injective,
      h.odd_prime_common_centralizer_card p hp x hxC hx] at hd
    exact hd
  have hge : 2 ≤ Nat.card P := by simpa only [hzcard] using card_le_of_le hP
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hnlarge
    have hd : 4 ∣ 2 * p := (show 2 ^ 2 ∣ Nat.card P by
      rw [hn]
      exact Nat.pow_dvd_pow 2 hnlarge).trans hdiv
    rcases hp with rfl | rfl <;> norm_num at hd
  have hcard : Nat.card P = 2 := by
    interval_cases n <;> simp_all
  refine ⟨P, (eq_of_le_of_card_ge hP ?_).symm⟩
  rw [hcard, hzcard]

end CFSG.Quasithin.Janko1CentralizerData
