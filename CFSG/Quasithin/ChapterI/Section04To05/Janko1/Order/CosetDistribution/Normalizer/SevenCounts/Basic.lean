module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Commuting
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# The elementary counts in the contrary seven-normalizer

Write `A = C_G(S)` and `H = N_G(A)`. From the supplied literal
factorization, the cyclic order-six complement is disjoint from A, so
`|H| = 6|A|`. The involutions of H are exactly the products `at` for
`a ∈ A`. Two such involutions commute only when equal, giving thirty
external commuting involutions for each internal one.

Regular centralizers give the trivial-intersection property of A. A
fixed-point-free commutator map conjugates every element of `H ∖ A`
into the complement. Finally the order-three element in both normalizers
fixes an involution in the elementary eight, whereas no involution of H
lies there; the odd-prime local count therefore forces `d = 3`.

These results use `BenderSevenStructure` as an explicit input. They do
not assert that input's existence or the external coset distribution.
Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {h : Janko1CentralizerData G} {d : ℕ} (localData : BenderPrimeData G d)
    {S : Subgroup G} (hS : Nat.card S = 7) (structureData : BenderSevenStructure h S)

namespace BenderSevenStructure

include h localData hS structureData

/-- The kernel and the literal complement intersect trivially. -/
public theorem kernel_disjoint_complement :
    Disjoint (centralizer (S : Set G))
      (normalizer (centralizer (S : Set G) : Set G) ⊓
        centralizer ({structureData.t} : Set G)) := by
  apply Disjoint.mono_right inf_le_right
  apply disjoint_of_coprime_natCard
  rw [h.involution_centralizer_card structureData.t structureData.involution]
  exact h.seven_centralizer_coprime localData S hS

/-- The factorization is unique, hence the normalizer has order `6a`. -/
public theorem normalizer_card :
    Nat.card (normalizer (centralizer (S : Set G) : Set G)) =
      6 * Nat.card (centralizer (S : Set G)) := by
  let A := centralizer (S : Set G)
  let H := normalizer (A : Set G)
  let C := H ⊓ centralizer ({structureData.t} : Set G)
  let f : A × C → H := fun p => ⟨p.1 * p.2, H.mul_mem (le_normalizer p.1.2) p.2.2.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply mul_injective_of_disjoint (structureData.kernel_disjoint_complement localData hS)
      exact congrArg Subtype.val he
    · intro x
      obtain ⟨a, ha, c, hc, he⟩ := structureData.factorization x x.2
      exact ⟨(⟨a, ha⟩, ⟨c, hc⟩), Subtype.ext he.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]
  change Nat.card A * Nat.card C = 6 * Nat.card A
  rw [show Nat.card C = 6 from structureData.complement_card, Nat.mul_comm]

omit h localData hS structureData in
private theorem cyclic_square_eq_one {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (t : C) (ht : orderOf t = 2) (c : C) (hc : c ^ 2 = 1) : c = 1 ∨ c = t := by
  classical
  let _ : Fintype C := Fintype.ofFinite _
  let F : Finset C := {x | x ^ 2 = 1}
  have hle : F.card ≤ 2 := IsCyclic.card_pow_eq_one_le (by decide)
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.mp ht).2
  by_contra hn
  push Not at hn
  have hsub : ({1, t, c} : Finset C) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [F, ht2, hc]
  have hcard : ({1, t, c} : Finset C).card = 3 := by
    simp [ht1.symm, hn.1.symm, hn.2.symm]
  have hh := Finset.card_le_card hsub
  omega

omit structureData in
private theorem square_eq_one_kernel (a : G) (ha : a ∈ centralizer (S : Set G))
    (ha2 : a ^ 2 = 1) : a = 1 := by
  let A := centralizer (S : Set G)
  let x : A := ⟨a, ha⟩
  have hc : Nat.Coprime (Nat.card A) 2 :=
    (h.seven_centralizer_coprime localData S hS).of_dvd_right (by decide)
  have he : x = 1 := (pow_eq_one_iff_of_coprime hc).mp
    ⟨pow_card_eq_one', Subtype.ext ha2⟩
  exact congrArg Subtype.val he

/-- Every involution of the normalizer lies in the one nontrivial coset
of the seven-centralizer determined by the distinguished involution. -/
public theorem involution_factorization (u : G) (hu : orderOf u = 2)
    (huH : u ∈ normalizer (centralizer (S : Set G) : Set G)) :
    ∃ a ∈ centralizer (S : Set G), u = a * structureData.t := by
  let A := centralizer (S : Set G)
  let H := normalizer (A : Set G)
  let C := H ⊓ centralizer ({structureData.t} : Set G)
  obtain ⟨a, ha, c, hc, rfl⟩ := structureData.factorization u huH
  have hu2 : (a * c) ^ 2 = 1 := (orderOf_eq_prime_iff.mp hu).1
  have hac : c * a * c⁻¹ ∈ A := (mem_normalizer_iff.mp hc.1 a).mp ha
  have hc2A : c ^ 2 ∈ A := by
    have he : c ^ 2 = (a * (c * a * c⁻¹))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      calc
        a * (c * a * c⁻¹) * c ^ 2 = (a * c) ^ 2 := by simp only [pow_two]; group
        _ = 1 := hu2
    rw [he]
    exact A.inv_mem (A.mul_mem ha hac)
  have hc2 : c ^ 2 = 1 :=
    (structureData.kernel_disjoint_complement localData hS).le_bot
      ⟨hc2A, C.pow_mem hc 2⟩
  have htH : structureData.t ∈ H :=
    normalizer_le_normalizer_centralizer S structureData.normalizes
  have htC : structureData.t ∈ C := ⟨htH, mem_centralizer_singleton_iff.mpr rfl⟩
  let _ : IsCyclic C := structureData.complement_cyclic
  have he := cyclic_square_eq_one (⟨structureData.t, htC⟩ : C)
    ((orderOf_injective C.subtype C.subtype_injective _).symm.trans structureData.involution)
    (⟨c, hc⟩ : C) (Subtype.ext hc2)
  rcases he with he | he
  · have hc1 : c = 1 := congrArg Subtype.val he
    rw [hc1, mul_one] at hu hu2
    have ha1 := square_eq_one_kernel (h := h) localData hS a ha hu2
    rw [ha1, orderOf_one] at hu
    omega
  · exact ⟨a, ha, congrArg (a * ·) (congrArg Subtype.val he)⟩

/-- Each product `at` is an involution: `t` inverts the odd kernel. -/
public theorem mul_t_involution (a : G) (ha : a ∈ centralizer (S : Set G)) :
    orderOf (a * structureData.t) = 2 := by
  have ht := structureData.involution
  have ht2 : structureData.t * structureData.t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht).1
  have hti : structureData.t⁻¹ = structureData.t := inv_eq_of_mul_eq_one_right ht2
  have hinv := (h.seven_centralizer_inverted localData S hS structureData.t ht
    structureData.normalizes).1 a ha
  rw [hti] at hinv
  apply orderOf_eq_prime_iff.mpr
  constructor
  · calc
      (a * structureData.t) ^ 2 = a * (structureData.t * a * structureData.t) := by simp only [pow_two]; group
      _ = 1 := by rw [hinv, mul_inv_cancel]
  · intro he
    have htA : structureData.t ∈ centralizer (S : Set G) := by
      rw [show structureData.t = a⁻¹ from eq_inv_of_mul_eq_one_right he]
      exact inv_mem ha
    have ht1 := square_eq_one_kernel (h := h) localData hS _ htA
      (orderOf_eq_prime_iff.mp ht).1
    exact (orderOf_eq_prime_iff.mp ht).2 ht1

/-- The base fiber is in bijection with the actual seven-centralizer. -/
public theorem base_fiber :
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G))
      (benderBaseCoset (normalizer (centralizer (S : Set G) : Set G)))) =
      Nat.card (centralizer (S : Set G)) := by
  let A := centralizer (S : Set G)
  let H := normalizer (A : Set G)
  have htH : structureData.t ∈ H :=
    normalizer_le_normalizer_centralizer S structureData.normalizes
  let f : A → BenderFiber H (benderBaseCoset H) := fun a =>
    ⟨a * structureData.t, structureData.mul_t_involution localData hS a a.2,
      (benderRightCoset_eq_base_iff H _).mpr (H.mul_mem (le_normalizer a.2) htH)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      apply Subtype.ext
      exact mul_right_cancel (congrArg Subtype.val he)
    · intro u
      obtain ⟨a, ha, he⟩ := structureData.involution_factorization localData hS u.1 u.2.1
        ((benderRightCoset_eq_base_iff H u.1).mp u.2.2)
      exact ⟨⟨a, ha⟩, Subtype.ext he.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm


/-- Two commuting involutions in the normalizer are equal. -/
public theorem commuting_involutions_eq (u v : G) (hu : orderOf u = 2)
    (hv : orderOf v = 2)
    (huH : u ∈ normalizer (centralizer (S : Set G) : Set G))
    (hvH : v ∈ normalizer (centralizer (S : Set G) : Set G))
    (huv : Commute u v) : u = v := by
  have huvA : u * v ∈ centralizer (S : Set G) := by
    obtain ⟨a, ha, rfl⟩ := structureData.involution_factorization localData hS u hu huH
    obtain ⟨b, hb, rfl⟩ := structureData.involution_factorization localData hS v hv hvH
    have ht2 : structureData.t * structureData.t = 1 := by
      simpa only [pow_two] using (orderOf_eq_prime_iff.mp structureData.involution).1
    have hti : structureData.t⁻¹ = structureData.t := inv_eq_of_mul_eq_one_right ht2
    have hinv := (h.seven_centralizer_inverted localData S hS structureData.t
      structureData.involution structureData.normalizes).1 b hb
    rw [hti] at hinv
    have he : a * structureData.t * (b * structureData.t) = a * b⁻¹ := by
      rw [mul_assoc, ← mul_assoc structureData.t b, hinv]
    rw [he]
    exact mul_mem ha (inv_mem hb)
  have huv2 : (u * v) ^ 2 = 1 := by
    rw [huv.mul_pow, (orderOf_eq_prime_iff.mp hu).1, (orderOf_eq_prime_iff.mp hv).1, one_mul]
  have huv1 := square_eq_one_kernel (h := h) localData hS _ huvA huv2
  have hv2 : v * v = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hv).1
  exact mul_right_cancel (huv1.trans hv2.symm)

/-- An internal involution commutes with thirty involutions outside the
normalizer, since it is the sole internal involution in its centralizer. -/
public theorem outside_commuting_involutions_card (u : G) (hu : orderOf u = 2)
    (huH : u ∈ normalizer (centralizer (S : Set G) : Set G)) :
    Nat.card {v : G // orderOf v = 2 ∧ Commute v u ∧
      v ∉ normalizer (centralizer (S : Set G) : Set G)} = 30 := by
  classical
  let H := normalizer (centralizer (S : Set G) : Set G)
  let J := {v : G // orderOf v = 2 ∧ Commute v u}
  let p : J → Prop := fun v => v.1 ∈ H
  have hi : Nat.card {v : J // p v} = 1 := by
    let ei : {v : J // p v} ≃ Unit := {
      toFun := fun _ => ()
      invFun := fun _ => ⟨⟨u, hu, Commute.refl u⟩, huH⟩
      left_inv := by
        intro v
        apply Subtype.ext; apply Subtype.ext
        exact (structureData.commuting_involutions_eq localData hS
          v.1.1 u v.1.2.1 hu v.2 huH v.1.2.2).symm
      right_inv := by intro v; cases v; rfl }
    rw [Nat.card_congr ei, Nat.card_unique]
  let eo : {v : J // ¬ p v} ≃
      {v : G // orderOf v = 2 ∧ Commute v u ∧ v ∉ H} := {
    toFun := fun v => ⟨v.1.1, v.1.2.1, v.1.2.2, v.2⟩
    invFun := fun v => ⟨⟨v.1, v.2.1, v.2.2.1⟩, v.2.2.2⟩
    left_inv := by intro v; rfl
    right_inv := by intro v; rfl }
  have hc := Nat.card_congr (Equiv.sumCompl p).symm
  rw [Nat.card_sum, hi, Nat.card_congr eo] at hc
  have hJ : Nat.card J = 31 := h.bender_commuting_involutions_card u hu
  change Nat.card {v : G // orderOf v = 2 ∧ Commute v u ∧ v ∉ H} = 30
  omega

omit localData hS [IsSimpleGroup G] in
/-- The conjugates of the kernel have trivial intersections unless their
conjugating element normalizes it. This is the TI step in Bender (4.3). -/
public theorem normalizes_of_conjugate_kernel_ne_one (g x : G)
    (hx : x ∈ centralizer (S : Set G)) (hx1 : x ≠ 1)
    (hgx : g * x * g⁻¹ ∈ centralizer (S : Set G)) :
    g ∈ normalizer (centralizer (S : Set G) : Set G) := by
  let e := MulAut.conj g
  have hex1 : e x ≠ 1 := fun he => hx1 (e.injective (he.trans (map_one e).symm))
  have hcx := structureData.centralizers x hx hx1
  have hcex := structureData.centralizers (e x) hgx hex1
  apply mem_normalizer_iff.mpr
  intro a
  change a ∈ centralizer (S : Set G) ↔ e a ∈ centralizer (S : Set G)
  conv_lhs => rw [← hcx, mem_centralizer_singleton_iff]
  conv_rhs => rw [← hcex, mem_centralizer_singleton_iff]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

omit localData hS [IsSimpleGroup G] in
/-- An outside involution cannot invert a nonidentity kernel element. -/
public theorem inverted_kernel_eq_one (u x : G)
    (huH : u ∉ normalizer (centralizer (S : Set G) : Set G))
    (hx : x ∈ centralizer (S : Set G)) (hinv : u * x * u⁻¹ = x⁻¹) : x = 1 := by
  by_contra hx1
  exact huH (structureData.normalizes_of_conjugate_kernel_ne_one u x hx hx1
    (hinv.symm ▸ inv_mem hx))


omit localData hS [IsSimpleGroup G] in
/-- Every element outside the kernel is conjugate by a kernel element into
the literal cyclic complement. -/
public theorem conjugate_into_complement (u : G)
    (huH : u ∈ normalizer (centralizer (S : Set G) : Set G))
    (huA : u ∉ centralizer (S : Set G)) :
    ∃ b ∈ centralizer (S : Set G),
      ∃ c ∈ normalizer (centralizer (S : Set G) : Set G) ⊓
        centralizer ({structureData.t} : Set G), u = b * c * b⁻¹ := by
  let A := centralizer (S : Set G)
  let C := normalizer (A : Set G) ⊓ centralizer ({structureData.t} : Set G)
  obtain ⟨a, ha, c, hc, rfl⟩ := structureData.factorization u huH
  have hcA : c ∉ A := fun hh => huA (A.mul_mem ha hh)
  let f : MulAut A := A.normalizerMonoidHom ⟨c, hc.1⟩
  have hfree : MonoidHom.FixedPointFree f := by
    intro x hx
    by_contra hx1
    apply hcA
    change c ∈ centralizer (S : Set G)
    rw [← structureData.centralizers x x.2 (fun he => hx1 (Subtype.ext he))]
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hx))
  obtain ⟨b, hb⟩ := hfree.commutatorMap_surjective (⟨a, ha⟩ : A)
  have he : (b : G) * (c * (b : G) * c⁻¹)⁻¹ = a := by
    have he0 := congrArg Subtype.val hb
    change (b : G) / (c * (b : G) * c⁻¹) = a at he0
    simpa only [div_eq_mul_inv] using he0
  refine ⟨b, b.2, c, hc, ?_⟩
  calc
    a * c = ((b : G) * (c * (b : G) * c⁻¹)⁻¹) * c := by rw [he]
    _ = (b : G) * c * (b : G)⁻¹ := by group

/-- No internal involution lies in the marked Sylow two-subgroup. The
seven-subgroup would otherwise centralize it. -/
public theorem involution_not_mem_sylow (hSN : S ≤ normalizer (h.sylow : Set G))
    (u : G) (hu : orderOf u = 2)
    (huH : u ∈ normalizer (centralizer (S : Set G) : Set G)) :
    u ∉ (h.sylow : Subgroup G) := by
  intro huQ
  let H := normalizer (centralizer (S : Set G) : Set G)
  have hle : S ≤ centralizer ({u} : Set G) := by
    intro s hs
    let e := MulAut.conj s
    have hsH : s ∈ H := normalizer_le_normalizer_centralizer S (le_normalizer hs)
    have hsuH : e u ∈ H := H.mul_mem (H.mul_mem hsH huH) (H.inv_mem hsH)
    have hsuQ : e u ∈ (h.sylow : Subgroup G) := (mem_normalizer_iff.mp (hSN hs) u).mp huQ
    have hcomm : Commute (e u) u := by
      let vQ : h.sylow := ⟨e u, hsuQ⟩
      let uQ : h.sylow := ⟨u, huQ⟩
      exact congrArg Subtype.val (Commute.of_orderOf_dvd_two
        (fun a => orderOf_dvd_of_pow_eq_one (h.sylow_square a)) vQ uQ).eq
    have he := structureData.commuting_involutions_eq localData hS (e u) u
      ((e.orderOf_eq u).trans hu) hu hsuH huH hcomm
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hd := card_dvd_of_le hle
  rw [hS, h.involution_centralizer_card u hu] at hd
  norm_num at hd

/-- The order-three element supplied in both normalizers forces `d = 3`.
An order-three action fixes a nonidentity element of the elementary eight,
whereas no internal involution lies in that eight. -/
public theorem d_eq_three (hSN : S ≤ normalizer (h.sylow : Set G)) : d = 3 := by
  rcases localData.d_cases with hd | hd
  · obtain ⟨x, hxN, hxH, hx3⟩ := structureData.three_in_sylow_normalizer
    let Q : Subgroup G := h.sylow
    let X := zpowers x
    let D := Q ⊓ centralizer (X : Set G)
    have hp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hx3, pow_one])
    have hm := X.card_modEq_card_inf_centralizer Q hp (zpowers_le.mpr hxN)
    change Nat.card Q % 3 = Nat.card D % 3 at hm
    have hQ : Nat.card Q = 8 := h.sylow_card
    have hD : D ≠ ⊥ := by
      intro he
      rw [he, card_bot, hQ] at hm
      norm_num at hm
    have hex : ∃ v : G, v ∈ D ∧ v ≠ 1 := by
      by_contra hn
      push Not at hn
      exact hD (eq_bot_iff.mpr hn)
    obtain ⟨v, hv, hv1⟩ := hex
    have hv2 : orderOf v = 2 := orderOf_eq_prime_iff.mpr
      ⟨congrArg Subtype.val (h.sylow_square ⟨v, hv.1⟩), hv1⟩
    have hvx : Commute v x := (hv.2 x (mem_zpowers x)).symm
    have hxA : x ∉ centralizer (S : Set G) := by
      intro hx
      have hxsub : orderOf (⟨x, hx⟩ : centralizer (S : Set G)) = 3 :=
        (orderOf_injective _ (centralizer (S : Set G)).subtype_injective _).symm.trans hx3
      exact (h.seven_centralizer_small_primes localData S hS).2.1
        (hxsub ▸ orderOf_dvd_natCard (⟨x, hx⟩ : centralizer (S : Set G)))
    obtain ⟨b, hb, c, hc, he⟩ := structureData.conjugate_into_complement x hxH hxA
    let e := MulAut.conj b
    let u := e structureData.t
    have hu : orderOf u = 2 := (e.orderOf_eq _).trans structureData.involution
    have huH : u ∈ normalizer (centralizer (S : Set G) : Set G) := by
      let H := normalizer (centralizer (S : Set G) : Set G)
      have hbH : b ∈ H := le_normalizer hb
      exact H.mul_mem (H.mul_mem hbH
        (normalizer_le_normalizer_centralizer S structureData.normalizes)) (H.inv_mem hbH)
    have hux : Commute u x := by
      have htc : Commute structureData.t c := (mem_centralizer_singleton_iff.mp hc.2).symm
      have hh := htc.map e.toMonoidHom
      change Commute u (e c) at hh
      exact he.symm ▸ hh
    let J := {t : G // orderOf t = 2 ∧ Commute t x}
    have hJ : Nat.card J = 1 := by
      change Nat.card {t : G // orderOf t = 2 ∧ Commute t x} = 1
      rw [localData.commuting_three x hx3, hd]
    have : Subsingleton J := (Nat.card_eq_one_iff_unique.mp hJ).1
    have huv : u = v := congrArg Subtype.val
      (Subsingleton.elim (⟨u, hu, hux⟩ : J) ⟨v, hv2, hvx⟩)
    exact (structureData.involution_not_mem_sylow localData hS hSN u hu huH
      (huv.symm ▸ hv.1)).elim
  · exact hd

end BenderSevenStructure
end CFSG.Quasithin.Janko1CentralizerData
