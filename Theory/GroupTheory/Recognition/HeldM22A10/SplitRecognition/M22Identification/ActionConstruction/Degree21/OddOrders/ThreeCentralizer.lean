module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.CentralizerControl

/-!
# The order-three centralizer and the exclusion of order nine

The local involution geometry identifies the marked three-centralizer modulo
its center with A₄ or A₅, giving orders 36 or 180. Burnside fusion makes the
eight nonidentity elements of an elementary Sylow three-group a single orbit
of its normalizer. When the latter has order 72, the stabilizer has order nine.
It is the Sylow normalizer inside the three-centralizer. The order-180 case
would therefore have twenty Sylow three-subgroups, contrary to Sylow's
congruence. Conjugacy transports the remaining order 36 to every element of
order three. Elementary Sylow three-groups also exclude any order divisible
by nine.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, Lemma 8, and Section 7, pp.15–16,
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.OddOrders
open LocalModelDichotomy CaseII
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem order_three_of_ne_one {P : Type*} [Group P]
    [IsElementaryAbelian 3 P] (x : P) (hx : x ≠ 1) : orderOf x = 3 := by
  apply orderOf_eq_prime
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 P) x
  · exact hx

private theorem sylow_three_stabilizer_card
    (P : Sylow 3 G) [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    (hN : Nat.card (normalizer (P : Set G)) = 72)
    (hf : ∀ x y : G, orderOf x = 3 → orderOf y = 3 → IsConj x y)
    (x : (P : Subgroup G)) (hx : x ≠ 1) :
    Nat.card ((centralizer ({(x : G)} : Set G)).subgroupOf
      (normalizer (P : Set G))) = 9 := by
  classical
  let N := normalizer ((P : Subgroup G) : Set G)
  have horbit : MulAction.orbit N x = {y : (P : Subgroup G) | y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      intro h
      have he := congrArg Subtype.val h
      change (n : G) * (x : G) * (n : G)⁻¹ = 1 at he
      apply hx
      apply Subtype.ext
      change (x : G) = 1
      have hh := congrArg (fun t : G => (n : G)⁻¹ * t * (n : G)) he
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
        mul_one, inv_mul_cancel] using hh
    · intro hy
      have hxy := hf x y (by simpa using order_three_of_ne_one x hx)
        (by simpa using order_three_of_ne_one y hy)
      obtain ⟨g, hg⟩ := isConj_iff.mp hxy
      have hgmem : (g⁻¹)⁻¹ * (x : G) * g⁻¹ ∈ P := by
        change (g⁻¹)⁻¹ * (x : G) * g⁻¹ ∈ (P : Subgroup G)
        simpa only [inv_inv, hg] using y.property
      obtain ⟨n, hn, he⟩ := P.conj_eq_normalizer_conj_of_mem (x : G) g⁻¹
        x.property hgmem
      refine ⟨⟨n⁻¹, N.inv_mem hn⟩, ?_⟩
      apply Subtype.ext
      change n⁻¹ * (x : G) * (n⁻¹)⁻¹ = y
      simpa only [inv_inv, hg] using he.symm
  have horbitcard : Nat.card (MulAction.orbit N x) = 8 := by
    rw [horbit]
    let := Fintype.ofFinite P
    change Nat.card {y : (P : Subgroup G) // y ≠ 1} = 8
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card, hP]
  have hstab : MulAction.stabilizer N x =
      (centralizer ({(x : G)} : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    rw [Subtype.ext_iff]
    change (n : G) * (x : G) * (n : G)⁻¹ = x ↔ _
    exact mul_inv_eq_iff_eq_mul
  have hi : (MulAction.stabilizer N x).index = 8 := by
    rw [MulAction.index_stabilizer]
    exact horbitcard
  have hh := (MulAction.stabilizer N x).card_mul_index
  rw [hi, hstab] at hh
  change _ * 8 = Nat.card (normalizer (P : Set G)) at hh
  rw [hN] at hh
  change Nat.card ((centralizer ({(x : G)} : Set G)).subgroupOf
    (normalizer (P : Set G))) * 8 = 72 at hh
  omega

/-- The order-72 Sylow normalizer excludes the A₅ central quotient. -/
public theorem marked_three_centralizer_card (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hN : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72) :
    Nat.card (centralizer ({into D k c} : Set G)) = 36 := by
  let H := centralizer ({into D k c} : Set G)
  let t := markedInvolutionInThreeCentralizer D k
  have ht : orderOf t = 2 := by
    rw [orderOf_mk]
    exact D.z_order
  have hZ : Nat.card (center H) = 3 := three_centralizer_center_card D k L.involution_fusion
  have he := CentralizerControl.alternating_four_or_five_of_center_three hZ t ht
    (marked_three_involution_centralizer_card D k)
    (fun x => Subtype.ext (three_centralizer_pow_six_of_commuting_involution D k
      L.involution_fusion x t ht (mem_centralizer_singleton_iff.mp x.property)))
    (three_centralizer_involution_fusion D k L.involution_fusion)
  have hHcard : Nat.card H = 36 ∨ Nat.card H = 180 := by
    have hh := (center H).card_eq_card_quotient_mul_card_subgroup
    rw [hZ] at hh
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · left
      rw [Nat.card_congr e.toEquiv] at hh
      norm_num [nat_card_alternatingGroup, Nat.card_fin] at hh
      exact hh
    · right
      rw [Nat.card_congr e.toEquiv] at hh
      norm_num [nat_card_alternatingGroup, Nat.card_fin] at hh
      exact hh
  rcases hHcard with hh | hh
  · exact hh
  have hc : orderOf (into D k c) = 3 := by
    rw [orderOf_injective (into D k) (into_injective D k)]
    exact actor_orders.2.2.1
  have hQ : IsPGroup 3 (zpowers (into D k c)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hc]; rfl : Nat.card (zpowers (into D k c)) = 3 ^ 1)
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  let : IsElementaryAbelian 3 P := (L.sylow_three P).1
  have hcP : into D k c ∈ (P : Subgroup G) := hQP (mem_zpowers _)
  have hPH : (P : Subgroup G) ≤ H := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨x, hx⟩ : P) ⟨_, hcP⟩))
  have hs := sylow_three_stabilizer_card P (L.sylow_three P).2.1 (hN P)
    (fun x y hx hy => (L.three_fusion x hx).trans (L.three_fusion y hy).symm)
    ⟨_, hcP⟩ (by intro he; have hz : into D k c = 1 := congrArg Subtype.val he; rw [hz, orderOf_one] at hc; omega)
  let R := P.subtype hPH
  have hR : Nat.card (normalizer (R : Set H)) = 9 := by
    change Nat.card (normalizer ((P : Subgroup G).subgroupOf H : Set H)) = 9
    rw [← subgroupOf_normalizer_eq hPH]
    let N := normalizer (P : Set G)
    let e : N.subgroupOf H ≃ H.subgroupOf N := {
      toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans hs
  have hm := card_sylow_modEq_one 3 H
  rw [R.card_eq_index_normalizer] at hm
  have hi := (normalizer (R : Set H)).card_mul_index
  rw [hR, hh] at hi
  change (normalizer (R : Set H)).index % 3 = 1 % 3 at hm
  omega

/-- All ambient elements of order three have centralizer order 36. -/
public theorem three_centralizer_card (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hN : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (x : G) (hx : orderOf x = 3) : Nat.card (centralizer ({x} : Set G)) = 36 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (L.three_fusion x hx)
  let e := MulAut.conj g
  have he : e x = into D k c := hg
  let f : centralizer ({x} : Set G) ≃ centralizer ({into D k c} : Set G) :=
    Equiv.subtypeEquiv e.toEquiv (by
      intro t
      change t ∈ centralizer ({x} : Set G) ↔ e t ∈ centralizer ({into D k c} : Set G)
      simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff])
  exact (Nat.card_congr f).trans (marked_three_centralizer_card D k L hN)

/-- Elementary Sylow three-subgroups exclude every multiple of nine. -/
public theorem not_nine_dvd_order (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k) (g : G) :
    ¬ 9 ∣ orderOf g := by
  intro h9
  let x := g ^ (orderOf g / 9)
  have hx : orderOf x = 9 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos g)) h9
  have hQ : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hx]; rfl : Nat.card (zpowers x) = 3 ^ 2)
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  let : IsElementaryAbelian 3 P := (L.sylow_three P).1
  let y : P := ⟨x, hP (mem_zpowers x)⟩
  have hy : y ^ 3 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 3 P) y
  have hp : x ^ 3 = 1 := congrArg Subtype.val hy
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hx] at hd
  norm_num at hd

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.OddOrders
