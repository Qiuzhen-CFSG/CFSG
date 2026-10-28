module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.AlternativesData
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Intrinsic restrictions on an odd centralizer complement

The normal complement has index two in `C_G(x)`, so its elements are
exactly the odd-order elements of that centralizer. This proves uniqueness
and shows that the full normalizer of `⟨x⟩` normalizes the complement.

Conjugation by `z` gives an involutive automorphism of `A` with fixed
subgroup `⟨x⟩`, which lies in the center of `A`. The fixed/inverted
factorization of an odd group makes the induced action on `A/⟨x⟩`
inversion. That quotient is therefore abelian, so `[A,A] ≤ ⟨x⟩` and `A`
has nilpotency class at most two. If `A` is nonabelian, its commutator
subgroup is exactly `⟨x⟩` and their ambient normalizers coincide.

These are inputs to reconstructing the proof cited in Bender, *Finite
groups with large subgroups* (1974), proof of (4.1), printed p.225:
Janko, *A new finite simple group with abelian Sylow 2-subgroups and its
characterization*, J. Algebra 3 (1966), proof of Lemma 3.1. They do not
classify `A` or construct the exceptional normalizer. In particular,
central fixed points alone do not imply that an odd group is abelian.
-/

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}
  {x : G} {A : Subgroup G}

/-- The complement and the distinguished involution give the full centralizer order. -/
public theorem OddCentralizerComplement.centralizer_card
    (a : OddCentralizerComplement h x A) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card A * 2 := by
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes A (zpowers h.z)
    (zpowers_le.mpr (a.normalizes (by
      rw [← a.sup_eq]
      exact (show zpowers h.z ≤ A ⊔ zpowers h.z from le_sup_right) (mem_zpowers h.z))))
  rw [a.disjoint.eq_bot, card_bot, one_mul, a.sup_eq,
    Nat.card_zpowers, h.involution] at hc
  exact hc.symm

/-- The complement has index two in the actual element centralizer. -/
public theorem OddCentralizerComplement.relative_index_two
    (a : OddCentralizerComplement h x A) :
    (A.subgroupOf (centralizer ({x} : Set G))).index = 2 := by
  have he := (A.subgroupOf (centralizer ({x} : Set G))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (a.le_centralizer h)).toEquiv,
    a.centralizer_card] at he
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos he

/-- Every element of the odd complement has odd order. -/
public theorem OddCentralizerComplement.odd_orderOf
    (a : OddCentralizerComplement h x A) {y : G} (hy : y ∈ A) : Odd (orderOf y) := by
  have ho : Odd (orderOf (⟨y, hy⟩ : A)) :=
    a.odd_card.of_dvd_nat (orderOf_dvd_natCard (⟨y, hy⟩ : A))
  rwa [← orderOf_injective A.subtype Subtype.val_injective] at ho

/-- Inside the centralizer, the odd-order elements are exactly the complement. -/
public theorem OddCentralizerComplement.mem_iff_odd_orderOf
    (a : OddCentralizerComplement h x A) {y : G}
    (hy : y ∈ centralizer ({x} : Set G)) : y ∈ A ↔ Odd (orderOf y) := by
  refine ⟨a.odd_orderOf, ?_⟩
  intro hodd
  let C := centralizer ({x} : Set G)
  let K := A.subgroupOf C
  let : K.Normal := a.normal_subgroupOf h
  let q := QuotientGroup.mk' K
  let yC : C := ⟨y, hy⟩
  have hc : Nat.card (C ⧸ K) = 2 := K.index_eq_card ▸ a.relative_index_two
  have hd2 : orderOf (q yC) ∣ 2 := hc ▸ orderOf_dvd_natCard (q yC)
  have hdy : orderOf (q yC) ∣ orderOf y := by
    have he : orderOf yC = orderOf y :=
      (orderOf_injective C.subtype Subtype.val_injective yC).symm
    rw [← he]
    exact orderOf_map_dvd q yC
  have hq : q yC = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right hdy hd2)
  exact (QuotientGroup.eq_one_iff yC).mp hq

/-- The odd complement to the distinguished involution is unique. -/
public theorem OddCentralizerComplement.unique
    (a : OddCentralizerComplement h x A) {B : Subgroup G}
    (b : OddCentralizerComplement h x B) : A = B := by
  apply le_antisymm
  · intro y hy
    exact (b.mem_iff_odd_orderOf (a.le_centralizer h hy)).mpr (a.odd_orderOf hy)
  · intro y hy
    exact (a.mem_iff_odd_orderOf (b.le_centralizer h hy)).mpr (b.odd_orderOf hy)

/-- Normalizing the element centralizer preserves its odd complement. -/
public theorem OddCentralizerComplement.normalizer_centralizer_le
    (a : OddCentralizerComplement h x A) :
    normalizer (centralizer ({x} : Set G) : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  have hgc := mem_normalizer_iff.mp hg y
  have ho : orderOf (g * y * g⁻¹) = orderOf y := (MulAut.conj g).orderOf_eq y
  constructor
  · intro hy
    apply (a.mem_iff_odd_orderOf (hgc.mp (a.le_centralizer h hy))).mpr
    rw [ho]
    exact a.odd_orderOf hy
  · intro hy
    apply (a.mem_iff_odd_orderOf (hgc.mpr (a.le_centralizer h hy))).mpr
    rw [← ho]
    exact a.odd_orderOf hy

/-- The full ambient normalizer of the prime-order subgroup normalizes its complement. -/
public theorem OddCentralizerComplement.normalizer_zpowers_le
    (a : OddCentralizerComplement h x A) :
    normalizer (zpowers x : Set G) ≤ normalizer (A : Set G) := by
  have hn : normalizer (zpowers x : Set G) ≤
      normalizer (centralizer (zpowers x : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (zpowers x : Set G))).mp
      inferInstance
  have he : centralizer (zpowers x : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [he] at hn
  exact hn.trans a.normalizer_centralizer_le

/-- The distinguished involution normalizes the odd complement. -/
public theorem OddCentralizerComplement.z_mem_normalizer
    (a : OddCentralizerComplement h x A) : h.z ∈ normalizer (A : Set G) := by
  apply a.normalizes
  rw [← a.sup_eq]
  exact (show zpowers h.z ≤ A ⊔ zpowers h.z from le_sup_right) (mem_zpowers h.z)

/-- The actual conjugation action of the distinguished involution on the complement. -/
public noncomputable def OddCentralizerComplement.zAction
    (a : OddCentralizerComplement h x A) : MulAut A :=
  A.normalizerMonoidHom ⟨h.z, a.z_mem_normalizer⟩

/-- The conjugation action agrees with ambient conjugation, with no opposite convention. -/
public theorem OddCentralizerComplement.zAction_apply
    (a : OddCentralizerComplement h x A) (y : A) :
    (a.zAction y : G) = h.z * (y : G) * h.z⁻¹ := by
  unfold zAction
  rfl

/-- The conjugation action squares to the identity. -/
public theorem OddCentralizerComplement.zAction_involutive
    (a : OddCentralizerComplement h x A) : Function.Involutive a.zAction := by
  have hz2 : h.z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one h.z
  have hpow : a.zAction ^ 2 = 1 := by
    change A.normalizerMonoidHom ⟨h.z, a.z_mem_normalizer⟩ ^ 2 = 1
    rw [← map_pow, show (⟨h.z, a.z_mem_normalizer⟩ : normalizer (A : Set G)) ^ 2 = 1
      from Subtype.ext hz2, map_one]
  exact fun y => congrArg (fun f : MulAut A => f y) hpow

/-- The fixed subgroup is the literal prime-order subgroup restricted to the complement. -/
public theorem OddCentralizerComplement.zAction_fixed
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    a.zAction.fixedSubgroup = (zpowers x).subgroupOf A := by
  ext y
  rw [MulAut.mem_fixedSubgroup, Subtype.ext_iff, a.zAction_apply,
    mul_inv_eq_iff_eq_mul, mem_subgroupOf]
  rw [← a.inf_centralizer_eq_zpowers h p hp hxC hx]
  simp only [mem_inf, y.property, true_and, mem_centralizer_singleton_iff, eq_comm]

/-- The marked odd-prime element is central in its complement. -/
public theorem OddCentralizerComplement.x_mem_center
    (a : OddCentralizerComplement h x A) :
    (⟨x, a.x_mem⟩ : A) ∈ center A := by
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (a.le_centralizer h y.property))

/-- Every fixed point of the distinguished involution is central in the complement. -/
public theorem OddCentralizerComplement.fixed_le_center
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    a.zAction.fixedSubgroup ≤ center A := by
  rw [a.zAction_fixed p hp hxC hx]
  intro y hy
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hy
  have hy' : (⟨x, a.x_mem⟩ : A) ^ n = y := Subtype.ext hn
  rw [← hy']
  exact (center A).zpow_mem a.x_mem_center n

private theorem commutator_le_fixed_of_central_fixed
    {H : Type*} [Group H] [Finite H] (hodd : Odd (Nat.card H))
    (f : MulAut H) (hf : Function.Involutive f)
    (hc : f.fixedSubgroup ≤ center H) : _root_.commutator H ≤ f.fixedSubgroup := by
  let F := f.fixedSubgroup
  let : F.Normal := ⟨fun u hu v => by
    rw [mem_center_iff.mp (hc hu) v, mul_assoc, mul_inv_cancel, mul_one]
    exact hu⟩
  let q := QuotientGroup.mk' F
  have hinv (y : H) : q (f y) = (q y)⁻¹ := by
    obtain ⟨⟨u, v⟩, ⟨hu, hv, rfl⟩, _⟩ :=
      Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd f hf y
    have huq : q u = 1 := (QuotientGroup.eq_one_iff u).mpr
      ((MulAut.mem_fixedSubgroup f u).mpr hu)
    simp only [map_mul, hu, hv, huq, map_inv, one_mul]
  have hcomm (u v : H) : Commute (q u) (q v) := by
    have he := hinv (u * v)
    rw [map_mul f, map_mul q, hinv u, hinv v, map_mul, mul_inv_rev] at he
    have he' := congrArg Inv.inv he
    change q u * q v = q v * q u
    simpa only [mul_inv_rev, inv_inv] using he'.symm
  rw [commutator_eq_closure, closure_le]
  rintro _ ⟨u, v, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅u, v⁆ = 1
  rw [map_commutatorElement, (hcomm u v).commutator_eq]

/-- The quotient by the marked prime-order subgroup is abelian. -/
public theorem OddCentralizerComplement.commutator_le_zpowers
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    ⁅A, A⁆ ≤ zpowers x := by
  rw [← map_subtype_commutator, map_le_iff_le_comap]
  change _root_.commutator A ≤ (zpowers x).subgroupOf A
  rw [← a.zAction_fixed p hp hxC hx]
  exact commutator_le_fixed_of_central_fixed a.odd_card a.zAction a.zAction_involutive
    (a.fixed_le_center p hp hxC hx)

/-- The odd complement has nilpotency class at most two. -/
public theorem OddCentralizerComplement.commutator_central
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    ⁅⁅A, A⁆, A⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply (a.commutator_le_zpowers p hp hxC hx).trans
  apply zpowers_le.mpr
  rw [mem_centralizer_iff]
  intro y hy
  exact mem_centralizer_singleton_iff.mp (a.le_centralizer h hy)

/-- A nonabelian complement has exactly the marked prime-order commutator subgroup. -/
public theorem OddCentralizerComplement.commutator_eq_zpowers_of_not_commutative
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hnonab : ¬ IsMulCommutative A) : ⁅A, A⁆ = zpowers x := by
  have hle := a.commutator_le_zpowers p hp hxC hx
  have hd := card_dvd_of_le hle
  rw [Nat.card_zpowers, hx] at hd
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  rcases (Nat.dvd_prime hprime).mp hd with hone | heq
  · exact (hnonab (commutator_self_eq_bot_iff.mp (eq_bot_of_card_eq _ hone))).elim
  · apply eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, hx, heq]

/-- In the nonabelian branch, the commutator line determines the full normalizer. -/
public theorem OddCentralizerComplement.normalizer_eq_of_not_commutative
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hnonab : ¬ IsMulCommutative A) :
    normalizer (A : Set G) = normalizer (zpowers x : Set G) := by
  apply le_antisymm ?_ a.normalizer_zpowers_le
  intro g hg
  rw [← a.commutator_eq_zpowers_of_not_commutative p hp hxC hx hnonab,
    mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp hg]

end CFSG.Quasithin.Janko1CentralizerData
