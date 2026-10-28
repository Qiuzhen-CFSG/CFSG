module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Centralizer
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Alternating-five sections inside A₇

If a subgroup of A₇ has a normal two-subgroup with quotient of order sixty,
that two-subgroup is trivial. Counting reduces its order to one or two;
in the second case it is central, whereas an involution centralizer in S₇
has order forty-eight and cannot contain the subgroup.

Consequently a two-kernel image of a group with two-core quotient A₅ is
itself A₅. The image equivalence retains the original quotient marking,
and its kernel is exactly the original two-core.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
10.2.9, printed pp.751–752, the alternating-seven reduced-action case.
-/

public section
open Subgroup Equiv.Perm
namespace alternatingGroup.SevenFiveSection

private theorem involution_centralizer_card (x : alternatingGroup (Fin 7))
    (hx : orderOf x = 2) :
    Nat.card (centralizer ({(x : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 48 := by
  have ho : orderOf (x : Equiv.Perm (Fin 7)) = 2 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := (x : Equiv.Perm (Fin 7)).sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign := mem_alternatingGroup.mp x.property
  rw [sign_of_cycleType', hk] at hsign
  have hkbound : k ≤ 2 := by omega
  have hk1 : k = 1 := by
    interval_cases k
    · norm_num at hsign
    · rfl
    · norm_num at hsign
  rw [nat_card_centralizer, hk, hk1]
  norm_num [Nat.factorial]

/-- A normal two-subgroup of an A₇ subgroup with quotient of order sixty is trivial. -/
theorem normal_two_subgroup_eq_bot_of_quotient_card_sixty
    (B : Subgroup (alternatingGroup (Fin 7))) (N : Subgroup B) [N.Normal]
    (hN : IsPGroup 2 N) (hq : Nat.card (B ⧸ N) = 60) : N = ⊥ := by
  classical
  have hBcard : Nat.card B = 60 * Nat.card N := by
    rw [card_eq_card_quotient_mul_card_subgroup N, hq]
  have hdiv : Nat.card N ∣ 42 := by
    have hd := B.card_subgroup_dvd_card
    have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hBcard, hA] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 60) hd
  have hcop : Nat.Coprime (Nat.card N) 21 := by
    obtain ⟨n, hn⟩ := hN.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 21).pow_left n
  have hd2 : Nat.card N ∣ 2 := hcop.dvd_mul_right.mp hdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
  · exact card_eq_one.mp h1
  have hcentral := central_of_normal_card_two N h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := N) 2 (by rw [← Nat.card_eq_fintype_card, h2])
  let y : alternatingGroup (Fin 7) := x.val.val
  have hy : orderOf y = 2 :=
    (Subgroup.orderOf_coe x.val).trans ((Subgroup.orderOf_coe x).trans hx)
  let f : B →* centralizer ({(y : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7))) :=
    ((alternatingGroup (Fin 7)).subtype.comp B.subtype).codRestrict _ (fun b => by
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg (fun z : B => z.val.val) (mem_center_iff.mp (hcentral x.property) b))
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (fun z => z.val) hab
    exact hh
  have hd := card_dvd_of_injective f hi
  rw [involution_centralizer_card y hy, hBcard, h2] at hd
  norm_num at hd

/-- A subgroup of A₇ with two-core quotient A₅ has trivial two-core. -/
theorem twoCore_eq_bot (B : Subgroup (alternatingGroup (Fin 7)))
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : pCore 2 B = ⊥ := by
  apply normal_two_subgroup_eq_bot_of_quotient_card_sixty B _ pCore_isPGroup
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- Recover the actual A₅ subgroup from its quotient by the two-core. -/
noncomputable def fiveEquiv (B : Subgroup (alternatingGroup (Fin 7)))
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : B ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (twoCore_eq_bot B e).symm)).trans e

/-- In the actual A₇ image, the original two-core is exactly the restricted kernel. -/
theorem image_twoCore_eq_bot_and_ker_eq {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    pCore 2 (L.map f) = ⊥ ∧ (f.subgroupMap L).ker = pCore 2 L := by
  let eq := ((f.subgroupMap L).pCoreQuotientEquiv (f.subgroupMap_surjective L) hk).symm.trans e
  have hbot := twoCore_eq_bot (L.map f) eq
  refine ⟨hbot, ?_⟩
  have hpre := (f.subgroupMap L).comap_pCore_of_ker_isPGroup
    (f.subgroupMap_surjective L) hk
  rw [hbot] at hpre
  exact hpre

/-- Identify the actual image using the original A₅ quotient marking. -/
@[expose] noncomputable def imageFiveEquiv {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    L.map f ≃* alternatingGroup (Fin 5) :=
  ((QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap L)
    (f.subgroupMap_surjective L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (image_twoCore_eq_bot_and_ker_eq f L hk e).2)).trans e

/-- The image marking agrees on every original element with the given quotient marking. -/
theorem imageFiveEquiv_apply {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (l : L) :
    imageFiveEquiv f L hk e ((f.subgroupMap L) l) = e (QuotientGroup.mk' (pCore 2 L) l) := by
  let d := QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap L)
    (f.subgroupMap_surjective L)
  have hd : d (QuotientGroup.mk' (f.subgroupMap L).ker l) = (f.subgroupMap L) l := rfl
  change e ((QuotientGroup.quotientMulEquivOfEq (image_twoCore_eq_bot_and_ker_eq f L hk e).2)
    (d.symm ((f.subgroupMap L) l))) = _
  rw [← hd, MulEquiv.symm_apply_apply]
  rfl

end alternatingGroup.SevenFiveSection
