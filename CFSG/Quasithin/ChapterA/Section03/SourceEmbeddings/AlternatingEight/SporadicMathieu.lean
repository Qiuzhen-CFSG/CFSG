module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenFaithfulSylow
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicOrders
public import Theory.Mathieu.M23.Properties.NoOrderTen
public import CFSG.Quasithin.MainConverse.MathieuLocal.M23Even
public import CFSG.Quasithin.MainConverse.Transport

/-!
# Excluding M₂₃ from the original local A₈ section

The original two-core has order dividing two, by the literal group orders.
If nontrivial it is normalized by B and thus centralized by B, so an element
of order five in B produces an element of order ten in the ambient group.

If the core is trivial, B is A₈. Even characteristic makes its normalized
Sylow action faithful. The normalizer action image contains both the inner
A₈ of order 20160 and a subgroup of order 128, so equals Aut(A₈)=S₈. An
order-ten automorphism lifts to an ambient element whose order is divisible
by ten, again contrary to the proved M₂₃ spectrum. The proof keeps the literal
B and full Sylow throughout; no maximal-subgroup classification is assumed.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 15.3.32(3), p.1133.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]
private theorem core_card_dvd_two {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Sporadic.Mathieu.M23) : Nat.card (pCore 2 B) ∣ 2 := by
  have hd := B.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m23_order,
    ← (pCore 2 B).card_mul_index, show (pCore 2 B).index = 20160 from quotient_card h] at hd
  have hd' : Nat.card (pCore 2 B) ∣ 2 * 253 :=
    (Nat.mul_dvd_mul_iff_right (by decide : 0 < 20160)).mp hd
  have hcop : Nat.Coprime (Nat.card (pCore 2 B)) 253 := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 253).pow_left n
  exact hcop.dvd_of_dvd_mul_right hd'

private theorem core_ne_bot_no10 {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Sporadic.Mathieu.M23) (hc : pCore 2 B ≠ ⊥) : False := by
  have hcard : Nat.card (pCore 2 B) = 2 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp (core_card_dvd_two h e)).resolve_left
      (fun h1 => hc ((pCore 2 B).eq_bot_iff_card.mpr h1))
  let U := (pCore 2 B).map B.subtype
  have hU : Nat.card U = 2 := (card_map_of_injective B.subtype_injective).trans hcard
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hzG : orderOf (z : G) = 2 := (orderOf_coe z).trans hz
  have heq : zpowers (z : G) = U := eq_of_le_of_card_ge
    (zpowers_le.mpr z.property) (by rw [Nat.card_zpowers,hzG,hU])
  have hBN : B ≤ normalizer (U : Set G) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  rw [← heq, normalizer_zpowers_eq_centralizer_of_order_two _ hzG] at hBN
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 5
    ((by decide : 5 ∣ 20160).trans (quotient_card_dvd h))
  have hbG : orderOf (b : G) = 5 := (orderOf_coe b).trans hb
  have hcomm : Commute (z : G) (b : G) := (mem_centralizer_singleton_iff.mp (hBN b.property)).symm
  have hten : orderOf ((z : G) * (b : G)) = 10 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hzG,hbG]; decide),hzG,hbG]
  exact Sporadic.Mathieu.m23_orderOf_ne_ten (e ((z : G) * (b : G)))
    ((e.orderOf_eq _).trans hten)
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
open Equiv
private def ten : Equiv.Perm (Fin 8) :=
  swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 5 6
private theorem ten_order : orderOf ten = 10 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide +kernel)
  intro p hp hd
  have hcases : p = 2 ∨ p = 5 := by
    rcases hp.dvd_mul.mp (show p ∣ 2 * 5 from hd) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  rcases hcases with rfl | rfl <;> decide +kernel

variable {G : Type*} [Group G] [Finite G]
private theorem ordinary_no10 (S : Sylow 2 G) (B : Subgroup G)
    (eB : B ≃* alternatingGroup (Fin 8))
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    (hScard : Nat.card S = 128)
    (hno : ∀ x : G, orderOf x ≠ 10) : False := by
  let eA : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))
  let eAut : MulAut B ≃* Equiv.Perm (Fin 8) := (MulAut.congr eB).trans eA.symm
  have hAut : Nat.card (MulAut B) = 40320 := by
    rw [Nat.card_congr eAut.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hBcard : Nat.card B = 20160 := by
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hcenter : center B = ⊥ := by
    apply (center B).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr eB).toEquiv,
      alternatingGroup.center_eq_bot (by simp),card_bot]
  let f := B.normalizerMonoidHom
  let s : S →* f.range := f.rangeRestrict.comp (inclusion hn)
  have hs : Function.Injective s := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfaith]
    refine ⟨a.property, ?_⟩
    have hh : inclusion hn a ∈ f.ker := congrArg Subtype.val ha
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  have hSdiv : 128 ∣ Nat.card f.range := hScard ▸ card_dvd_of_injective s hs
  let b : B →* f.range := f.rangeRestrict.comp (inclusion B.le_normalizer)
  have hb : Function.Injective b := by
    intro x y he
    apply MulAut.conj_injective_of_center_eq_bot hcenter
    ext z
    exact congrArg (fun a : f.range => ((a : MulAut B) z : G)) he
  have hBdiv : 20160 ∣ Nat.card f.range := hBcard ▸ card_dvd_of_injective b hb
  have hdiv : 40320 ∣ Nat.card f.range := by
    have hh := Nat.lcm_dvd hSdiv hBdiv
    norm_num only [show Nat.lcm 128 20160 = 40320 by decide] at hh
    exact hh
  have hEq : Nat.card f.range = Nat.card (MulAut B) := by
    apply le_antisymm (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective)
    rw [hAut]
    exact Nat.le_of_dvd Nat.card_pos hdiv
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp (f.range.eq_top_of_card_eq hEq)
  obtain ⟨x,hx⟩ := hf (eAut.symm ten)
  have ho : orderOf (f x) = 10 := by rw [hx,eAut.symm.orderOf_eq,ten_order]
  have hd : 10 ∣ orderOf x := ho ▸ orderOf_map_dvd f x
  let y := x ^ (orderOf x / 10)
  have hy : orderOf (y : G) = 10 := by
    rw [orderOf_coe]
    exact orderOf_pow_orderOf_div (isOfFinOrder_of_finite x).orderOf_pos.ne' hd
  exact hno y hy
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]
/-- The literal Sylow-normalized local A₈ section cannot occur in M₂₃. -/
theorem not_mathieu_twentyThree (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Sporadic.Mathieu.M23) : False := by
  by_cases hc : pCore 2 B = ⊥
  · obtain ⟨a⟩ := quotient_equiv h
    let eB : B ≃* alternatingGroup (Fin 8) :=
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans a
    let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup B := eB.isSimpleGroup
    let := local_perfect hB
    have hz : center B = ⊥ :=
      (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
    let : IsQuasisimple B :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
    have hE := MainConverse.evenCharacteristic_of_model_equiv e
      MainConverse.m23_evenCharacteristic
    have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S (hE S) hB hn
    have hS : Nat.card S = 128 := by
      rw [S.card_eq_multiplicity,Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
      decide +kernel
    apply ordinary_no10 S B eB hn hf hS
    intro x hx
    exact Sporadic.Mathieu.m23_orderOf_ne_ten (e x) ((e.orderOf_eq x).trans hx)
  · exact core_ne_bot_no10 h e hc
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
