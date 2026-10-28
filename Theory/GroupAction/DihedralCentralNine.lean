module

public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Dihedral actions on two central ternary planes

Two elementary nine-groups generate over a central elementary nine.
A reflection swaps their noncentral generators, while the other reflection
fixes one and inverts the other modulo the center. Their product fixes the
generator commutator but inverts the central layer, so the commutator is
trivial. The original generators then give exponent three.

This is the elementary-abelian step in Aschbacher (1994), Lemma 45.7, p245.
-/
open Subgroup
open scoped commutatorElement
namespace MulAut
variable {P : Type*} [Group P] [Finite P]
omit [Finite P] in
private theorem swapped_commutator_eq_one (X : Subgroup P) (hX : X≤center P)
    (ho : Odd (Nat.card X)) (a b : P) (hc : ⁅a,b⁆∈X)
    (s t : MulAut P) (hsa : s a=b) (hsb : s b=a)
    (hta : t a=a) (htb : t b*b∈X)
    (hr : ∀x∈X,(s*t) x=x⁻¹) : Commute a b := by
  let c := ⁅a,b⁆
  have hsc : s c=c⁻¹ := by
    rw [map_commutatorElement,hsa,hsb,commutatorElement_inv]
  have htc : t c=c⁻¹ := by
    let d := t b*b
    have hd : d∈center P := hX htb
    have htb' : t b=d*b⁻¹ := by dsimp [d]; group
    rw [map_commutatorElement,hta,htb',commutatorElement_mul_right_eq_mul_conj]
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hd a),one_mul,
      commutatorElement_inv_right,←commutatorElement_inv]
    have hcc : c⁻¹∈center P := (center P).inv_mem (hX hc)
    calc
      d*(b⁻¹*c⁻¹*b)*d⁻¹ = d*c⁻¹*d⁻¹ := by rw [mem_center_iff.mp hcc b⁻¹]; group
      _ = c⁻¹ := by rw [mem_center_iff.mp hcc d,mul_inv_cancel_right]
  have hfix : (s*t) c=c := by
    change s (t c)=c
    rw [htc,map_inv,hsc,inv_inv]
  have hi : c=c⁻¹ := hfix.symm.trans (hr c hc)
  have hsquare : (⟨c,hc⟩:X)^2=1 := by
    apply Subtype.ext
    change c^2=1
    rw [pow_two]
    calc
      c*c = c⁻¹*c := congrArg (fun x=>x*c) hi
      _ = 1 := inv_mul_cancel c
  have he : (⟨c,hc⟩:X)=1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ho.coprime_two_right
      (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one hsquare))
  exact commutatorElement_eq_one_iff_commute.mp (congrArg Subtype.val he)

public theorem elementary_of_dihedral_central_generators
    (X : Subgroup P) [IsElementaryAbelian 3 X] (hX : X≤center P)
    (a b : P) (ha : a^3=1) (hb : b^3=1)
    (hgen : (X⊔zpowers a)⊔zpowers b=⊤) (hc : ⁅a,b⁆∈X)
    (s t : MulAut P) (hsa : s a=b) (hsb : s b=a)
    (hta : t a=a) (htb : t b*b∈X)
    (hr : ∀x∈X,(s*t) x=x⁻¹) : IsElementaryAbelian 3 P := by
  have ho : Odd (Nat.card X) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 X).exists_card_eq
    rw [hn]
    exact Odd.pow (by decide : Odd 3)
  have hab := swapped_commutator_eq_one X hX ho a b hc s t hsa hsb hta htb hr
  have hca : a∈center P := by
    have hl : (X⊔zpowers a)⊔zpowers b ≤ centralizer ({a}:Set P) := sup_le
      (sup_le (hX.trans (center_le_centralizer _))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hab.symm.eq))
    rw [hgen] at hl
    exact mem_center_iff.mpr (fun x=>mem_centralizer_singleton_iff.mp (hl (mem_top x)))
  have hcb : b∈center P := by
    have hl : (X⊔zpowers a)⊔zpowers b ≤ centralizer ({b}:Set P) := sup_le
      (sup_le (hX.trans (center_le_centralizer _))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hab.eq)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    rw [hgen] at hl
    exact mem_center_iff.mpr (fun x=>mem_centralizer_singleton_iff.mp (hl (mem_top x)))
  have habel : IsMulCommutative P := center_eq_top_iff.mp (top_unique (hgen ▸
    sup_le (sup_le hX (zpowers_le.mpr hca)) (zpowers_le.mpr hcb)))
  let : IsMulCommutative P := habel
  let : CommGroup P := IsMulCommutative.instCommGroup
  let C : Subgroup P := {
    carrier := {x|x^3=1}
    one_mem' := one_pow 3
    mul_mem' := fun hx hy=>by
      change _^3=1 at hx hy ⊢
      rw [mul_pow,hx,hy,mul_one]
    inv_mem' := fun hx=>by
      change _^3=1 at hx ⊢
      rw [inv_pow,hx,inv_one] }
  have hC : C=⊤ := top_unique (hgen ▸ sup_le
    (sup_le (fun x hx=>elemPow_eq_one_of_isElementaryAbelian x hx) (zpowers_le.mpr ha))
    (zpowers_le.mpr hb))
  exact { toIsMulCommutative := habel
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
            (fun x=>show x∈C from hC ▸ mem_top x) }

private theorem exists_central_nine_generator
    (X A : Subgroup P) [IsElementaryAbelian 3 A]
    (hX : X≤center P) (hX9 : Nat.card X=9) (hA9 : Nat.card A=9)
    (hXA : Nat.card (X⊓A : Subgroup P)=3) :
    ∃a∈A, a^3=1 ∧ X⊔zpowers a=X⊔A := by
  have hnA : ¬A≤X := by
    intro hh
    rw [inf_eq_right.mpr hh,hA9] at hXA
    omega
  obtain ⟨a,ha,hax⟩ := SetLike.not_le_iff_exists.mp hnA
  have ha3 := elemPow_eq_one_of_isElementaryAbelian (p:=3) a ha
  have hao : orderOf a=3 := orderOf_eq_prime ha3 (fun he=>hax (he ▸ X.one_mem))
  have hnorm : (⊤:Subgroup P)≤normalizer (X:Set P) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact fun g _ x hx=>(mem_center_iff.mp (hX hx) g).symm
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes X A (le_top.trans hnorm)
  rw [hX9,hA9,hXA] at hprod
  have hcard : Nat.card (X⊔zpowers a : Subgroup P)=27 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint X (zpowers a) (le_top.trans hnorm)
      (X.disjoint_zpowers_of_prime_order_not_mem a hao hax),hX9,Nat.card_zpowers,hao]
  refine ⟨a,ha,ha3,eq_of_le_of_card_ge (sup_le_sup_left (zpowers_le.mpr ha) X) ?_⟩
  rw [hcard]
  omega

public theorem elementary_of_dihedral_central_nines
    (X A : Subgroup P) [IsElementaryAbelian 3 X] [IsElementaryAbelian 3 A]
    (hX : X≤center P) (hX9 : Nat.card X=9) (hA9 : Nat.card A=9)
    (hXA : Nat.card (X⊓A : Subgroup P)=3)
    (s t : MulAut P) (hs : Function.Involutive s) (hsX : X.map s.toMonoidHom=X)
    (hgen : (X⊔A)⊔A.map s.toMonoidHom=⊤) (hc : _root_.commutator P≤X)
    (hta : ∀a∈A,t a=a) (htb : ∀b∈A.map s.toMonoidHom,t b*b∈X)
    (hr : ∀x∈X,(s*t) x=x⁻¹) : IsElementaryAbelian 3 P := by
  obtain ⟨a,ha,ha3,hag⟩ := exists_central_nine_generator X A hX hX9 hA9 hXA
  have hbg := congrArg (fun K:Subgroup P=>K.map s.toMonoidHom) hag
  rw [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,hsX] at hbg
  have hwhole : (X⊔zpowers a)⊔zpowers (s a)=⊤ := by
    apply top_unique
    rw [←hgen]
    apply sup_le
    · exact hag.ge.trans le_sup_left
    · exact (show A.map s.toMonoidHom≤X⊔A.map s.toMonoidHom from le_sup_right).trans
        (hbg.ge.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  exact elementary_of_dihedral_central_generators X hX a (s a) ha3
    (by rw [←map_pow,ha3,map_one]) hwhole
    (hc (commutator_mem_commutator (mem_top a) (mem_top (s a)))) s t rfl (hs a)
    (hta a ha) (htb (s a) (mem_map_of_mem s.toMonoidHom ha)) hr
end MulAut
