module
public import Theory.SpecificGroups.HeisenbergPrime.ScalarAction
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
/-!
# Square roots of quotient inversion on the ternary Heisenberg group

On the two-dimensional ternary central quotient, a square root of minus
identity has determinant one. Explicit Heisenberg coordinates identify
this determinant with the action on the center. Thus every automorphism
of order four fixes the center. Consequently a faithful actor of order
four with nontrivial center action is elementary abelian.

The finite checks use only the 27 coordinate triples and 81 coefficient
quadruples, while all group and quotient transports are structural.
Source application: Aschbacher–Smith, 14.7.15(2), printed p.1047.
-/
public noncomputable section
open Subgroup
open scoped commutatorElement
namespace HeisenbergPrime
private abbrev P := HeisenbergPrime 3
private def x : P := ⟨1,0,0⟩
private def y : P := ⟨0,1,0⟩
private def z (c : ZMod 3) : P := ⟨0,0,c⟩
private theorem coordinates_product : ∀ v : P,
    v = x ^ v.a.val * y ^ v.b.val * z (v.c - v.a*v.b) := by
  intro ⟨a,b,c⟩
  apply HeisenbergPrime.ext <;> revert a b c <;> decide +kernel
private theorem action_coordinates (α : MulAut P) (v : P) :
    (α v).a = (α x).a * v.a + (α y).a * v.b ∧
    (α v).b = (α x).b * v.a + (α y).b * v.b := by
  have hz (c : ZMod 3) : (α (z c)).a = 0 ∧ (α (z c)).b = 0 := by
    apply (mem_center_iff _).mp
    exact ((MulAut.characteristic (center P) α)
      ⟨z c,(mem_center_iff _).mpr ⟨rfl,rfl⟩⟩).property
  have he := congrArg α (coordinates_product v)
  rw [map_mul,map_mul,map_pow,map_pow] at he
  constructor
  · rw [he]
    simp only [mul_a,pow_a,hz,ZMod.natCast_zmod_val,add_zero]
    ring
  · rw [he]
    simp only [mul_b,pow_b,hz,ZMod.natCast_zmod_val,add_zero]
    ring
private theorem determinant_of_square_neg_one : ∀ a b c d : ZMod 3,
    a*a+b*c = -1 → c*a+d*c = 0 → a*b+b*d = 0 → c*b+d*d = -1 →
    a*d-b*c = 1 := by decide +kernel

/-- A square root of inversion on the central quotient fixes the center. -/
theorem fixes_center_of_square_inverts_quotient
    {G : Type*} [Group G] (e : G ≃* HeisenbergPrime 3) (α : MulAut G)
    (hi : ∀ v : G, α (α v) * v ∈ center G) :
    ∀ v ∈ center G, α v = v := by
  let β := e.symm.trans (α.trans e)
  have hβ (v : P) : β v = e (α (e.symm v)) := rfl
  have hi' (v : P) : β (β v) * v ∈ center P := by
    have hh := (centerCongr e ⟨_,hi (e.symm v)⟩).property
    change e (α (α (e.symm v)) * e.symm v) ∈ center P at hh
    simpa only [hβ,map_mul,MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply] using hh
  have hiab (v : P) : (β (β v)).a = -v.a ∧ (β (β v)).b = -v.b := by
    have hh := (mem_center_iff _).mp (hi' v)
    simpa only [mul_a,mul_b,add_eq_zero_iff_eq_neg] using hh
  have hxx := (action_coordinates β (β x))
  have hyy := (action_coordinates β (β y))
  have hd : (β x).a * (β y).b - (β y).a * (β x).b = 1 := by
    apply determinant_of_square_neg_one
    · exact hxx.1.symm.trans (hiab x).1
    · exact hxx.2.symm.trans (hiab x).2
    · exact hyy.1.symm.trans (hiab y).1
    · exact hyy.2.symm.trans (hiab y).2
  have hfix (v : P) (hv : v ∈ center P) : β v = v := by
    have hvab := (mem_center_iff _).mp hv
    have hb := (mem_center_iff _).mp
      ((MulAut.characteristic (center P) β) ⟨v,hv⟩).property
    change (β v).a = 0 ∧ (β v).b = 0 at hb
    apply HeisenbergPrime.ext (hb.1.trans hvab.1.symm) (hb.2.trans hvab.2.symm)
    have hh := center_coordinate_determinant (MulEquiv.refl P) β
      (β x).a (β y).a (β x).b (β y).b
      (fun w => (action_coordinates β w).1) (fun w => (action_coordinates β w).2) v hv
    simpa only [MulEquiv.refl_apply,hd,one_mul] using hh
  intro v hv
  apply e.injective
  simpa only [hβ,MulEquiv.symm_apply_apply] using
    hfix (e v) ((centerCongr e ⟨v,hv⟩).property)
end HeisenbergPrime

namespace IsExtraspecial
variable {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
/-- Every automorphism of order four of the extraspecial ternary cube fixes its center. -/
theorem order_four_aut_fixes_center
    (e : P ≃* HeisenbergPrime 3) (α : MulAut P)
    (h4 : α^4=1) (h2 : α^2≠1) : ∀ z ∈ center P, α z = z := by
  have hc : Nat.card P = 27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hb : Function.Involutive (α^2 : MulAut P) := by
    intro x
    have he : (α^2)^2=1 := by rw [←pow_mul]; exact h4
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  have hfix : ∀ z ∈ center P, (α^2) z = z := by
    let f := MulAut.characteristic (center P) α
    have hcard : Nat.card (MulAut (center P)) = 2 := by
      let : IsCyclic (center P) := isCyclic_of_prime_card (center_order_p 3 P)
      rw [IsCyclic.card_mulAut,center_order_p 3 P]
      decide
    have hf : f^2=1 := by rw [←hcard]; exact pow_card_eq_one'
    have hf' : MulAut.characteristic (center P) (α^2)=1 := by rwa [map_pow]
    intro z hz
    exact congrArg (fun a : MulAut (center P) => (a ⟨z,hz⟩ : P)) hf'
  have hinv := (exponent_and_frattini_inversion_of_card27 hc (α^2) hb h2 hfix).2
  apply HeisenbergPrime.fixes_center_of_square_inverts_quotient e α
  intro x
  rw [←frattini_eq_center_three]
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (frattini P) (α (α x) * x) = 1
  rw [map_mul,show α (α x) = (α^2) x from rfl,hinv,inv_mul_cancel]

/-- A faithful order-four actor with nontrivial center action is elementary. -/
theorem four_actor_elementary_of_center_movement
    {A : Type*} [Group A] [Finite A]
    (e : P ≃* HeisenbergPrime 3) (α : A →* MulAut P)
    (hf : Function.Injective α) (hc : Nat.card A = 4)
    (hm : ¬ ∀ a : A, ∀ z ∈ center P, α a z = z) :
    IsElementaryAbelian 2 A := by
  let : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hc
  refine { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one ?_ }
  intro a
  by_contra ha
  have ho4 : orderOf a = 4 := by
    have hd := orderOf_dvd_natCard a
    rw [hc] at hd
    obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf a ∣ 2^2 from hd)
    interval_cases n
    · have he1 : a = 1 := orderOf_eq_one_iff.mp he
      exact (ha (by rw [he1,one_pow])).elim
    · exact (ha (by simpa only [he,pow_one] using pow_orderOf_eq_one a)).elim
    · exact he
  have hpow : a^4=1 := ho4 ▸ pow_orderOf_eq_one a
  have hfix := order_four_aut_fixes_center e (α a)
    (by rw [←map_pow,hpow,map_one]) (fun hh => ha (hf (by rwa [map_pow,map_one])))
  have hgen : zpowers a = ⊤ := eq_of_le_of_card_ge le_top (by rw [card_top,hc,Nat.card_zpowers,ho4])
  apply hm
  intro b z hz
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp (hgen ▸ mem_top b)
  have he : MulAut.characteristic (center P) (α a) = 1 := by
    ext v
    exact hfix v v.property
  have he' : MulAut.characteristic (center P) (α (a^n)) = 1 := by
    rw [map_zpow,map_zpow,he,one_zpow]
  exact congrArg (fun f : MulAut (center P) => (f ⟨z,hz⟩ : P)) he'
end IsExtraspecial
