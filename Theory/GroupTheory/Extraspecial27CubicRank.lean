module
public import Theory.GroupTheory.PGroup.ExtraspecialCubicCentralInvolution
public import Theory.GroupAction.Extraspecial27InvolutionFixed
public import Theory.GroupTheory.PrimeRankCentralizer
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.Quasithin.Rank

public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Theory.GroupTheory.PGroup.RankOneInvolution

/-!
# Cubic actors on an extraspecial group of order 27

A center-fixing involution commuting with a cubic actor forces at least
nine fixed points. In ambient three-rank at most two those fixed points
force the cubic into the extraspecial subgroup, where central inversion
makes its inner action trivial. A nontrivial center-fixing two-group of
automorphisms has a unique involution, preserved by its full normalizer.

Source: Aschbacher–Smith 14.7.21(1), printed pp.1049–1050. The application
retains the actual Sylow subgroup and quotient conjugation action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace MulAut
variable {J : Type*} [Group J] [Finite J]

theorem cubic_fixed_card_ge_nine_of_extraspecial27_involution
    [IsExtraspecial 3 J] (hJ : Nat.card J=27)
    (a b : MulAut J) (ha : Function.Involutive a) (hb : b^3=1)
    (hab : a*b=b*a) (haZ : ∀ z ∈ center J, a z=z)
    (hbZ : ∀ z ∈ center J, b z=z)
    (hne : a ≠ 1) : 9≤Nat.card b.fixedSubgroup := by
  let W := center J
  let q := QuotientGroup.mk' W
  have hW : Nat.card W=3 := IsExtraspecial.center_order_p 3 J
  let : IsElementaryAbelian 3 (J ⧸ W) := IsExtraspecial.quotient_elementary_abelian 3 J
  have hfix : a.fixedSubgroup=W :=
    fixed_eq_center_of_extraspecial27_involution hJ a ha hne haZ
  have hoddW : Odd (Nat.card W) := by rw [hW]; decide
  have hinv := (a.quotient_inversion_of_odd_fixed_kernel ha W hoddW
    (fun x => (mem_fixedSubgroup a x).symm.trans (by rw [hfix]))).1
  have hmap : W.map b.toMonoidHom=W := by
    ext x
    constructor
    · rintro ⟨w,hw,rfl⟩; change b w∈W; rwa [hbZ w hw]
    · intro hx; exact ⟨x,hx,hbZ x hx⟩
  let β : MulAut (J ⧸ W) := QuotientGroup.congr W W b hmap
  have hβ (x : J) : β (q x)=q (b x) := rfl
  have hβ3 : β^3=1 := by
    ext u
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective W u
    change β (β (β (q x)))=q x
    rw [hβ,hβ,hβ,show b (b (b x))=x from DFunLike.congr_fun hb x]
  have hlift (x : J) (hx : β (q x)=q x) : b x=x := by
    apply fixed_of_central_displacement_of_inverted_quotient a b hab W le_rfl hoddW
      haZ hbZ hinv x
    apply (QuotientGroup.eq_one_iff _).mp
    change q (b x*x⁻¹)=1
    rw [map_mul,map_inv,←hβ,hx,mul_inv_cancel]
  let f : b.fixedSubgroup →* β.fixedSubgroup := {
    toFun x := ⟨q x,by
      rw [mem_fixedSubgroup,hβ,(mem_fixedSubgroup b x).mp x.property]⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' x y := Subtype.ext (map_mul q (x:J) (y:J)) }
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective W (u:J ⧸ W)
    refine ⟨⟨x,(mem_fixedSubgroup b x).mpr (hlift x ?_)⟩,Subtype.ext hx⟩
    rw [hx]; exact (mem_fixedSubgroup β u).mp u.property
  let e : f.ker ≃ W := {
    toFun x := ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val x.property)⟩
    invFun w := ⟨⟨w,(mem_fixedSubgroup b w).mpr (hbZ w w.property)⟩,
      Subtype.ext ((QuotientGroup.eq_one_iff _).mpr w.property)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc : Nat.card b.fixedSubgroup=3*Nat.card β.fixedSubgroup := by
    have hh := f.ker.card_mul_index
    rw [Nat.card_congr e,hW,index_ker,MonoidHom.range_eq_top.mpr hf,card_top] at hh
    exact hh.symm
  have hQ : Nat.card (J ⧸ W)=9 := by
    have hh := W.card_mul_index
    rw [hW,hJ,index] at hh
    omega
  have hbound := β.ternary_cubic_fixed_card_bound hβ3
  rw [hQ] at hbound
  have hdiv : Nat.card β.fixedSubgroup ∣ 9 := hQ ▸ β.fixedSubgroup.card_subgroup_dvd_card
  obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=2)).mp hdiv
  rw [hc,he]
  rw [he] at hbound
  interval_cases i
  all_goals norm_num at hbound
  all_goals norm_num

end MulAut

namespace Subgroup
variable {N : Type*} [Group N] [Finite N]

theorem cubic_action_trivial_of_extraspecial27_inverter
    (P : Subgroup N) [P.Normal] (hr : primeRank 3 N ≤ 2)
    (e : P ≃* HeisenbergPrime 3)
    (a : MulAut P) (ha : Function.Involutive a) (ha1 : a ≠ 1)
    (haZ : ∀ z ∈ center P, a z = z)
    (b : N) (hb : b ^ 3 = 1)
    (hab : a * (MulAut.conjNormal b : MulAut P) = (MulAut.conjNormal b : MulAut P) * a)
    (hbZ : ∀ z ∈ center P, (MulAut.conjNormal b : MulAut P) z = z) :
    (MulAut.conjNormal b : MulAut P) = 1 := by
  let β : MulAut P := MulAut.conjNormal b
  let : IsExtraspecial 3 P := (HeisenbergPrime.isExtraspecial (p := 3) (by decide)).of_mulEquiv e.symm
  have hc : Nat.card P = 27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hβ3 : β ^ 3 = 1 := by
    change (MulAut.conjNormal : N →* MulAut P) b ^ 3 = 1
    rw [←map_pow,hb,map_one]
  have hfixed : 9 ≤ Nat.card β.fixedSubgroup :=
    MulAut.cubic_fixed_card_ge_nine_of_extraspecial27_involution hc a β ha hβ3 hab haZ hbZ ha1
  have hP3 : IsPGroup 3 P := IsExtraspecial.isPGroup 3 P
  have hpow (x : P) : x ^ 3 = 1 := by
    apply e.injective
    rw [map_pow,HeisenbergPrime.pow_prime (by decide),map_one]
  have hrF : 2 ≤ primeRank 3 β.fixedSubgroup := by
    by_contra hh
    have hr1 : primeRank 3 β.fixedSubgroup ≤ 1 := by omega
    let : IsCyclic β.fixedSubgroup :=
      (hP3.to_subgroup β.fixedSubgroup).isCyclic_of_odd_of_elementary_card_le (by decide)
        (fun E hE => by
          let := hE
          exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr1 E)
    have hdiv : Nat.card β.fixedSubgroup ∣ 3 := by
      rw [←IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => Subtype.ext (hpow x))
    have hh := Nat.le_of_dvd (by decide : 0 < 3) hdiv
    omega
  let F := β.fixedSubgroup.map P.subtype
  have hrF' : primeRank 3 F = 2 := by
    have hFe : β.fixedSubgroup ≃* F := equivMapOfInjective _ P.subtype P.subtype_injective
    have hh := (primeRank_le_of_injective 3 F.subtype F.subtype_injective).trans hr
    rw [←primeRank_congr 3 hFe] at hh ⊢
    omega
  have hbF : b ∈ F := mem_of_prime_pow_eq_one_of_centralizes_rank_two hr F hrF' hb (by
    rintro x ⟨y,hy,rfl⟩
    have hh := congrArg Subtype.val ((MulAut.mem_fixedSubgroup β y).mp hy)
    change b * (y : N) * b⁻¹ = y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm)
  have hbP : b ∈ P := map_subtype_le β.fixedSubgroup hbF
  let W := center P
  have hW : Nat.card W = 3 := IsExtraspecial.center_order_p 3 P
  have hfix : a.fixedSubgroup = W :=
    MulAut.fixed_eq_center_of_extraspecial27_involution hc a ha ha1 haZ
  have hinv := (a.quotient_inversion_of_odd_fixed_kernel ha W (by rw [hW]; decide)
    (fun x => (MulAut.mem_fixedSubgroup a x).symm.trans (by rw [hfix]))).1
  let : IsElementaryAbelian 3 (P ⧸ W) := IsExtraspecial.quotient_elementary_abelian 3 P
  have hclass : _root_.commutator P ≤ W :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  apply MulEquiv.ext
  intro x
  apply MulAut.fixed_of_central_displacement_of_inverted_quotient a β hab W le_rfl
    (by rw [hW]; decide) haZ hbZ hinv x
  have hh := hclass (commutator_mem_commutator (mem_top (⟨b,hbP⟩ : P)) (mem_top x))
  exact hh
end Subgroup

namespace MulAut
open Subgroup
variable {J : Type*} [Group J] [Finite J] [IsExtraspecial 3 J]

/-- The unique involution of a center-fixing two-group is fixed by every normalizer. -/
theorem exists_involution_fixed_by_normalizer_of_extraspecial27
    (hJ : Nat.card J = 27) (R : Subgroup (MulAut J))
    (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hZ : ∀ a ∈ R, ∀ z ∈ center J, a z = z) :
    ∃ a : MulAut J, a ∈ R ∧ a ^ 2 = 1 ∧ a ≠ 1 ∧
      ∀ b ∈ normalizer (R : Set (MulAut J)), a * b = b * a := by
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hne
  have hfour (E : Subgroup R) (hE : IsElementaryAbelian 2 E) : Nat.card E ≠ 4 := by
    let := hE
    have hh := elementary_two_center_preserving_card_le_two hJ
      (R.subtype.comp E.subtype) (R.subtype_injective.comp E.subtype_injective)
      (fun a => hZ a a.val.property)
    omega
  obtain ⟨a,ha,_,huniq⟩ := hR.exists_central_involution_of_no_elementary_four hfour
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha
  refine ⟨a,a.property,congrArg Subtype.val ha2,fun he => ha1 (Subtype.ext he),?_⟩
  intro b hb
  let c : R := ⟨b * a * b⁻¹,(mem_normalizer_iff.mp hb a).mp a.property⟩
  have hc2 : c ^ 2 = 1 := by
    apply Subtype.ext
    change (b * (a : MulAut J) * b⁻¹)^2 = 1
    rw [conj_pow,show (a : MulAut J)^2 = 1 from congrArg Subtype.val ha2,mul_one,mul_inv_cancel]
  have hc1 : c ≠ 1 := by
    intro he
    have hh : b * (a : MulAut J) * b⁻¹ = 1 := congrArg Subtype.val he
    apply ha1
    apply Subtype.ext
    change (a : MulAut J) = 1
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one,one_mul] using
      congrArg (fun x => b⁻¹ * x * b) hh
  have he := congrArg Subtype.val ((huniq c hc2).resolve_left hc1)
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end MulAut

namespace Subgroup
variable {N J : Type*} [Group N] [Finite N] [Group J]

/-- Transfer the rank obstruction through an actual equivariant marking. -/
theorem cubic_action_trivial_of_extraspecial27_marking
    (P : Subgroup N) [P.Normal] (hr : primeRank 3 N ≤ 2)
    (e : P ≃* J) (eJ : J ≃* HeisenbergPrime 3)
    (a β : MulAut J) (ha : a^2=1) (ha1 : a ≠ 1)
    (haZ : ∀ z ∈ center J, a z = z)
    (b : N) (hb : b^3=1) (hab : a*β=β*a)
    (hbZ : ∀ z ∈ center J, β z=z)
    (hβ : ∀ x : P, e (MulAut.conjNormal b x) = β (e x)) : β=1 := by
  let α := MulAut.congr e.symm
  have hact : α β = (MulAut.conjNormal b : MulAut P) := by
    apply MulEquiv.ext
    intro x
    apply e.injective
    change e (e.symm (β (e x))) = e (MulAut.conjNormal b x)
    rw [e.apply_symm_apply,hβ]
  have ha2 : (α a)^2=1 := by rw [←map_pow,ha,map_one]
  have hinv : Function.Involutive (α a) := fun x =>
    DFunLike.congr_fun (show (α a)*(α a)=1 by simpa only [pow_two] using ha2) x
  have hcenter (γ : MulAut J) (hγ : ∀ z ∈ center J, γ z=z) :
      ∀ z ∈ center P, α γ z=z := by
    intro z hz
    apply e.injective
    change e (e.symm (γ (e z))) = e z
    rw [e.apply_symm_apply,hγ (e z) ((centerCongr e) ⟨z,hz⟩).property]
  have hcomm : α a * (MulAut.conjNormal b : MulAut P) =
      (MulAut.conjNormal b : MulAut P) * α a := by
    rw [←hact,←map_mul,←map_mul,hab]
  have hz : ∀ z ∈ center P, (MulAut.conjNormal b : MulAut P) z=z := by
    rw [←hact]; exact hcenter β hbZ
  have ht := cubic_action_trivial_of_extraspecial27_inverter P hr (e.trans eJ)
    (α a) hinv (fun he => ha1 (α.injective (he.trans α.map_one.symm)))
    (hcenter a haZ) b hb hcomm hz
  exact α.injective (hact.trans (ht.trans α.map_one.symm))
end Subgroup

namespace MulAut
open Subgroup
/-- A cubic automorphism fixes a center of order three pointwise. -/
theorem fixes_cubic_center_of_cube_eq_one
    {J : Type*} [Group J] [Finite J] (hc : Nat.card (center J)=3)
    (b : MulAut J) (hb : b^3=1) : ∀ z ∈ center J, b z=z := by
  let : IsCyclic (center J) := isCyclic_of_prime_card hc
  have hcard : Nat.card (MulAut (center J))=2 := by
    rw [IsCyclic.card_mulAut,hc]; decide
  let f := MulAut.characteristic (center J)
  have hcube : (f b)^3=1 := by rw [←map_pow,hb,map_one]
  have hf : f b=1 := (show Nat.Coprime (Nat.card (MulAut (center J))) 3 by
    rw [hcard]; decide).pow_left_bijective.injective (hcube.trans (one_pow 3).symm)
  intro z hz
  exact congrArg (fun a : MulAut (center J) => (a ⟨z,hz⟩ : J)) hf
end MulAut
