module

public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Complement

/-!
# Cubic Sylow census in the quaternion–cubic complement

SL₂(3) has four Sylow3 subgroups by the Sylow congruence and its nonnormal
upper root group. A normal index-two extension has exactly the same cubic
Sylow subgroups. A surjection with 3-group kernel also preserves the census.
Thus a split group of order243·48 with this complement has cubic Sylow
normalizers of order2916. All transports use the literal quotient maps.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
namespace Sylow
variable {G H:Type*} [Group G] [Group H]
theorem card_eq_of_surjective_pgroup_kernel {p:ℕ}
    (f:G→*H) (hf:Function.Surjective f) (hk:IsPGroup p f.ker) :
    Nat.card (Sylow p G)=Nat.card (Sylow p H) := by
  let F:Sylow p H→Sylow p G:=fun P=>P.comapOfKerIsPGroup f hk
    (by rw [MonoidHom.range_eq_top.mpr hf];exact le_top)
  have hi:Function.Injective F:=by
    intro P Q he
    apply Sylow.ext
    apply comap_injective hf
    exact congrArg Sylow.toSubgroup he
  have hs:Function.Surjective F:=by
    intro P
    obtain ⟨Q,hQ⟩:=P.exists_comap_eq_of_ker_isPGroup hk
    exact ⟨Q,Sylow.ext hQ⟩
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hi,hs⟩)).symm

theorem card_eq_of_mulEquiv {p:ℕ} (e:G≃*H) :
    Nat.card (Sylow p G)=Nat.card (Sylow p H) :=
  card_eq_of_surjective_pgroup_kernel e.toMonoidHom e.surjective
    (IsPGroup.ker_isPGroup_of_injective e.injective)
end Sylow
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem cubic_sylow_count_of_sl2_three (hG:Nat.card G=24)
    (e:G≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card (Sylow 3 G)=4 := by
  let P:Sylow 3 G:=default
  have hc:Nat.card P=3:=by
    have hf:Nat.factorization 24 3=1:=by
      rw [Nat.factorization_def 24 Nat.prime_three,show (24:ℕ)=3^1*8 by norm_num,
        padicValNat_base_pow_mul (by norm_num) (by norm_num) 1,
        show padicValNat 3 8=0 from padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))]
    rw [P.card_eq_multiplicity,hG,hf,pow_one]
  have hi:P.index=8:=by have hh:=P.card_mul_index;rw [hc,hG] at hh;omega
  have hd:=P.card_dvd_index
  rw [hi] at hd
  have hm:=card_sylow_modEq_one 3 G
  have hn:Nat.card (Sylow 3 G)≠1:=by
    intro hh
    have he:=Sylow.card_eq_of_mulEquiv (p:=3) e
    rw [hh] at he
    let :Subsingleton (Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))):=
      (Nat.card_eq_one_iff_unique.mp he.symm).1
    exact Matrix.SpecialLinearGroup.no_normal_sylow (ZMod 3) 3 default
      (Sylow.normal_of_subsingleton default)
  have hh:=Nat.mem_divisors.mpr ⟨hd,(by decide:8≠0)⟩
  have he:Nat.divisors 8={1,2,4,8}:=by decide
  simp only [he,Finset.mem_insert,Finset.mem_singleton] at hh
  change Nat.card (Sylow 3 G)%3=1%3 at hm
  omega

theorem cubic_sylow_count_of_sl2_three_index_two (J:Subgroup G) [J.Normal]
    (hG:Nat.card G=48) (hJ:Nat.card J=24)
    (e:J≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card (Sylow 3 G)=4 := by
  have hi:J.index=2:=by have hh:=J.card_mul_index;rw [hJ,hG] at hh;omega
  have hle (P:Sylow 3 G): (P:Subgroup G)≤J:=by
    have hc:Nat.card P=3:=by
      have hf:Nat.factorization 48 3=1:=by
        rw [Nat.factorization_def 48 Nat.prime_three,show (48:ℕ)=3^1*16 by norm_num,
          padicValNat_base_pow_mul (by norm_num) (by norm_num) 1,
          show padicValNat 3 16=0 from padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))]
      rw [P.card_eq_multiplicity,hG,hf,pow_one]
    intro x hx
    have hx3:x^3=1:=by
      have hh:=pow_card_eq_one' (x:=(⟨x,hx⟩:↥(P:Subgroup G)))
      rw [hc] at hh
      exact congrArg Subtype.val hh
    let q:=QuotientGroup.mk' J
    have hq3:(q x)^3=1:=by rw [←map_pow,hx3,map_one]
    have hq2:(q x)^2=1:=by
      have hh:=pow_card_eq_one' (x:=q x)
      change (q x)^J.index=1 at hh
      rwa [hi] at hh
    have hd:=Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq2) (orderOf_dvd_of_pow_eq_one hq3)
    have ho:orderOf (q x)=1:=Nat.dvd_one.mp (by simpa using hd)
    exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp ho)
  let F:Sylow 3 G→Sylow 3 J:=fun P=>P.subtype (hle P)
  have hFi:Function.Injective F:=by intro P Q he;exact Sylow.subtype_injective he
  have hFs:Function.Surjective F:=by
    intro Q
    obtain ⟨P,hP⟩:=Q.exists_comap_subtype_eq
    exact ⟨P,Sylow.ext hP⟩
  rw [Nat.card_congr (Equiv.ofBijective F ⟨hFi,hFs⟩)]
  exact cubic_sylow_count_of_sl2_three hJ e
end Subgroup

namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
/-- A normal ternary kernel preserves the cubic Sylow census. -/
theorem cubic_sylow_normalizer_card_of_split (D K:Subgroup G) [D.Normal]
    (hD:Nat.card D=243) (hK:Nat.card K=48) (hcomp:D.IsComplement' K)
    (hcount:Nat.card (Sylow 3 K)=4) (P:Sylow 3 G) :
    Nat.card (normalizer (P:Set G))=2916 := by
  have hG:Nat.card G=11664:=by
    have hh:=hcomp.card_mul_card
    rw [hD,hK] at hh
    exact hh.symm
  have hk:IsPGroup 3 (QuotientGroup.mk' D).ker:=by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n:=5) hD
  have hc:Nat.card (Sylow 3 G)=4:=by
    rw [Sylow.card_eq_of_surjective_pgroup_kernel (QuotientGroup.mk' D)
      (QuotientGroup.mk'_surjective D) hk,
      Sylow.card_eq_of_mulEquiv hcomp.symm.QuotientMulEquiv,hcount]
  have hh:=(normalizer (P:Set G)).card_mul_index
  rw [←P.card_eq_index_normalizer,hc,hG] at hh
  omega
end Subgroup
