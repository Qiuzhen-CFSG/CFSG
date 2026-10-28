module
public import Theory.LinearAlgebra.OrderFourFixedLine
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
/-!
# Cubic symmetry on a binary six-space

A fixed-free three-group makes every stable kernel even-dimensional. For an
order-four operator whose square moves two dimensions, this identifies its
fixed plane with the square's displacement plane. More generally, even
kernel growth forces a nilpotent operator on this six-space to have cube zero.
Thus a commuting operator of two-power order has fourth power one.

These structural calculations supply the original point-core action in
Aschbacher–Smith, 14.7.15(2) and 14.7.16(3), printed pp.1047–1048.
-/
public noncomputable section
namespace LinearMap
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
/-- Even kernel dimensions force the order-four actor's fixed plane to be
exactly the displacement plane of its square. -/
theorem order_four_fixed_plane_of_even_kernels
    (hd : finrank (ZMod 2) V=6)
    (x : Module.End (ZMod 2) V) (h4 : x^4=1)
    (hr : finrank (ZMod 2) (x^2-1).range=2)
    (he1 : Even (finrank (ZMod 2) (x-1).ker))
    (he3 : Even (finrank (ZMod 2) ((x-1)^3).ker)) :
    (x-1).ker=(x^2-1).range ∧ finrank (ZMod 2) (x-1).ker=2 := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0<finrank (ZMod 2) V)
  let : CharP (Module.End (ZMod 2) V) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  let N := x-1
  have hN2 : N^2=x^2-1 := by
    simpa only [one_pow] using sub_pow_char_of_commute 2 (Commute.one_right x)
  have hN4 : N^4=0 := by
    have hh := sub_pow_char_pow_of_commute 2 2 (Commute.one_right x)
    simpa only [show 2^2=4 by decide,one_pow,h4,sub_self] using hh
  have hr2 : finrank (ZMod 2) (N^2).range=2 := hN2.symm ▸ hr
  have hdim := (N^2).finrank_range_add_finrank_ker
  rw [hd,hr2] at hdim
  have hk2 : finrank (ZMod 2) (N^2).ker=4 := by omega
  have hker : N.ker≤(N^2).ker := by
    intro v hv
    change N (N v)=0
    change N v=0 at hv
    rw [hv,map_zero]
  have hk13 := Submodule.finrank_mono hker
  have hpos : 0<finrank (ZMod 2) N.ker := by
    by_contra hn
    have hz : N.ker=⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hstable : LinearMap.ker (N^0)=LinearMap.ker (N^1) := by
      simpa only [pow_zero,pow_one,Module.End.one_eq_id,LinearMap.ker_id] using hz.symm
    have he := Module.End.ker_pow_constant hstable 4
    have hbad : (⊥ : Submodule (ZMod 2) V)=⊤ := by
      simpa only [pow_zero,zero_add,hN4,LinearMap.ker_zero,Module.End.one_eq_id,LinearMap.ker_id] using he
    exact bot_ne_top hbad
  have hne4 : finrank (ZMod 2) N.ker≠4 := by
    intro hh
    have he : N.ker=(N^2).ker := Submodule.eq_of_le_of_finrank_eq hker (hh.trans hk2.symm)
    have hstable : LinearMap.ker (N^1)=LinearMap.ker (N^2) := by simpa only [pow_one] using he
    have htop : N.ker=⊤ := by simpa [hN4] using Module.End.ker_pow_constant hstable 3
    have hdimN : finrank (ZMod 2) N.ker=6 := by rw [htop,finrank_top,hd]
    omega
  have hk1 : finrank (ZMod 2) N.ker=2 := by
    obtain ⟨n,hn⟩ := he1
    change finrank (ZMod 2) N.ker=n+n at hn
    omega
  have h23 : (N^2).ker≤(N^3).ker := by
    intro v hv
    change N (N (N v))=0
    change N (N v)=0 at hv
    rw [hv,map_zero]
  have hlow3 := Submodule.finrank_mono h23
  have hhigh3 := Submodule.finrank_le (N^3).ker
  have hne3 : finrank (ZMod 2) (N^3).ker≠4 := by
    intro hh
    have he : (N^2).ker=(N^3).ker := Submodule.eq_of_le_of_finrank_eq h23 (hk2.trans hh.symm)
    have htop : (N^2).ker=⊤ := by simpa [hN4] using Module.End.ker_pow_constant he 2
    rw [htop,finrank_top,hd] at hk2
    omega
  have hk3 : finrank (ZMod 2) (N^3).ker=6 := by
    obtain ⟨n,hn⟩ := he3
    change finrank (ZMod 2) (N^3).ker=n+n at hn
    rw [hd] at hhigh3
    omega
  have hzero : N^3=0 := LinearMap.ker_eq_top.mp
    (Submodule.eq_top_of_finrank_eq (hk3.trans hd.symm))
  have hle : (N^2).range ≤ N.ker := by
    rintro _ ⟨v,rfl⟩
    exact LinearMap.congr_fun hzero v
  have heq : (N^2).range=N.ker := Submodule.eq_of_le_of_finrank_eq hle (hr2.trans hk1.symm)
  exact ⟨by rw [←hN2]; exact heq.symm,hk1⟩
end LinearMap

namespace Representation
open Subgroup BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem even_ker_finrank_of_commuting_three_group
    (ρ : Representation (ZMod 2) G V) (Z : Subgroup G) (hZ : IsPGroup 3 Z)
    (hfixed : invariants (ρ.comp Z.subtype)=⊥)
    (k : Module.End (ZMod 2) V)
    (hcomm : ∀ z : Z, Commute (ρ z) k) : Even (Module.finrank (ZMod 2) k.ker) := by
  let S : Subrepresentation (ρ.comp Z.subtype) := {
    toSubmodule := k.ker
    apply_mem_toSubmodule z v hv := by
      change k (ρ z v)=0
      change k v=0 at hv
      have hh := LinearMap.congr_fun (hcomm z).eq v
      change ρ z (k v)=k (ρ z v) at hh
      rw [←hh,hv,map_zero] }
  have hs : invariants S.toRepresentation=⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    have hh : (v : V) ∈ invariants (ρ.comp Z.subtype) := by
      intro z
      exact congrArg Subtype.val (hv z)
    change (v : V)=0
    simpa only [hfixed,Submodule.mem_bot] using hh
  have hh := orderOf_two_dvd_finrank_of_isPGroup S.toRepresentation
    Nat.prime_three (by decide) hZ hs
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at hh
  exact even_iff_two_dvd.mpr hh

theorem order_four_fixed_plane_of_commuting_three_group
    (ρ : Representation (ZMod 2) G V) (Z : Subgroup G) (hZ : IsPGroup 3 Z)
    (hfixed : invariants (ρ.comp Z.subtype)=⊥)
    (hd : Module.finrank (ZMod 2) V=6)
    (x : Module.End (ZMod 2) V) (h4 : x^4=1)
    (hr : Module.finrank (ZMod 2) (x^2-1).range=2)
    (hcomm : ∀ z : Z, Commute (ρ z) x) :
    (x-1).ker=(x^2-1).range ∧ Module.finrank (ZMod 2) (x-1).ker=2 := by
  apply LinearMap.order_four_fixed_plane_of_even_kernels hd x h4 hr
  · exact even_ker_finrank_of_commuting_three_group ρ Z hZ hfixed _
      (fun z => (hcomm z).sub_right (Commute.one_right _))
  · exact even_ker_finrank_of_commuting_three_group ρ Z hZ hfixed _
      (fun z => ((hcomm z).sub_right (Commute.one_right _)).pow_right 3)
end Representation

namespace LinearMap
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
theorem nilpotent_cube_zero_of_six_even_kernels
    (hd : finrank (ZMod 2) V = 6) (k : Module.End (ZMod 2) V)
    (hnil : IsNilpotent k)
    (he : ∀ n : ℕ, Even (finrank (ZMod 2) (k^n).ker)) : k^3=0 := by
  have hmono (n : ℕ) : (k^n).ker ≤ (k^(n+1)).ker := by
    rw [pow_succ']
    exact LinearMap.ker_le_ker_comp _ _
  have hgrow (n : ℕ) : finrank (ZMod 2) (k^n).ker=6 ∨
      finrank (ZMod 2) (k^n).ker+2 ≤ finrank (ZMod 2) (k^(n+1)).ker := by
    by_cases hh : (k^n).ker=(k^(n+1)).ker
    · left
      obtain ⟨m,hm⟩ := hnil
      have ht := Module.End.ker_pow_constant hh m
      rw [pow_add,hm,mul_zero,LinearMap.ker_zero] at ht
      rw [ht,finrank_top,hd]
    · right
      have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono n) hh)
      obtain ⟨a,ha⟩ := he n
      obtain ⟨b,hb⟩ := he (n+1)
      omega
  have hg0 := hgrow 0
  have hg1 := hgrow 1
  have hg2 := hgrow 2
  have hm1 := Submodule.finrank_mono (hmono 1)
  have hm2 := Submodule.finrank_mono (hmono 2)
  have hb := Submodule.finrank_le (k^3).ker
  have hzero : finrank (ZMod 2) (k^0).ker=0 := by
    change finrank (ZMod 2) (LinearMap.id (R := ZMod 2) (M := V)).ker=0
    rw [LinearMap.ker_id]
    exact finrank_bot _ _
  simp only [Nat.reduceAdd] at hg0 hg1 hg2 hm1 hm2
  have hthree : finrank (ZMod 2) (k^3).ker=finrank (ZMod 2) V := by omega
  exact LinearMap.ker_eq_top.mp (Submodule.eq_top_of_finrank_eq hthree)
end LinearMap

namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
theorem two_power_cube_zero_of_commuting_three_group
    (ρ : Representation (ZMod 2) G V) (Z : Subgroup G) (hZ : IsPGroup 3 Z)
    (hfixed : invariants (ρ.comp Z.subtype)=⊥)
    (hd : Module.finrank (ZMod 2) V=6)
    (x : Module.End (ZMod 2) V) {n : ℕ} (hx : x^(2^n)=1)
    (hcomm : ∀ z : Z, Commute (ρ z) x) : (x-1)^3=0 := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank (ZMod 2) V)
  let : CharP (Module.End (ZMod 2) V) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  apply LinearMap.nilpotent_cube_zero_of_six_even_kernels hd (x-1)
  · exact ⟨2^n,by rw [sub_pow_char_pow_of_commute 2 n (Commute.one_right x),hx,one_pow,sub_self]⟩
  · intro m
    exact even_ker_finrank_of_commuting_three_group ρ Z hZ hfixed _
      (fun z => ((hcomm z).sub_right (Commute.one_right _)).pow_right m)
end Representation
