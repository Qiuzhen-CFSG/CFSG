module
public import Theory.SpecificGroups.Alternating.FourPairOuter
public import Mathlib.GroupTheory.PGroup
public import Stellmacher.OmegaOneCenterMap
/-!
# Centralizers of the Sylow omega-center above cubic normal blocks

For a normal A₄ or A₄² subgroup N, the automorphism-invariant set of
involutions whose intrinsic centralizers have exponent two has size three
or nine. A Sylow two-group fixes one such involution. Its centralizer in N
is then contained in that Sylow subgroup.

If N, its centralizer and the Sylow generate the ambient group, an element
centralizing the Sylow omega-center consequently lies in the product of
the last two factors. This is precisely the centralizer inclusion needed
for the outside-block product in Aschbacher--Smith 14.1.13, printed p.979.
-/

@[expose] public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.CubicOrbit
variable (N : Type*) [Group N]
def TwoCentralInvolution (z : N) : Prop :=
  z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ x : N, x * z = z * x → x ^ 2 = 1

instance [Fintype N] [DecidableEq N] (z : N) : Decidable (TwoCentralInvolution N z) := by
  unfold TwoCentralInvolution
  infer_instance

variable {N}

private theorem twoCentralInvolution_equiv {K : Type*} [Group K] (e : N ≃* K) (z : N) :
    TwoCentralInvolution K (e z) ↔ TwoCentralInvolution N z := by
  constructor
  · rintro ⟨hne,hpow,hcentral⟩
    refine ⟨fun he => hne (he ▸ e.map_one),?_,?_⟩
    · apply e.injective
      simpa only [map_pow,map_one] using hpow
    · intro x hx
      apply e.injective
      have hh := hcentral (e x) (by simpa only [←map_mul] using congrArg e hx)
      simpa only [map_pow,map_one] using hh
  · rintro ⟨hne,hpow,hcentral⟩
    refine ⟨fun he => hne (e.map_eq_one_iff.mp he),?_,?_⟩
    · simpa only [map_pow,map_one] using congrArg e hpow
    · intro x hx
      have hh := hcentral (e.symm x) (by
        apply e.injective
        simpa only [map_mul,e.apply_symm_apply] using hx)
      simpa only [map_pow,e.apply_symm_apply,map_one] using congrArg e hh

private def twoCentralInvolutionEquiv {K : Type*} [Group K] (e : N ≃* K) :
    {z : N // TwoCentralInvolution N z} ≃ {z : K // TwoCentralInvolution K z} where
  toFun z := ⟨e z, (twoCentralInvolution_equiv e z).mpr z.property⟩
  invFun z := ⟨e.symm z, (twoCentralInvolution_equiv e.symm z).mpr z.property⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z)
  right_inv z := Subtype.ext (e.apply_symm_apply z)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
private theorem single_count : Nat.card {z : AlternatingFourPair.A //
    TwoCentralInvolution AlternatingFourPair.A z} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
private theorem pair_count : Nat.card {z : AlternatingFourPair.Model //
    TwoCentralInvolution AlternatingFourPair.Model z} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem exists_fixed_involution {A : Type*} [Group A]
    (hA : IsPGroup 2 A) (ρ : A →* MulAut N)
    (hm : Nonempty (N ≃* AlternatingFourPair.A) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) :
    ∃ z : N, TwoCentralInvolution N z ∧ ∀ a : A, ρ a z = z := by
  let U := {z : N // TwoCentralInvolution N z}
  have hcard : ¬ 2 ∣ Nat.card U := by
    rcases hm with he | he
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr (twoCentralInvolutionEquiv e),single_count]
      decide
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr (twoCentralInvolutionEquiv e),pair_count]
      decide
  let : MulAction A U :=
    { smul := fun a z => ⟨ρ a z, (twoCentralInvolution_equiv (ρ a) z).mpr z.property⟩
      one_smul := fun z => Subtype.ext (by change ρ 1 z.val = z.val; rw [map_one]; rfl)
      mul_smul := fun a b z => Subtype.ext (by
        change ρ (a*b) z.val = ρ a (ρ b z.val)
        rw [map_mul]; rfl) }
  obtain ⟨z,hz⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card U hcard
  exact ⟨z,z.property,fun a => congrArg Subtype.val (hz a)⟩

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_omega_le_of_normal_cubic
    (N : Subgroup G) [N.Normal] (S : Sylow 2 G)
    (hm : Nonempty (N ≃* AlternatingFourPair.A) ∨
      Nonempty (N ≃* AlternatingFourPair.Model))
    (hgen : (N ⊔ centralizer (N : Set G)) ⊔ (S : Subgroup G) = ⊤) :
    centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) ≤
      centralizer (N : Set G) ⊔ (S : Subgroup G) := by
  let ρ : S →* MulAut N := MulAut.conjNormal.comp (S : Subgroup G).subtype
  obtain ⟨z,hz,hfix⟩ := exists_fixed_involution S.isPGroup' ρ hm
  let C := centralizer ({(z : G)} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg N.subtype (hfix ⟨s,hs⟩)
    change s * (z : G) * s⁻¹ = z at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  have hp : IsPGroup 2 (N.subgroupOf C) := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro x
    refine ⟨1,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg N.subtype (hz.2.2 ⟨x,x.property⟩ (Subtype.ext
      (mem_centralizer_singleton_iff.mp x.val.property)))
  have hCS : N ⊓ C ≤ (S : Subgroup G) := by
    intro x hx
    exact hp.le_sylow_of_normal (S.subtype hSC)
      (show (⟨x,hx.2⟩ : C) ∈ N.subgroupOf C from hx.1)
  have hzS : (z : G) ∈ S := hCS ⟨z.property,mem_centralizer_singleton_iff.mpr rfl⟩
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (S : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hzS,congrArg N.subtype hz.2.1,fun s hs =>
      mem_centralizer_singleton_iff.mp (hSC hs)⟩
  intro g hg
  have hggen : g ∈ (N ⊔ centralizer (N : Set G)) ⊔ (S : Subgroup G) := by
    rw [hgen]
    trivial
  obtain ⟨nk,hnk,s,hs,rfl⟩ := mem_sup_of_normal_left.mp hggen
  obtain ⟨n,hnN,k,hk,rfl⟩ := mem_sup_of_normal_left.mp hnk
  have hsz : s ∈ C := hSC hs
  have hkz : k ∈ C := mem_centralizer_singleton_iff.mpr (hk z z.property).symm
  have hnz : n ∈ C := by
    have hprod : n * k * s ∈ C := mem_centralizer_singleton_iff.mpr (hg z hzZ).symm
    have hh := C.mul_mem (C.mul_mem hprod (C.inv_mem hsz)) (C.inv_mem hkz)
    simpa only [mul_inv_cancel_right] using hh
  exact (centralizer (N : Set G) ⊔ (S : Subgroup G)).mul_mem
    ((centralizer (N : Set G) ⊔ (S : Subgroup G)).mul_mem
      ((le_sup_right : (S : Subgroup G) ≤ centralizer (N : Set G) ⊔ (S : Subgroup G))
        (hCS ⟨hnN,hnz⟩))
      ((le_sup_left : centralizer (N : Set G) ≤ centralizer (N : Set G) ⊔ (S : Subgroup G)) hk))
    ((le_sup_right : (S : Subgroup G) ≤ centralizer (N : Set G) ⊔ (S : Subgroup G)) hs)

end Theory.GroupTheory.CubicOrbit
