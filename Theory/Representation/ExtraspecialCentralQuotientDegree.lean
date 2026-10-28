module
public import Theory.GroupAction.OddInversePairDisplacement
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
public import Theory.Representation.NormalInvariants

/-!
# Small binary actions through an extraspecial central quotient

If an actor inverts an odd subgroup modulo the kernel of a binary
representation with zero fixed space, odd norm pairing puts its fixed
vectors inside its displacement space. Thus the dimension is at most
twice its displacement rank, without assuming a faithful action.

For an irreducible representation detecting an extraspecial subgroup of
order 27 but killing its center, a nontrivial center-fixing involution
inverts the action image. Displacement at most two forces dimension two
or four; odd three-group fixed-point counting supplies evenness.
This keeps the nonfaithful case separate from the faithful six-space.

Source application: the point-central branch in Aschbacher–Smith
14.7.20(2), printed p.1049, and the inversion calculation of D.2.11,
printed p.183. The original-group exclusion is a separate obligation.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Representation

/-- Inversion in the action image bounds the whole fixed-free odd support
by twice the displacement rank, even if the original action has a kernel. -/
theorem finrank_le_twice_displacement_of_inversion_mod_kernel
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (P : Subgroup D)
    (hodd : Odd (Nat.card P)) (t : D)
    (hinv : ∀ x ∈ P, σ (t*x*t⁻¹) = σ x⁻¹)
    (hfix : invariants (σ.comp P.subtype) = ⊥) :
    Module.finrank (ZMod 2) W ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) := by
  let q := QuotientGroup.mk' σ.ker
  let τ := quotientOfLEKer σ σ.ker le_rfl
  let R := P.map q
  let := BinaryGroupAction.action τ
  let := BinaryGroupAction.elementary (V := W)
  have hR : Odd (Nat.card R) := hodd.of_dvd_nat (card_map_dvd P q)
  have hi : ∀ x : R, q t * (x : D ⧸ σ.ker) * (q t)⁻¹ = (x : D ⧸ σ.ker)⁻¹ := by
    rintro ⟨_,x,hx,rfl⟩
    rw [←map_inv,←map_mul,←map_mul,←map_inv]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change σ ((t*x*t⁻¹) / x⁻¹) = 1
    rw [div_eq_mul_inv,inv_inv,map_mul,hinv x hx,←map_mul,inv_mul_cancel,map_one]
  have hf : FixedPoints.subgroup R (Multiplicative W) = ⊥ := by
    apply bot_unique
    intro w hw
    have hh : w.toAdd ∈ invariants (σ.comp P.subtype) := by
      intro x
      exact congrArg Multiplicative.toAdd (hw ⟨q x,mem_map_of_mem q x.property⟩)
    apply mem_bot.mpr
    apply Multiplicative.toAdd.injective
    change w.toAdd = 0
    simpa only [hfix,Submodule.mem_bot] using hh
  have hle : LinearMap.ker (σ t - 1) ≤ LinearMap.range (σ t - 1) := by
    intro w hw
    have ht : q t • (Multiplicative.ofAdd w) = Multiplicative.ofAdd w :=
      congrArg Multiplicative.ofAdd (sub_eq_zero.mp hw)
    obtain ⟨v,hv⟩ := OddInversePairDisplacement.fixed_mem_range R hR (q t) hi hf
      (Multiplicative.ofAdd w) ht
    refine ⟨v.toAdd,?_⟩
    have hh := congrArg Multiplicative.toAdd hv
    change -v.toAdd + σ t v.toAdd = w at hh
    change σ t v.toAdd - v.toAdd = w
    simpa only [sub_eq_neg_add] using hh
  have hdim := (σ t - 1).finrank_range_add_finrank_ker
  have hbound := Submodule.finrank_mono hle
  omega

/-- An irreducible binary action killing the extraspecial center, but not
the whole extraspecial group, has degree two or four under a small involution. -/
theorem extraspecial_center_kernel_small_involution_degree
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) [σ.IsIrreducible]
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hZ : (center P).map P.subtype ≤ σ.ker)
    (hmove : ¬ P ≤ σ.ker) (t : D) (ht : t^2=1)
    (hne : (MulAut.conjNormal t : MulAut P) ≠ 1)
    (hcenter : ∀ z ∈ center P, (MulAut.conjNormal t : MulAut P) z = z)
    (hsmall : Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) ≤ 2) :
    Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 4 := by
  let a : MulAut P := MulAut.conjNormal t
  have ha : Function.Involutive a := by
    intro x
    have he : a^2=1 := by
      change (MulAut.conjNormal t : MulAut P)^2=1
      rw [←map_pow,ht,map_one]
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  have hi := (IsExtraspecial.exponent_and_frattini_inversion_of_card27
    hP a ha hne hcenter).2
  have hφ : frattini P ≤ (σ.comp P.subtype).ker := by
    rw [IsExtraspecial.frattini_eq_center_three]
    intro z hz
    exact hZ (mem_map_of_mem P.subtype hz)
  let τ := quotientOfLEKer (σ.comp P.subtype) (frattini P) hφ
  have hinv : ∀ x ∈ P, σ (t*x*t⁻¹) = σ x⁻¹ := by
    intro x hx
    have hh := congrArg τ (hi ⟨x,hx⟩)
    exact hh
  have hfix : invariants (σ.comp P.subtype) = ⊥ := by
    by_contra hn
    exact hmove (le_ker_of_normal_invariants_ne_bot σ P hn)
  have hd := finrank_le_twice_displacement_of_inversion_mod_kernel σ P
    (by rw [hP]; decide) t hinv hfix
  have heven := BinaryOffender.orderOf_two_dvd_finrank_of_isPGroup
    (σ.comp P.subtype) (by decide : Nat.Prime 3) (by decide)
    (IsExtraspecial.isPGroup 3 P) hfix
  norm_num [BinaryPrimeDegree.orderOf_two_mod_three] at heven
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  have hpos := Module.finrank_pos (R := ZMod 2) (M := W)
  omega

/-- Killing the extraspecial center gives the literal elementary abelian
action quotient, with order dividing nine. No action image is replaced by a tag. -/
theorem extraspecial_center_kernel_quotient
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (P : Subgroup D) [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hZ : (center P).map P.subtype ≤ σ.ker) :
    IsElementaryAbelian 3 (P ⧸ (σ.comp P.subtype).ker) ∧
      Nat.card (P ⧸ (σ.comp P.subtype).ker) ∣ 9 := by
  let N := (σ.comp P.subtype).ker
  have hZN : center P ≤ N := fun z hz => hZ (mem_map_of_mem P.subtype hz)
  let f : (P ⧸ center P) →* (P ⧸ N) :=
    QuotientGroup.map (center P) N (MonoidHom.id P) hZN
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨QuotientGroup.mk' (center P) x,rfl⟩
  let : IsElementaryAbelian 3 (P ⧸ center P) := IsExtraspecial.quotient_elementary_abelian 3 P
  have hel : IsElementaryAbelian 3 (P ⧸ N) := {
    toIsMulCommutative := ⟨⟨fun x y => by
      obtain ⟨a,rfl⟩ := hf x
      obtain ⟨b,rfl⟩ := hf y
      rw [←map_mul,←map_mul,mul_comm]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      obtain ⟨a,rfl⟩ := hf x
      rw [←map_pow,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 (P ⧸ center P)),map_one] }
  have hc : Nat.card (P ⧸ center P) = 9 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (center P)
    rw [hP,IsExtraspecial.center_order_p 3 P] at hh
    omega
  exact ⟨hel,hc ▸ card_dvd_of_surjective f hf⟩

end Representation
