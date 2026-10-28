module

public import Theory.Representation.ExtraspecialCubicDisplacement
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Small binary actors on an extraspecial cubic residual

In a faithful binary representation of an extraspecial group of order 27,
every element of order three moves at least four dimensions, and a central
one moves at least six. Maschke decomposition supplies a faithful constituent;
the exact extraspecial degree and cubic fixed-space calculation give the bounds.

The displacement of a commutator is at most twice that of its first entry.
Consequently an ambient actor moving at most two dimensions fixes the residual
center. An involution moving at most one dimension centralizes an exponent-three
residual, and is trivial when that residual contains its ambient centralizer.

These estimates supply the alternative point-normality argument in
Aschbacher–Smith 14.7.15(1), printed p.1047, using the representation calculation
of G.7.1(2), printed p.347. They retain the literal ambient representation.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace Representation.ExtraspecialBinarySix

variable {P W : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite P] [FiniteDimensional (ZMod 2) W] in
private theorem irreducible_center_fixed
    (ρ : Representation (ZMod 2) P W) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) : invariants (ρ.comp (center P).subtype) = ⊥ := by
  by_contra hn
  have hk := le_ker_of_normal_invariants_ne_bot ρ (center P) hn
  have hb : center P = ⊥ := bot_unique (by
    simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hf] using hk)
  have hc := IsExtraspecial.center_order_p 3 P
  rw [hb,card_bot] at hc
  omega

/-- Every cubic moves at least four dimensions; a central cubic moves at least six. -/
theorem faithful_cubic_displacement_lower
    (ρ : Representation (ZMod 2) P W) (hf : Function.Injective ρ)
    (hP : Nat.card P = 27) (x : P) (hx : orderOf x = 3) :
    4 ≤ fixedCodim ρ (zpowers x) ∧
      (x ∈ center P → 6 ≤ fixedCodim ρ (zpowers x)) := by
  let : IsSemisimpleModule (ZMod 2)[P] ρ.asModule := by
    apply isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
    right
    rw [ZMod.ringChar_zmod_n,hP]
    exact ⟨Nat.prime_two,by decide⟩
  have hcenter : ¬ center P ≤ ρ.ker := by
    intro hc
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hf] using hc)
    have hh := IsExtraspecial.center_order_p 3 P
    rw [hb,card_bot] at hh
    omega
  obtain ⟨m,hm,hmk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker ρ (center P) hcenter
  let τ := (Subrepresentation.ofSubmodule' m).toRepresentation
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ hm
  have hτ : Function.Injective τ := (MonoidHom.ker_eq_bot_iff _).mp
    (ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 3) τ hmk)
  have hd := BinaryCoprimeDegree.extraspecial_irreducible_finrank (by decide : 3 ≠ 2) τ hτ hP
  rw [BinaryPrimeDegree.orderOf_two_mod_three] at hd
  have hz := irreducible_center_fixed τ hτ
  have hle := fixedCodim_subrepresentation_le ρ (Subrepresentation.ofSubmodule' m) (zpowers x)
  change fixedCodim τ (zpowers x) ≤ fixedCodim ρ (zpowers x) at hle
  by_cases hxc : x ∈ center P
  · have hgen : zpowers x = center P := eq_of_le_of_card_ge (zpowers_le.mpr hxc)
      (by rw [Nat.card_zpowers,hx,IsExtraspecial.center_order_p 3 P])
    have he := fixedCodim_add_finrank τ (center P)
    change fixedCodim τ (center P) + Module.finrank (ZMod 2)
      (invariants (τ.comp (center P).subtype)) = _ at he
    rw [hz,finrank_bot] at he
    rw [hgen] at hle ⊢
    exact ⟨by omega,fun _ => by omega⟩
  · have he := BinaryCoprimeDegree.extraspecial_twentySeven_fixedCodim_zpowers τ hP hz hx hxc
    rw [hd] at he
    exact ⟨by omega,fun hc => (hxc hc).elim⟩

variable {D : Type*} [Group D] [Finite D]

/-- An actor moving at most two dimensions fixes the extraspecial center pointwise. -/
theorem small_actor_fixes_extraspecial_center
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P] (hP : Nat.card P = 27)
    (t : D) (hsmall : fixedCodim ρ (zpowers t) ≤ 2) :
    ∀ z ∈ center P, (MulAut.conjNormal t : MulAut P) z = z := by
  intro z hz
  let a : MulAut P := MulAut.conjNormal t
  let x : P := a z * z⁻¹
  have hxZ : x ∈ center P := (center P).mul_mem
    ((center P).characteristic_iff_map_eq.mp inferInstance a |>.le (mem_map_of_mem a.toMonoidHom hz))
    ((center P).inv_mem hz)
  by_contra hn
  have hxne : x ≠ 1 := by
    intro he
    exact hn (mul_inv_eq_one.mp he)
  have hx3 : orderOf x = 3 := orderOf_eq_prime (by
    have he := pow_card_eq_one' (x := (⟨x,hxZ⟩ : center P))
    rw [IsExtraspecial.center_order_p 3 P] at he
    exact congrArg Subtype.val he) hxne
  have hlo := (faithful_cubic_displacement_lower (ρ.comp P.subtype)
    (hf.comp P.subtype_injective) hP x hx3).2 hxZ
  have hhi := fixedCodim_commutator_le_twice ρ t (z : D)
  simp only [fixedCodim_zpowers_eq_displacement_rank] at hlo hhi hsmall
  change 6 ≤ Module.finrank (ZMod 2) (ρ (t*(z:D)*t⁻¹*(z:D)⁻¹) - LinearMap.id).range at hlo
  omega

/-- A faithful binary action with a self-centralizing exponent-three residual has no transvections. -/
theorem rank_one_actor_trivial
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P] (hP : Nat.card P = 27)
    (hexp : Monoid.exponent P = 3)
    (hcentral : centralizer (P : Set D) ≤ P)
    (t : D) (ht : t ^ 2 = 1) (hsmall : fixedCodim ρ (zpowers t) ≤ 1) : t = 1 := by
  have hc : t ∈ centralizer (P : Set D) := by
    intro p hp
    let x : P := ⟨t*p*t⁻¹*p⁻¹, P.mul_mem ((inferInstance : P.Normal).conj_mem p hp t) (P.inv_mem hp)⟩
    have hx : x = 1 := by
      by_contra hn
      have hx3 : orderOf x = 3 := orderOf_eq_prime
        (by simpa only [hexp] using Monoid.pow_exponent_eq_one x) hn
      have hlo := (faithful_cubic_displacement_lower (ρ.comp P.subtype)
        (hf.comp P.subtype_injective) hP x hx3).1
      have hhi := fixedCodim_commutator_le_twice ρ t p
      simp only [fixedCodim_zpowers_eq_displacement_rank] at hlo hhi hsmall
      change 4 ≤ Module.finrank (ZMod 2) (ρ (t*p*t⁻¹*p⁻¹) - LinearMap.id).range at hlo
      omega
    have he : t*p*t⁻¹*p⁻¹=1 := congrArg Subtype.val hx
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have ht3 : t ^ 3 = 1 := by
    exact congrArg Subtype.val (show (⟨t,hcentral hc⟩ : P)^3=1 by
      simpa only [hexp] using Monoid.pow_exponent_eq_one (⟨t,hcentral hc⟩ : P))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
    (orderOf_dvd_of_pow_eq_one ht) (orderOf_dvd_of_pow_eq_one ht3))
end Representation.ExtraspecialBinarySix
