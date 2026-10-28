module
public import Theory.Representation.ExtraspecialQuinticDisplacement
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Displacement of actors moving an extraspecial five-group

A faithful binary constituent of an extraspecial group of order 125 has
dimension twenty. A noncentral quintic fixes four dimensions, and a central
one fixes none. The commutator rank inequality therefore forces an actor
moving an exponent-five such subgroup to move at least eight dimensions.
The embedding and its conjugation action are retained explicitly.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832, using G.7.1(2).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace Representation.ExtraspecialQuinticActor
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {P W : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite P] [FiniteDimensional (ZMod 2) W] in
private theorem irreducible_center_fixed
    (ρ : Representation (ZMod 2) P W) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) : invariants (ρ.comp (center P).subtype) = ⊥ := by
  by_contra hn
  have hk := le_ker_of_normal_invariants_ne_bot ρ (center P) hn
  have hb : center P = ⊥ := bot_unique (by
    simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hf] using hk)
  have hc := IsExtraspecial.center_order_p 5 P
  rw [hb,card_bot] at hc
  omega

/-- Every nonidentity quintic moves at least sixteen dimensions; a central one moves at least twenty. -/
theorem faithful_quintic_displacement_lower
    (ρ : Representation (ZMod 2) P W) (hf : Function.Injective ρ)
    (hP : Nat.card P = 125) (x : P) (hx : orderOf x = 5) :
    16 ≤ fixedCodim ρ (zpowers x) ∧
      (x ∈ center P → 20 ≤ fixedCodim ρ (zpowers x)) := by
  let : IsSemisimpleModule (ZMod 2)[P] ρ.asModule := by
    apply isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
    right
    rw [ZMod.ringChar_zmod_n,hP]
    exact ⟨Nat.prime_two,by decide⟩
  have hcenter : ¬ center P ≤ ρ.ker := by
    intro hc
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hf] using hc)
    have hh := IsExtraspecial.center_order_p 5 P
    rw [hb,card_bot] at hh
    omega
  obtain ⟨m,hm,hmk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker ρ (center P) hcenter
  let τ := (Subrepresentation.ofSubmodule' m).toRepresentation
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ hm
  have hτ : Function.Injective τ := (MonoidHom.ker_eq_bot_iff _).mp
    (ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 5) τ hmk)
  have hd := BinaryCoprimeDegree.extraspecial_irreducible_finrank (by decide : 5 ≠ 2) τ hτ hP
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hd
  have hz := irreducible_center_fixed τ hτ
  have hle := fixedCodim_subrepresentation_le ρ (Subrepresentation.ofSubmodule' m) (zpowers x)
  change fixedCodim τ (zpowers x) ≤ fixedCodim ρ (zpowers x) at hle
  by_cases hxc : x ∈ center P
  · have hgen : zpowers x = center P := eq_of_le_of_card_ge (zpowers_le.mpr hxc)
      (by rw [Nat.card_zpowers,hx,IsExtraspecial.center_order_p 5 P])
    have he := fixedCodim_add_finrank τ (center P)
    change fixedCodim τ (center P) + Module.finrank (ZMod 2)
      (invariants (τ.comp (center P).subtype)) = _ at he
    rw [hz,finrank_bot] at he
    rw [hgen] at hle ⊢
    exact ⟨by omega,fun _ => by omega⟩
  · have he := BinaryCoprimeDegree.extraspecial_quintic_fixed_finrank τ hz hx hxc
    have hr := fixedCodim_add_finrank τ (zpowers x)
    rw [hd] at he hr
    exact ⟨by omega,fun hc => (hxc hc).elim⟩


/-- A nontrivial conjugating actor on an exponent-five extraspecial subgroup
moves at least eight dimensions in the unchanged faithful representation. -/
theorem eight_le_displacement_of_movement
    {D : Type*} [Group D]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (j : P →* D) (hj : Function.Injective j) (hP : Nat.card P = 125)
    (hexp : ∀ x : P, x ^ 5 = 1)
    (t : D) (a : MulAut P) (ha : a ≠ 1)
    (heq : ∀ x : P, j (a x) = t * j x * t⁻¹) :
    8 ≤ Module.finrank (ZMod 2) (ρ t - LinearMap.id).range := by
  have hm : ∃ x : P, a x ≠ x := by
    by_contra! hn
    exact ha (MulEquiv.ext hn)
  obtain ⟨x,hx⟩ := hm
  have hne : a x * x⁻¹ ≠ 1 := fun he => hx (mul_inv_eq_one.mp he)
  have ho : orderOf (a x * x⁻¹) = 5 := orderOf_eq_prime (hexp _) hne
  have hl := (faithful_quintic_displacement_lower (ρ.comp j) (hf.comp hj) hP _ ho).1
  have hu := fixedCodim_commutator_le_twice ρ t (j x)
  rw [fixedCodim_zpowers_eq_displacement_rank] at hl
  change 16 ≤ Module.finrank (ZMod 2) (ρ (j (a x * x⁻¹)) - LinearMap.id).range at hl
  rw [map_mul,map_inv,heq] at hl
  rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank] at hu
  omega
end Representation.ExtraspecialQuinticActor
