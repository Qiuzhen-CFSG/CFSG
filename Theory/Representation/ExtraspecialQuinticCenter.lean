module
public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation

/-!
# The central quintic action on an extraspecial binary module

A faithful irreducible binary representation of an extraspecial group of
order 125 has dimension 20. Its center has no fixed vectors, since normal
invariants in an irreducible module are either zero or the whole module.
For any binary representation with nontrivial central action, Maschke
decomposition supplies such a constituent. Hence central fixed codimension
is at least 20, and the actual fixed-subgroup index is at least 2^20.

This is the central-element argument used at the end of Aschbacher--Smith
4.3.2, printed p.618, using G.7.1(2), p.347. It is separate from the
noncentral-element calculation in `ExtraspecialQuinticDisplacement`.
-/

public section
open Subgroup Representation
open scoped MonoidAlgebra
namespace Representation.ExtraspecialQuinticCenter
variable {P V : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The center moves all twenty binary dimensions of a faithful chief action. -/
theorem irreducible_center_fixedCodim
    (ρ : Representation (ZMod 2) P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hP : Nat.card P = 5 ^ 3) :
    BinaryOffender.fixedCodim ρ (center P) = 20 := by
  have hz : invariants (ρ.comp (center P).subtype) = ⊥ := by
    by_contra hn
    have hk := le_ker_of_normal_invariants_ne_bot ρ (center P) hn
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hf] using hk)
    have hc := IsExtraspecial.center_order_p 5 P
    rw [hb, card_bot] at hc
    omega
  have hd := BinaryCoprimeDegree.extraspecial_irreducible_finrank (by decide : 5 ≠ 2) ρ hf hP
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hd
  have he := BinaryOffender.fixedCodim_add_finrank ρ (center P)
  change BinaryOffender.fixedCodim ρ (center P) +
    Module.finrank (ZMod 2) (invariants (ρ.comp (center P).subtype)) = _ at he
  rw [hz, finrank_bot] at he
  omega

/-- One faithful constituent already consumes twenty central moving dimensions. -/
theorem twenty_le_center_fixedCodim
    (ρ : Representation (ZMod 2) P V) (hP : Nat.card P = 5 ^ 3)
    (hcenter : ¬ center P ≤ ρ.ker) :
    20 ≤ BinaryOffender.fixedCodim ρ (center P) := by
  let : IsSemisimpleModule (ZMod 2)[P] ρ.asModule := by
    apply isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
    right
    rw [ZMod.ringChar_zmod_n, hP]
    exact ⟨Nat.prime_two, by decide⟩
  obtain ⟨m, hm, hmk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker ρ (center P) hcenter
  let τ := (Subrepresentation.ofSubmodule' m).toRepresentation
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ hm
  have hf : Function.Injective τ := (MonoidHom.ker_eq_bot_iff _).mp
    (ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 5) τ hmk)
  have hd := irreducible_center_fixedCodim τ hf hP
  exact hd ▸ BinaryOffender.fixedCodim_subrepresentation_le ρ
    (Subrepresentation.ofSubmodule' m) (center P)

/-- The dimension bound expressed on the actual multiplicative additive group. -/
theorem center_fixedIndex_lower_bound
    (ρ : Representation (ZMod 2) P V) (hP : Nat.card P = 5 ^ 3)
    (hcenter : ¬ center P ≤ ρ.ker) :
    2 ^ 20 ≤ BinaryFixedPoints.fixedIndex (ρ.comp (center P).subtype) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hi := BinaryFixedPoints.fixedIndex_mul_card (ρ.comp (center P).subtype)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hi
  have he := BinaryOffender.fixedCodim_add_finrank ρ (center P)
  change BinaryOffender.fixedCodim ρ (center P) +
    Module.finrank (ZMod 2) (invariants (ρ.comp (center P).subtype)) = _ at he
  rw [← he, pow_add] at hi
  have hi' := Nat.eq_of_mul_eq_mul_right (by positivity :
    0 < 2 ^ Module.finrank (ZMod 2) (invariants (ρ.comp (center P).subtype))) hi
  rw [hi']
  exact Nat.pow_le_pow_right (by decide) (twenty_le_center_fixedCodim ρ hP hcenter)
end Representation.ExtraspecialQuinticCenter
