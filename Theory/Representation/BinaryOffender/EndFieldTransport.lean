module

public import Theory.Representation.EndFieldInvariants
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.FieldTheory.Finiteness

/-!
# Binary offenders over the commuting endomorphism field

An irreducible binary action becomes absolutely irreducible over its finite
endomorphism field. This change preserves the operators, faithfulness and
irreducibility on any specified subgroup. The fixed-space codimension is
multiplied by the field degree, and the offender condition becomes the exact
cardinality inequality for the same subgroup and its actual invariant space.

These are the scalar transports needed when applying cross-characteristic
projective degree estimates to binary FF-modules. Source: Guralnick--Malle,
*Classification of 2F-modules, I*, Section 2 and Proposition 4.6. No degree
estimate or group-family exclusion is assumed or proved here.
-/

public section

open scoped MonoidAlgebra
open Representation Representation.BinaryOffender

set_option backward.isDefEq.respectTransparency false
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ] in
/-- Changing to the endomorphism field preserves faithfulness. -/
theorem endFieldRep_injective (hρ : Function.Injective ρ) :
    Function.Injective ρ.endFieldRep := by
  intro g h he
  apply hρ
  ext v
  exact congrArg (fun f : Module.End (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule =>
    ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) he

/-- Binary irreducibility on a specified subgroup survives the scalar change. -/
theorem endFieldRep_comp_isIrreducible (N : Subgroup G)
    [IsIrreducible (ρ.comp N.subtype)] :
    IsIrreducible (ρ.endFieldRep.comp N.subtype) := by
  let : Nontrivial ρ.asModule := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨?_⟩
  intro W
  let U : Subrepresentation (ρ.comp N.subtype) := {
    toSubmodule := {
      carrier := W.toSubmodule.carrier
      zero_mem' := W.toSubmodule.zero_mem'
      add_mem' := W.toSubmodule.add_mem'
      smul_mem' := fun a v hv => W.toSubmodule.smul_mem (a • 1) hv }
    apply_mem_toSubmodule := fun g v hv => W.apply_mem_toSubmodule g hv }
  obtain h | h := (inferInstance : IsIrreducible (ρ.comp N.subtype)).eq_bot_or_eq_top U
  · left
    apply SetLike.ext
    intro v
    change v ∈ U ↔ v ∈ (⊥ : Subrepresentation (ρ.comp N.subtype))
    rw [h]
  · right
    apply SetLike.ext
    intro v
    change v ∈ U ↔ v ∈ (⊤ : Subrepresentation (ρ.comp N.subtype))
    rw [h]

/-- The literal fixed quotient has its dimension multiplied by the field degree. -/
theorem fixedCodim_eq_endField_mul (A : Subgroup G) :
    fixedCodim ρ A =
      Module.finrank (ZMod 2) (Module.End (ZMod 2)[G] ρ.asModule) *
        Module.finrank (Module.End (ZMod 2)[G] ρ.asModule)
          (ρ.asModule ⧸ Representation.invariants (ρ.endFieldRep.comp A.subtype)) := by
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule :=
    Module.Finite.of_finite
  have hf := fixedCodim_add_finrank ρ A
  have hi := finrank_invariants_eq_endField_mul ρ A
  have ht : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (Module.End (ZMod 2)[G] ρ.asModule) *
        Module.finrank (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule := by
    rw [Module.finrank_mul_finrank]
    exact ρ.asModuleEquiv.finrank_eq.symm
  have hq := (Representation.invariants (ρ.endFieldRep.comp A.subtype)).finrank_quotient_add_finrank
  rw [fixedSpace, hi, ht, ← hq, Nat.mul_add] at hf
  exact Nat.add_right_cancel hf

private noncomputable def endFieldFixedEquiv (A : Subgroup G) :
    Representation.invariants (ρ.endFieldRep.comp A.subtype) ≃ fixedSpace ρ A where
  toFun v := ⟨ρ.asModuleEquiv v, fun g => congrArg ρ.asModuleEquiv (v.property g)⟩
  invFun v := ⟨ρ.asModuleEquiv.symm v,
    fun g => congrArg ρ.asModuleEquiv.symm (v.property g)⟩
  left_inv v := Subtype.ext (ρ.asModuleEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (ρ.asModuleEquiv.apply_symm_apply v)

/-- The binary offender inequality is the same cardinal inequality over the endomorphism field. -/
theorem isOffender_iff_endField_card [Finite G] (A : Subgroup G) :
    IsOffender ρ A ↔ IsElementaryTwo A ∧
      Nat.card ρ.asModule ≤ Nat.card A *
        Nat.card (Representation.invariants (ρ.endFieldRep.comp A.subtype)) := by
  have hV : Nat.card ρ.asModule = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Nat.card_congr ρ.asModuleEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hC : Nat.card (Representation.invariants (ρ.endFieldRep.comp A.subtype)) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    rw [Nat.card_congr (endFieldFixedEquiv ρ A),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  constructor
  · rintro ⟨hA, hdim⟩
    refine ⟨hA, ?_⟩
    rw [hV, hC, hA.card_eq_two_pow_rank, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) ((fixedCodim_le_rank_iff ρ A).mp hdim)
  · rintro ⟨hA, hcard⟩
    refine ⟨hA, (fixedCodim_le_rank_iff ρ A).mpr ?_⟩
    rw [hV, hC, hA.card_eq_two_pow_rank, ← pow_add] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard

/-- The endomorphism field has the characteristic of the binary base field. -/
theorem endFieldRep_charTwo : CharP (Module.End (ZMod 2)[G] ρ.asModule) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) _).injective 2

/-- The endomorphism-field action remains finite-dimensional. -/
theorem endFieldRep_finiteDimensional :
    FiniteDimensional (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule := by
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  exact Module.Finite.of_finite

/-- A lower bound for the absolute degree gives a lower bound for the original
binary module's cardinality, even when its endomorphism field is larger. -/
theorem two_pow_endField_finrank_le_card :
    2 ^ Module.finrank (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule ≤ Nat.card V := by
  let : FiniteDimensional (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule :=
    endFieldRep_finiteDimensional ρ
  calc
    2 ^ Module.finrank (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule ≤
        Nat.card (Module.End (ZMod 2)[G] ρ.asModule) ^
          Module.finrank (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule :=
      Nat.pow_le_pow_left (Nat.succ_le_of_lt Finite.one_lt_card) _
    _ = Nat.card ρ.asModule := Module.natCard_eq_pow_finrank.symm
    _ = Nat.card V := Nat.card_congr ρ.asModuleEquiv.toEquiv

/-- An FF witness uses the same elementary subgroup after the scalar change. -/
theorem isFFModule_iff_endField_card [Finite G] :
    IsFFModule ρ ↔ ∃ A : Subgroup G, IsElementaryTwo A ∧
      Nat.card ρ.asModule ≤ Nat.card A *
        Nat.card (Representation.invariants (ρ.endFieldRep.comp A.subtype)) := by
  exact exists_congr (fun A => isOffender_iff_endField_card ρ A)

end Representation.BinaryOffender
