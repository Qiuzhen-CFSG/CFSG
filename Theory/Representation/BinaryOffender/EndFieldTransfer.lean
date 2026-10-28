module

public import Theory.Representation.EndFieldInvariants
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Offenders over the actual endomorphism field

An irreducible representation over a finite field becomes absolutely
irreducible over its Schur endomorphism field. This change retains the
operators, faithfulness, irreducibility on a specified subgroup, and the
cardinality of its fixed space. In particular the binary offender inequality
becomes exactly `|V| ≤ |A| |C_V(A)|`, with the same subgroup A.

Rank-nullity and the scalar tower also give the fixed-codimension formula.
No containment of A in a component is needed. Absolute irreducibility of
the whole group does not assert absolute irreducibility on that component.

Source: the scalar-field reduction preceding Guralnick–Malle,
*Classification of 2F-modules, II*, §§8–9; the F-module inequality is the
one in Theorem B, not the squared-offender inequality for 2F-modules.
-/

public section

open scoped MonoidAlgebra

namespace Representation.BinaryOffender.EndFieldTransfer

section General

variable {F G V : Type*} [Field F] [Finite F] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (ρ : Representation F G V) [IsIrreducible ρ]

omit [Finite F] [FiniteDimensional F V] [IsIrreducible ρ] in
/-- Faithfulness is preserved by the existing endomorphism-field action. -/
theorem faithful (hf : Function.Injective ρ) : Function.Injective ρ.endFieldRep := by
  intro x y hxy
  apply hf
  ext v
  have h := congrArg (fun f => ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) hxy
  simpa only [endFieldRep_apply, LinearEquiv.apply_symm_apply] using h

/-- The Schur representation has finite dimension over its actual scalar field. -/
theorem finiteDimensional :
    FiniteDimensional (Module.End F[G] ρ.asModule) ρ.asModule := by
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite F ρ.asModule)
  exact Module.Finite.of_finite

set_option backward.isDefEq.respectTransparency false in
/-- Irreducibility on any specified subgroup survives enlargement of scalars
inside the commuting endomorphisms of the whole action. -/
theorem restrict_irreducible (N : Subgroup G) [IsIrreducible (ρ.comp N.subtype)] :
    IsIrreducible (ρ.endFieldRep.comp N.subtype) := by
  let τ := ρ.comp N.subtype
  let : Nontrivial ρ.asModule := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation τ := {
    toSubmodule := {
      carrier := S.toSubmodule.carrier
      add_mem' := S.toSubmodule.add_mem'
      zero_mem' := S.toSubmodule.zero_mem'
      smul_mem' := fun f m hm => S.toSubmodule.smul_mem' (f • 1) hm }
    apply_mem_toSubmodule := fun g m hm => S.apply_mem_toSubmodule g hm }
  obtain h | h := (inferInstance : IsIrreducible τ).eq_bot_or_eq_top T <;>
    simp only [SetLike.ext'_iff, show (S : Set ρ.asModule) = (T : Set V) by rfl, h] <;>
    tauto

/-- The two fixed spaces have the same underlying vectors under asModuleEquiv. -/
theorem card_invariants (A : Subgroup G) :
    Nat.card (invariants (ρ.endFieldRep.comp A.subtype)) =
      Nat.card (invariants (ρ.comp A.subtype)) := by
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨ρ.asModuleEquiv v, fun a => congrArg ρ.asModuleEquiv (v.property a)⟩
    invFun := fun v => ⟨ρ.asModuleEquiv.symm v,
      fun a => congrArg ρ.asModuleEquiv.symm (v.property a)⟩
    left_inv := fun v => Subtype.ext (ρ.asModuleEquiv.symm_apply_apply v)
    right_inv := fun v => Subtype.ext (ρ.asModuleEquiv.apply_symm_apply v) }

end General

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The source's cardinal inequality is exactly the binary dimension inequality. -/
theorem offender_iff_card [Finite G] (A : Subgroup G) (hA : IsElementaryTwo A) :
    IsOffender ρ A ↔ Nat.card V ≤ Nat.card A * Nat.card (fixedSpace ρ A) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
    Nat.card_zmod, hA.card_eq_two_pow_rank, ← pow_add,
    Nat.pow_le_pow_iff_right (by decide : 1 < 2)]
  rw [IsOffender, and_iff_right hA, fixedCodim_le_rank_iff]
  rfl

variable [IsIrreducible ρ]

/-- The endomorphism field has characteristic two. -/
theorem charTwo : CharP (Module.End (ZMod 2)[G] ρ.asModule) 2 :=
  (Algebra.charP_iff (ZMod 2) _ 2).mp inferInstance

/-- Fixed codimension scales by the degree of the actual Schur field. -/
theorem fixedCodim_eq (A : Subgroup G) :
    fixedCodim ρ A = Module.finrank (ZMod 2) (Module.End (ZMod 2)[G] ρ.asModule) *
      Module.finrank (Module.End (ZMod 2)[G] ρ.asModule)
        (ρ.asModule ⧸ invariants (ρ.endFieldRep.comp A.subtype)) := by
  let E := Module.End (ZMod 2)[G] ρ.asModule
  let : FiniteDimensional E ρ.asModule := finiteDimensional ρ
  have htotal : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) E * Module.finrank E ρ.asModule := by
    rw [Module.finrank_mul_finrank]
    exact ρ.asModuleEquiv.finrank_eq.symm
  have hfixed := finrank_invariants_eq_endField_mul ρ A
  have hbinary := fixedCodim_add_finrank ρ A
  have hfield := (invariants (ρ.endFieldRep.comp A.subtype)).finrank_quotient_add_finrank
  change fixedCodim ρ A + Module.finrank (ZMod 2) (invariants (ρ.comp A.subtype)) =
    Module.finrank (ZMod 2) V at hbinary
  rw [htotal, hfixed] at hbinary
  change fixedCodim ρ A = Module.finrank (ZMod 2) E * _
  nlinarith

/-- The original subgroup is an offender exactly when it satisfies the
F-module cardinal inequality on the absolutely irreducible Schur action. -/
theorem offender_iff_endField_card [Finite G] (A : Subgroup G)
    (hA : IsElementaryTwo A) :
    IsOffender ρ A ↔ Nat.card ρ.asModule ≤
      Nat.card A * Nat.card (invariants (ρ.endFieldRep.comp A.subtype)) := by
  rw [card_invariants, Nat.card_congr ρ.asModuleEquiv.toEquiv]
  exact offender_iff_card ρ A hA

/-- Every binary FF-module supplies an actual source F-offender after the
scalar change; neither the actor nor its embedding changes. -/
theorem exists_endField_offender [Finite G] (hff : IsFFModule ρ) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ Nat.card ρ.asModule ≤
      Nat.card A * Nat.card (invariants (ρ.endFieldRep.comp A.subtype)) := by
  obtain ⟨A, hA⟩ := hff
  exact ⟨A, hA.1, (offender_iff_endField_card ρ A hA.1).mp hA⟩

end Representation.BinaryOffender.EndFieldTransfer
