module

public import Theory.Representation.EndFieldInvariants
public import Theory.Representation.BinaryOffender.Basic

/-!
# Binary offenders over the actual endomorphism field

An irreducible binary action becomes absolutely irreducible over its commuting
endomorphism field. Its faithfulness and irreducibility on a specified subgroup
are preserved. The fixed-space codimension for the same subgroup is multiplied
by the degree of that field over the binary field. Consequently the original
offender inequality can be tested over this field, without assuming absolute
irreducibility over the binary field or replacing the acting subgroup.

The dimension calculation combines `EndFieldInvariants` with rank-nullity.
This is the scalar step needed to apply the absolutely irreducible hypotheses
in Guralnick–Malle, *Classification of 2F-modules*, II, Theorem 8.1, to binary
FF-modules. No model-specific representation bound is asserted here.
-/

@[expose] public section

open scoped MonoidAlgebra

namespace Representation.BinaryOffender.EndField

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]

omit [FiniteDimensional (ZMod 2) V] [ρ.IsIrreducible] in
/-- The same operators remain faithful over the endomorphism ring. -/
theorem injective (hρ : Function.Injective ρ) : Function.Injective ρ.endFieldRep := by
  intro g h heq
  apply hρ
  ext v
  have hh := congrArg (fun f : Module.End (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule =>
    ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) heq
  simpa only [endFieldRep_apply, LinearEquiv.apply_symm_apply] using hh

set_option backward.isDefEq.respectTransparency false in
/-- Restriction remains irreducible over the ambient action's endomorphism
field. This does not assert absolute irreducibility of the restriction. -/
theorem restriction_irreducible (N : Subgroup G)
    [iIr : IsIrreducible (ρ.comp N.subtype)] :
    IsIrreducible (ρ.endFieldRep.comp N.subtype) := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · let : Nontrivial ρ.asModule := Subrepresentation.irreducible_module_nontrivial ρ
    infer_instance
  · intro r
    let r' : Subrepresentation (ρ.comp N.subtype) := {
      toSubmodule := {
        carrier := r.toSubmodule.carrier
        add_mem' := r.toSubmodule.add_mem'
        zero_mem' := r.toSubmodule.zero_mem'
        smul_mem' f m h := r.toSubmodule.smul_mem' (f • 1) h }
      apply_mem_toSubmodule g m h := r.apply_mem_toSubmodule g h }
    obtain h | h := iIr.eq_bot_or_eq_top r' <;>
      simp only [SetLike.ext'_iff, show (r : Set ρ.asModule) = (r' : Set V) by rfl, h] <;>
      tauto

/-- The exact binary codimension, with the original subgroup and quotient. -/
theorem fixedCodim_eq (A : Subgroup G) : fixedCodim ρ A =
    Module.finrank (ZMod 2) (Module.End (ZMod 2)[G] ρ.asModule) *
      Module.finrank (Module.End (ZMod 2)[G] ρ.asModule)
        (ρ.asModule ⧸ invariants (ρ.endFieldRep.comp A.subtype)) := by
  let E := Module.End (ZMod 2)[G] ρ.asModule
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  have hd : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) E *
      Module.finrank E ρ.asModule := by
    rw [Module.finrank_mul_finrank]
    exact ρ.asModuleEquiv.finrank_eq.symm
  have hi := finrank_invariants_eq_endField_mul ρ A
  have hc := fixedCodim_add_finrank ρ A
  have hq := (invariants (ρ.endFieldRep.comp A.subtype)).finrank_quotient_add_finrank
  refine Nat.add_right_cancel (hc.trans (hd.trans ?_))
  rw [← hq, mul_add]
  congr 1
  exact hi.symm

/-- The offender test over the Schur field retains precisely the binary
inequality; in particular it uses the first power of the offender order. -/
theorem offender_iff (A : Subgroup G) : IsOffender ρ A ↔
    IsElementaryTwo A ∧
      Module.finrank (ZMod 2) (Module.End (ZMod 2)[G] ρ.asModule) *
        Module.finrank (Module.End (ZMod 2)[G] ρ.asModule)
          (ρ.asModule ⧸ invariants (ρ.endFieldRep.comp A.subtype)) ≤ rank A := by
  rw [IsOffender, fixedCodim_eq ρ A]

/-- Bounds for absolutely irreducible modules over the actual Schur field
exclude offenders on the original binary module. -/
theorem not_ff_of_fixedSpace_gap
    (hgap : ∀ A : Subgroup G, IsElementaryTwo A →
      rank A < Module.finrank (ZMod 2) (Module.End (ZMod 2)[G] ρ.asModule) *
        Module.finrank (Module.End (ZMod 2)[G] ρ.asModule)
          (ρ.asModule ⧸ invariants (ρ.endFieldRep.comp A.subtype))) :
    ¬ IsFFModule ρ := by
  rintro ⟨A, hA⟩
  exact (Nat.not_lt_of_ge ((offender_iff ρ A).mp hA).2) (hgap A hA.1)

end Representation.BinaryOffender.EndField
