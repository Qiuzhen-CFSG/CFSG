module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.NormalType
public import Theory.Representation.CliffordRestriction
public import Theory.Representation.SubspaceQuotient

/-!
# Simple copies in semisimple isotypic quotients

A surjective image of a semisimple isotypic module retains its simple type:
a splitting embeds the image back into the original module. In a nonzero
binary isotypic module, odd-copy selection gives an actual simple submodule
fixed by a prescribed two-group. The literal quotient representation retains
both semisimplicity and the same group-algebra type.

Source: Aschbacher–Smith D.3.9(1), printed pp.199–200, and A.1.42(2).
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra
namespace IsIsotypicOfType
variable {R M V S : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup V] [Module R V] [AddCommGroup S] [Module R S]

theorem of_surjective_semisimple [IsSemisimpleModule R M]
    (h : IsIsotypicOfType R M S) (f : M →ₗ[R] V) (hf : Function.Surjective f) :
    IsIsotypicOfType R V S := by
  obtain ⟨g,hg⟩ := IsSemisimpleModule.lifting_property f hf (LinearMap.id : V →ₗ[R] V)
  apply h.of_injective g
  intro x y he
  have hx := LinearMap.congr_fun hg x
  have hy := LinearMap.congr_fun hg y
  exact hx.symm.trans ((congrArg f he).trans hy)
end IsIsotypicOfType

namespace Representation.BinaryOffender.Homogeneous
variable {G V E : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
  [AddCommGroup E] [Module (ZMod 2)[N] E]

theorem exists_invariant_simple_of_isotypic [Finite V] [Nontrivial V]
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) E)
    (P : Subgroup G) (hP : IsPGroup 2 P) :
    ∃ U : Subrepresentation (ρ.comp N.subtype), U.toRepresentation.IsIrreducible ∧
      Nonempty (U.asSubmodule ≃ₗ[(ZMod 2)[N]] E) ∧
      ∀ p : P, U.toSubmodule.map (ρ p) = U.toSubmodule := by
  let σ : Representation (ZMod 2) N V := ρ.comp N.subtype
  let : Nontrivial σ.asModule := σ.asModuleEquiv.toEquiv.nontrivial
  obtain ⟨B,hB⟩ := IsSemisimpleModule.exists_simple_submodule (ZMod 2)[N] σ.asModule
  let S := Subrepresentation.ofSubmodule' B
  have hS : S.toRepresentation.IsIrreducible := by
    rw [Subrepresentation.irreducible_iff_isAtom]
    exact Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff S |>.mp
      (isSimpleModule_iff_isAtom.mp hB)
  have hs (p : P) : SameModule S ((normalTypeAction ρ N).conjugate p S) := by
    let := simple_asSubmodule S hS
    let C := (normalTypeAction ρ N).conjugate p S
    have hc := (normalTypeAction ρ N).conjugate_irreducible S hS p
    let := simple_asSubmodule C hc
    exact (sameModule_iff_linearEquiv _ _).mpr
      ⟨(htype S.asSubmodule).some.trans (htype C.asSubmodule).some.symm⟩
  obtain ⟨U,_,hu,hfix⟩ := fixed_simple_copy ρ N P hP S hS hs
  let := simple_asSubmodule U hu
  exact ⟨U,hu,htype U.asSubmodule,hfix⟩


variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

omit [N.Normal] in
theorem quotient_restriction_isotypic
    (U : Subrepresentation ρ)
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) E) :
    IsIsotypicOfType (ZMod 2)[N]
      (Representation.asModule (U.quotientRepresentation.comp N.subtype)) E := by
  let f : Representation.IntertwiningMap (ρ.comp N.subtype)
      (U.quotientRepresentation.comp N.subtype) := {
    toLinearMap := U.toSubmodule.mkQ
    isIntertwining' _ := by ext; rfl }
  exact htype.of_surjective_semisimple
    (IntertwiningMap.equivLinearMapAsModule _ _ f) U.toSubmodule.mkQ_surjective

omit [N.Normal] in
theorem quotient_restriction_semisimple
    (U : Subrepresentation ρ)
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))] :
    IsSemisimpleModule (ZMod 2)[N]
      (Representation.asModule (U.quotientRepresentation.comp N.subtype)) := by
  let f : Representation.IntertwiningMap (ρ.comp N.subtype)
      (U.quotientRepresentation.comp N.subtype) := {
    toLinearMap := U.toSubmodule.mkQ
    isIntertwining' _ := by ext; rfl }
  exact IsSemisimpleModule.of_surjective
    (IntertwiningMap.equivLinearMapAsModule _ _ f) U.toSubmodule.mkQ_surjective

end Representation.BinaryOffender.Homogeneous
