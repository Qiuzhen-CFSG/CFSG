module
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Faithfulness of the simple type of an isotypic representation

A semisimple isotypic module is a direct sum of copies of its simple type.
Two scalars acting equally on that type therefore act equally everywhere.
For a group representation this identifies the kernels and transfers
faithfulness to each constituent, including the restriction to a subgroup.

The actual consumer is the faithful local type in the original A₅ passage,
Aschbacher–Smith D.3.9(1), printed pp.199–200. Ambient faithfulness alone
would not suffice without the proved isotypy.
-/

@[expose] public section
open scoped MonoidAlgebra
namespace IsIsotypicOfType
variable {R M S : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup S] [Module R S]

/-- Equality on the type is equality on every copy in its semisimple sum. -/
theorem smul_eq_of_type [IsSemisimpleModule R M]
    (h : IsIsotypicOfType R M S) {r s : R} (he : ∀ v : S, r • v = s • v)
    (v : M) : r • v = s • v := by
  obtain ⟨ι,⟨e⟩⟩ := h.linearEquiv_finsupp
  apply e.injective
  rw [map_smul, map_smul]
  ext i
  exact he (e v i)
end IsIsotypicOfType

namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A constituent of a faithful semisimple isotypic action is faithful. -/
theorem faithful_subrepresentation_of_isotypic
    [IsSemisimpleModule (ZMod 2)[G] ρ.asModule]
    (hρ : Function.Injective ρ) (S : Subrepresentation ρ)
    (htype : IsIsotypicOfType (ZMod 2)[G] ρ.asModule S.asSubmodule) :
    Function.Injective S.toRepresentation := by
  intro g h he
  apply hρ
  ext v
  have hpoint (w : S.asSubmodule) :
      MonoidAlgebra.of (ZMod 2) G g • w = MonoidAlgebra.of (ZMod 2) G h • w := by
    apply Subtype.ext
    have h' := LinearMap.congr_fun he
      (show S.toSubmodule from ⟨ρ.asModuleEquiv w.val,w.property⟩)
    have heq := congrArg (fun z : S.toSubmodule => z.val) h'
    change ρ g (ρ.asModuleEquiv w.val) = ρ h (ρ.asModuleEquiv w.val) at heq
    apply ρ.asModuleEquiv.injective
    simpa only [Submodule.coe_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of] using heq
  simpa only [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of,
    LinearEquiv.apply_symm_apply] using congrArg ρ.asModuleEquiv
    (htype.smul_eq_of_type hpoint (ρ.asModuleEquiv.symm v))

/-- The literal subgroup action on an isotypic constituent retains
faithfulness of the ambient action. -/
theorem faithful_restriction_subrepresentation_of_isotypic
    (hρ : Function.Injective ρ) (N : Subgroup G)
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (S : Subrepresentation (ρ.comp N.subtype))
    (htype : IsIsotypicOfType (ZMod 2)[N]
      (Representation.asModule (ρ.comp N.subtype)) S.asSubmodule) :
    Function.Injective S.toRepresentation :=
  faithful_subrepresentation_of_isotypic (ρ.comp N.subtype)
    (hρ.comp N.subtype_injective) S htype

end Representation.BinaryOffender.Homogeneous
