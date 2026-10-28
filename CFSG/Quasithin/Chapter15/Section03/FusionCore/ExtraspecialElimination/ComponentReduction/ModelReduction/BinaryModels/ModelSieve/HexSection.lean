module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.Representation.HexacodeAction.Field
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The equivariant triple-cover section required by the model sieve

The witness below identifies a literal section `I / C_I(L)` of the given
representation, with `I` in `Irr⁺(L,V)`, with the concrete hexacode module.
The same group equivalence intertwines both actions. Transporting the field
structure along that linear equivalence makes the source section an actual
three-dimensional F₄-module, and its original action is F₄-linear.

This is the output language for the triple-cover classification branch, not
a classification theorem. Constructing this witness from the appendix
alternatives remains necessary; an abstract cover or a dimension equality
does not construct it.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(8),
printed p.86, B.5.1(1)(i), printed p.99, and K.1.3, printed p.453.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- An actual irreducible source section with the marked hexacode action. -/
structure HexSection (ρ : Representation (ZMod 2) D V) (L : Subgroup D) where
  space : Submodule (ZMod 2) V
  stable : L ≤ subspaceStabilizer ρ space
  full : subspaceCommutator ρ space L = space
  irreducible : Representation.IsIrreducible (centralQuotientRepresentation ρ L space stable)
  groupEquiv : L ≃* Atlas.Codes.HexEvenAutomorphisms
  moduleEquiv : centralQuotient ρ L space ≃ₗ[ZMod 2] Atlas.Codes.hexacode
  equivariant : ∀ (g : L) (v : centralQuotient ρ L space),
    moduleEquiv (centralQuotientRepresentation ρ L space stable g v) =
      Representation.Hexacode.action (groupEquiv g).val (moduleEquiv v)

namespace HexSection
variable {ρ : Representation (ZMod 2) D V} {L : Subgroup D} (s : HexSection ρ L)

/-- The section is in the source family `Irr⁺`, with its actual induced action. -/
theorem isIrrPlus : IsIrrPlus ρ L s.space := ⟨s.stable, s.full, s.irreducible⟩

/-- The actual field structure transported to the source section. -/
@[instance_reducible] noncomputable def fieldModule :
    Module Representation.Hexacode.F (centralQuotient ρ L s.space) :=
  s.moduleEquiv.toAddEquiv.module Representation.Hexacode.F

/-- Its four-element scalars extend the existing binary scalars. -/
theorem fieldTower :
    letI := s.fieldModule
    IsScalarTower (ZMod 2) Representation.Hexacode.F (centralQuotient ρ L s.space) := by
  let := s.fieldModule
  exact s.moduleEquiv.isScalarTower (A := Representation.Hexacode.F)

/-- The same module identification, now linear over the four-element field. -/
noncomputable def fieldEquiv :
    letI := s.fieldModule
    centralQuotient ρ L s.space ≃ₗ[Representation.Hexacode.F] Atlas.Codes.hexacode := by
  letI := s.fieldModule
  exact s.moduleEquiv.toAddEquiv.linearEquiv Representation.Hexacode.F

/-- The coordinates identify the source section with F₄³. -/
noncomputable def fourCoordinates :
    centralQuotient ρ L s.space ≃ₗ[ZMod 2] (Fin 3 → Representation.Hexacode.F) :=
  s.moduleEquiv.trans Representation.Hexacode.binaryCoordinates

/-- The original section action agrees with the concrete field-linear action. -/
theorem fieldAction (g : L) (v : centralQuotient ρ L s.space) :
    s.moduleEquiv (centralQuotientRepresentation ρ L s.space s.stable g v) =
      Representation.Hexacode.evenFieldAction (s.groupEquiv g) (s.moduleEquiv v) :=
  s.equivariant g v

/-- The source action itself is linear for the transported four-element scalars. -/
theorem action_smul (g : L) (r : Representation.Hexacode.F)
    (v : centralQuotient ρ L s.space) :
    letI := s.fieldModule
    centralQuotientRepresentation ρ L s.space s.stable g (r • v) =
      r • centralQuotientRepresentation ρ L s.space s.stable g v := by
  let := s.fieldModule
  apply s.moduleEquiv.injective
  rw [s.fieldAction]
  change Representation.Hexacode.evenFieldAction (s.groupEquiv g)
    (s.fieldEquiv (r • v)) = s.fieldEquiv
      (r • centralQuotientRepresentation ρ L s.space s.stable g v)
  rw [s.fieldEquiv.map_smul, s.fieldEquiv.map_smul]
  exact (Representation.Hexacode.evenFieldAction (s.groupEquiv g)).map_smul r _ |>.trans
    (congrArg (r • ·) (s.fieldAction g v).symm)

/-- The field dimension comes from the equivariant module identification. -/
theorem field_finrank :
    letI := s.fieldModule
    Module.finrank Representation.Hexacode.F (centralQuotient ρ L s.space) = 3 := by
  let := s.fieldModule
  exact s.fieldEquiv.finrank_eq.trans Representation.Hexacode.field_finrank

include s in
/-- The group in the witness is quasisimple by the proved concrete-cover theorem. -/
theorem quasisimple : Theory.GroupTheory.IsQuasisimple L := by
  let := Representation.Hexacode.even_isQuasisimple
  exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv s.groupEquiv.symm

end HexSection
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
