module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import Theory.Representation.HexacodeAction.Field
public import Theory.Representation.BinaryOffender.Replacement
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Universal irreducible inputs for the central-cover branch

These definitions specify the specialized B.4.5 and B.4.2(8) inputs used by
13.8.21(2). They are hypotheses to be discharged by the earlier classification,
not assertions that the classification is proved. They quantify over every
intermediate overgroup of the actual component and every faithful module on
which that component is irreducible. The small-ratio conclusion retains a
faithful actor map, its component image and an actual linear intertwiner with
the hexacode. The FF conclusion retains the exact ratio one.

In particular neither input applies directly to a reducible FF-module, nor
does either supply an invariant submodule of the source U_H/V₁. Selecting the
homogeneous Irr⁺ member, proving invariance and handling reducible sections
remain separate proof obligations. We use only the quadratic-ratio ≤ 2
specialization of B.4.5; no stronger assertion about arbitrary modules with a
small cubic ratio is encoded here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(8) and
B.4.5, printed pp.86–87; F.9.18(3–6), pp.325–326; 13.8.21(2), p.956.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition
universe u v
variable {D : Type u} [Group D]
variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- The concrete representation conclusion of the irreducible cover case.
There is no assumed dimension; the coordinates imply it. -/
structure HexacodeModel (L : Subgroup D) (σ : Representation (ZMod 2) D W) where
  actor : D →* HexAutomorphisms
  faithful : Function.Injective actor
  component_image : L.map actor = hexSign.ker
  coordinates : W ≃ₗ[ZMod 2] hexacode
  intertwines : ∀ g w, coordinates (σ g w) = Hexacode.action (actor g) (coordinates w)

theorem HexacodeModel.finrank {L : Subgroup D} {σ : Representation (ZMod 2) D W}
    (m : HexacodeModel L σ) : Module.finrank (ZMod 2) W = 6 :=
  m.coordinates.finrank_eq.trans hexacode_finrank

/-- The universal irreducible statements, specialized to a fixed cubic-cover
component in D. The source assembly must supply these from B.4.2 and B.4.5.
Intermediate overgroups are retained for restriction to inertia groups. -/
structure IrreducibleInputs (L : Subgroup D) : Prop where
  small : ∀ (J : Subgroup D) (_hLJ : L ≤ J)
    (W : Type v) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) J W),
    Function.Injective σ → IsIrreducible (σ.comp (L.subgroupOf J).subtype) →
    quadraticRatio σ ≤ 2 → Nonempty (HexacodeModel (L.subgroupOf J) σ)
  ff_ratio : ∀ (J : Subgroup D) (_hLJ : L ≤ J)
    (W : Type v) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) J W),
    Function.Injective σ → IsIrreducible (σ.comp (L.subgroupOf J).subtype) →
    IsFFModule σ → quadraticRatio σ = 1

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition
