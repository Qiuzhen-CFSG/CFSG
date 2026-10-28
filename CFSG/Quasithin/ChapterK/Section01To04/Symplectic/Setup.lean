module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterK.Section01To04.Preliminaries
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Source hypotheses for K.3.4

These are the hypotheses of the introduction to Chapter K, with the component
retained as an actual subgroup of the acting group. The symplectic central
quotient and the field parameter are supplied separately. No representation
recognition or conclusion about offenders is part of these hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.451 and 456–457.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Symplectic
open Theory.GroupTheory Representation.BinaryOffender

universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The genuine Chapter K input; the final application uses the full known-simple class. -/
structure SourceHypothesis (K : GroupClass.{u})
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop where
  finite_group : Finite G
  finite_module : FiniteDimensional (ZMod 2) V
  sqtk : IsSQTK K G
  fitting : generalizedFitting G = L
  quasisimple : IsQuasisimple L
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp L.subtype)
  cubic_le_two : cubicRatio ρ ≤ 2

end CFSG.Quasithin.ChapterK.Symplectic
