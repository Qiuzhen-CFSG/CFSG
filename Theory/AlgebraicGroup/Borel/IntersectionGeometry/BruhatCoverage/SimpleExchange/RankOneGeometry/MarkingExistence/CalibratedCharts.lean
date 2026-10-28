module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.Inputs
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.MarkingExistence.CalibratedCharts.DiagonalContainment

/-!
Local SL₂ markings from compatible algebraic root curves.

`DiagonalContainment` proves that the diagonal condition follows from
compatibility of the two curves and maximality of the torus. The family here
uses the fundamental roots of the supplied positive system, not `D.simple`,
and supplies the literal premise consumed by `MarkingExistence`.

Compatible-curve existence remains an explicit geometric input. Constructing
it from reductivity requires the earlier rank-one centralizer and PGL₂
quotient geometry and a compatible SL₂ lift; this conditional theorem does
not assert that those inputs already exist.
Sources: GLS3, §§1.9--1.12; Borel, §§13.13--13.14 and 13.18.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T}

/-- Compatible algebraic curves at the actual fundamental roots supply the
local-marking premise of `nonempty_of_local_markings_borel_fixed_roots`.
The compatible curves remain an explicit geometric premise. -/
public theorem nonempty_markings_of_algebraic_root_curves
    (hD : D.IsRealization) (hT : IsMaximalTorus T) (P : Set D.Root)
    (hcurves : ∀ i : {α // α ∈ FundamentalRootsFor D P},
      ∃ (plus : OneParameterParametrization (D.rootSubgroup i.val).carrierVariety)
        (minus : OneParameterParametrization (D.rootSubgroup (D.neg i.val)).carrierVariety)
        (F : Morphism (slVariety k 2) G),
        F.comp standardSL2UpperMorphism = (D.rootSubgroup i.val).inclusion.comp plus.hom ∧
        F.comp standardSL2LowerMorphism =
          (D.rootSubgroup (D.neg i.val)).inclusion.comp minus.hom) :
    ∀ i : {α // α ∈ FundamentalRootsFor D P}, Nonempty (SL2RootMarking D i.val) := by
  intro i
  obtain ⟨plus, minus, F, hu, hl⟩ := hcurves i
  exact ⟨marking_of_algebraic_root_curves plus minus hD hT F hu hl⟩

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts
