module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.MarkingExistence.CalibratedCharts.CentralLifting.FiniteKernelCharts
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.MarkingExistence.CalibratedCharts.CentralLifting.SL2Derived
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.MarkingExistence.CalibratedCharts.DiagonalContainment

/-!
Regular opposite root sections through reductive central covers.

Let `q : Y → Q` be a surjective central morphism with reductive source,
and let `p : SL₂ → Q` be an algebraic-group morphism. Two regular lifts
of its literal upper and lower curves extend to an algebraic-group
morphism `F : SL₂ → Y`, whose composite with `q` is `p`.

Scalar conjugation puts both lifted curves in the abstract derived
subgroup of `Y`. The central kernel meets that subgroup in a finite set,
so `FiniteKernelCharts` glues the root-word charts and proves their
multiplication law upstairs. This retains finite central kernels in
every characteristic and permits the full kernel to be positive
dimensional, as in GL₂ → PGL₂. Taking `Q` to be PGL₂ and `p` to be the
standard projection gives the rank-one central-cover application.

The consumer composes `F` with the supplied ambient morphism and applies
`marking_of_algebraic_root_curves` to the actual parametrized root
subgroups. Torus maximality and realization give diagonal containment;
it is not an additional premise. Construction of the quotient and its
two calibrated regular sections is separate from this lifting theorem.

Sources: Borel, *Linear Algebraic Groups*, §§13.13--13.14 and 13.18
(`refs/KGroup/Bor1/Chapter4.tex`); GLS3, §§1.9--1.12, especially the
opposite-root relations (`refs/KGroup/GLS3/Chapter1.tex`).
-/

open Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts.CentralLifting

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {Y Q : Variety k} [AlgebraicGroup Y] [AlgebraicGroup Q]

/-- Lift an SL₂ morphism through a reductive central cover from regular
lifts of its two standard root curves. No finiteness assumption on the
whole kernel is needed. -/
public theorem exists_sl2Morphism_of_reductive_central_cover
    (hY : IsReductiveAlgebraicGroup Y)
    (q : Morphism Y Q) (hqsurj : Function.Surjective q.onPoints)
    (hq : q.kernel ≤ Subgroup.center (Variety.Point Y))
    (p : Morphism (slVariety k 2) Q) (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism) :
    ∃ F : Morphism (slVariety k 2) Y,
      F.comp standardSL2UpperMorphism = u ∧
      F.comp standardSL2LowerMorphism = v ∧ q.comp F = p :=
  exists_sl2Morphism_of_finite_kernel_root_lifts q p u v hu hv
    (_root_.commutator (Variety.Point Y))
    (upper_mem_commutator_of_central_sl2_lift hY q hqsurj hq p u hu)
    (lower_mem_commutator_of_central_sl2_lift hY q hqsurj hq p v hv)
    (central_derived_kernel_finite hY q hq)

variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T} {α : D.Root}

/-- A reductive central cover with calibrated regular root sections
constructs an SL₂ marking for the literal opposite root parametrizations.
This supplies the compatible map and proves diagonal containment. -/
public theorem nonempty_sl2RootMarking_of_reductive_central_cover
    (hD : D.IsRealization) (hT : IsMaximalTorus T)
    (plus : OneParameterParametrization (D.rootSubgroup α).carrierVariety)
    (minus : OneParameterParametrization (D.rootSubgroup (D.neg α)).carrierVariety)
    (hY : IsReductiveAlgebraicGroup Y)
    (q : Morphism Y Q) (hqsurj : Function.Surjective q.onPoints)
    (hq : q.kernel ≤ Subgroup.center (Variety.Point Y))
    (p : Morphism (slVariety k 2) Q) (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism)
    (j : Morphism Y G)
    (hju : j.comp u = (D.rootSubgroup α).inclusion.comp plus.hom)
    (hjv : j.comp v = (D.rootSubgroup (D.neg α)).inclusion.comp minus.hom) :
    Nonempty (SL2RootMarking D α) := by
  obtain ⟨F, hFu, hFv, _⟩ :=
    exists_sl2Morphism_of_reductive_central_cover hY q hqsurj hq p u v hu hv
  refine ⟨marking_of_algebraic_root_curves plus minus hD hT (j.comp F) ?_ ?_⟩
  · rw [← Morphism.comp_assoc, hFu, hju]
  · rw [← Morphism.comp_assoc, hFv, hjv]

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts.CentralLifting
