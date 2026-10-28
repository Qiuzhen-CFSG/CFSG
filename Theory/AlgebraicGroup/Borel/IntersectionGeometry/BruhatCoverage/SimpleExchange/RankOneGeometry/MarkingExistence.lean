module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.Inputs
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.MarkingExistence.Cartan
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.MarkingExistence.FixedRadicalUniqueness

/-!
Assembly of simple-root markings from local SL₂ maps and root uniqueness.

The local maps need only identify the two literal matrix curves and place
their diagonal in the actual torus. The Cartan calculation proves that their
reflection has exactly the weight prescribed by the supplied root datum.
Multiplicity one identifies its conjugated root subgroup. The fixed-radical
geometry of Borels supplies this uniqueness input. Choice then gives
a marking at every fundamental root of the supplied positive system.

The reductive existence theorem remains open until the compatible local maps
and root-subgroup uniqueness have been proved from reductivity and maximality
of the torus. Neither additional premise is included in `IsRealization`.
Sources: GLS3, 1.9.5(b)--(f), 1.9.6; Borel, §§13.18 and 14.6--14.8.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T} {P : Set D.Root}

/-- Compatible local SL₂ maps and root multiplicity one give all fields of
`SimpleRootMarkings`, including the literal direct-conjugation reflection law.
The indices are the fundamental roots of `P`, independently of `D.simple`. -/
public noncomputable def of_local_markings_multiplicityOne
    (hD : D.IsRealization) (hT : IsTorus T.carrierVariety)
    (localMarking : (i : {α // α ∈ FundamentalRootsFor D P}) → SL2RootMarking D i.val)
    (hmult : ∀ β, RootWeightSpaceMultiplicityOne T (D.rootWeight β)) :
    SimpleRootMarkings D P where
  marking := localMarking
  reflection_root := fun i β =>
    (localMarking i).reflection_root_of_multiplicityOne hD hT β (hmult _)

/-- Conditional existence, with exactly two independent remaining inputs:
compatible rank-one maps and uniqueness of the actual root subgroups. -/
public theorem nonempty_of_local_markings_multiplicityOne
    (hD : D.IsRealization) (hT : IsTorus T.carrierVariety)
    (hlocal : ∀ i : {α // α ∈ FundamentalRootsFor D P}, Nonempty (SL2RootMarking D i.val))
    (hmult : ∀ β, RootWeightSpaceMultiplicityOne T (D.rootWeight β)) :
    Nonempty (SimpleRootMarkings D P) := by
  classical
  exact ⟨of_local_markings_multiplicityOne hD hT
    (fun i => Classical.choice (hlocal i)) hmult⟩

/-- The existing fixed-radical geometry discharges root uniqueness in the
marking construction. Only compatible local SL₂ maps and the fixed-radical
source theorem remain to be supplied by the reductive assembly. -/
public theorem nonempty_of_local_markings_borel_fixed_roots
    (hD : D.IsRealization) (hT : IsSubtorus T)
    (hlocal : ∀ i : {α // α ∈ FundamentalRootsFor D P}, Nonempty (SL2RootMarking D i.val))
    (hfixed : HasBorelFixedRootGroups D) : Nonempty (SimpleRootMarkings D P) :=
  nonempty_of_local_markings_multiplicityOne hD hT hlocal
    (multiplicityOne_of_borel_fixed_roots hD hT hfixed)

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry
