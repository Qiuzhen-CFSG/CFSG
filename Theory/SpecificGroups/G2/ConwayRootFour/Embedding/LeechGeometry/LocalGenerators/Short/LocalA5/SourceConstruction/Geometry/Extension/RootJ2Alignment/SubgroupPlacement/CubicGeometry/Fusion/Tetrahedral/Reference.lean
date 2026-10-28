module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.Reference

/-!
# The two geometric inputs at one literal fixed-free cubic

The reference is the fourth power of the commutator of the retained icosian
ATLAS generators, modulo precisely the central signs. Its order, membership
in C(I), and fixed-freeness on the whole binary Leech module are proved in
`RootModel.Reference`.

Two concrete facts about this one centralizer remain separate: conjugacy of
all ambient transports of the literal scalar tetrahedron that lie in it,
and existence of one normalizing element acting non-innerly on I. The second
is only a single outer actor; the inner actions are already realized by I.
The transport and automorphism arguments in `Tetrahedral` apply these inputs
to every fixed-free cubic, using the explicitly supplied ambient fusion.
Neither definition asserts its own inhabitance or identifies a Suzuki model.

Source: Aschbacher, *Sporadic Groups* (1994), 48.3 and its root-subgroup
conventions (pp.268–269), 49.1–49.2 (p.280), and 49.5 (pp.283–284).
-/

@[expose] public noncomputable section
open Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- The literal full centralizer of the fixed reference cubic subgroup. -/
def referenceCubicCentralizer : Subgroup LeechCentralQuotient :=
  Subgroup.centralizer (Subgroup.zpowers RootModel.referenceCubic : Set LeechCentralQuotient)

/-- Root-tetrahedron conjugacy required only in the one reference centralizer.
The subgroups are actual ambient conjugates of scalarFour.range. -/
def ReferenceTetrahedralOrbit : Prop :=
  ∀ g : LeechCentralQuotient,
    Subgroup.zpowers RootModel.referenceCubic ≤ Subgroup.centralizer
      (I.map (MulAut.conj g).toMonoidHom : Set LeechCentralQuotient) →
    ∃ c ∈ referenceCubicCentralizer,
      (I.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom = I

/-- One actual element centralizing the reference cubic and inducing an outer
(non-inner) automorphism of the literal scalar tetrahedron. -/
def ReferenceOuterAction : Prop :=
  ∃ t ∈ referenceCubicCentralizer,
    t ∈ Subgroup.normalizer (I : Set LeechCentralQuotient) ∧
      ¬ ∃ j ∈ I, ∀ i ∈ I, MulAut.conj t i = MulAut.conj j i

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
