module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Layers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Marked

/-!
# Interfaces separating local seed recognition from geometric propagation

LocalConsequences is the output required from the first paragraph of
MS93 (4.6.12)(3), p.910. It records the conjugate span, its plane and seed
line, fixation by the first full actor, and the literal commutator image.
It has no constructor from the source seed here.

MarkedCyclicSeed is the output required after propagation through delta3
and delta4 and generation of the full local group, pp.910--911. Its actor
is twisted by the given NaturalU marking, so the proved conversion yields
the specified dual quotient. It is not an extra input to the source clause.
The seed construction and the propagation remain separate proof obligations.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Local output before the delta3--delta4 propagation, not source hypotheses. -/
structure LocalConsequences (d : LayerModule source (V R (alpha R)))
    (f : Frame source) (c : Vertex R) (x : Input (geometry := geometry) d f c) : Prop where
  conjugate_span : x.space = d.subspace (conjugateSpanBy (Z R c) (f.ambient true))
  seed_dimension : Module.finrank (ZMod 2) x.space = 2
  line_dimension : Module.finrank (ZMod 2) (d.subspace (Z R c)) = 1
  first_fixed : d.subspace (Z R c) ≤
    fixedSpace d.representation ((f.actor false).map source.projection)
  commutator_image : d.subspace ⁅d.preimage x.space, V R c⁆ = d.subspace (Z R c)

/-- The marked cyclic recognition hypotheses, required as propagation output. -/
structure MarkedCyclicSeed (common : CommonFacts R source geometry) (c : Vertex R)
    (d : LayerModule source (orbitSpan c)) where
  vector : d.Space
  nonzero : vector ≠ 0
  point_fixed : ∀ g ∈ Matrix.PSL3Two.pointParabolicSL,
    d.representation (dualTwist common.natural.marking g) vector = vector
  generates : BinaryLinearThree.ParabolicCyclic.orbitSpan
    (d.representation.comp (dualTwist common.natural.marking).toMonoidHom) ⊤ vector = ⊤
  plane_dimension : Module.finrank (ZMod 2) (BinaryLinearThree.ParabolicCyclic.orbitSpan
    (d.representation.comp (dualTwist common.natural.marking).toMonoidHom)
      Matrix.PSL3Two.lineParabolicSL vector) = 2

/-- Recognition of a genuinely constructed marked cyclic seed gives the actual
quotient; the three cyclic hypotheses are discharged by geometric propagation. -/
theorem MarkedCyclicSeed.quotient {common : CommonFacts R source geometry}
    {c : Vertex R} {d : LayerModule source (orbitSpan c)}
    (v : MarkedCyclicSeed common c d) : Nonempty (SpanQuotient source common c) :=
  spanQuotient_of_cyclic_seed common d v.vector v.nonzero v.point_fixed
    v.generates v.plane_dimension

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
