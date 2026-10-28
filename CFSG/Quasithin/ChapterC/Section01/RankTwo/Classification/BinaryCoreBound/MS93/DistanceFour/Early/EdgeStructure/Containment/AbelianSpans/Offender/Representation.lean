module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.PairedSpans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The literal central-quotient action required by the binary span argument

This interface fixes the underlying space to W/Z(W). The acting quotient is
the actual stabilizer modulo Q, identified with SL₃(2) by a surjective map
with its exact kernel. An explicit equation requires the action on quotient
representatives to be ambient conjugation. Linearization is the canonical
binary vector space on this same elementary abelian quotient.

The paired-span construction supplies the geometric inputs for this model.
Its construction, including faithfulness, self-duality from the order-two
commutator pairing, and the FF index comparison, is still required. This
file only publishes the interface; it does not assert that it is inhabited.
A separate binary SL₃(2) argument must exclude a faithful self-dual FF-module
before this route can discharge the nonabelian-span hypothesis.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.4), first paragraph,
printed p.902. The central quotient is the one in its nonabelian-span step.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
variable {M : Type*} [Group M] {R : Subgroup M}

/-- A compatible action on the specified central quotient, not an arbitrary module. -/
structure SpanQuotientAction (a : Vertex R) (W : Subgroup (FreeAmalgam R)) where
  finite : Finite W
  normalized : stabilizer R a ≤ normalizer (W : Set (FreeAmalgam R))
  elementary : IsElementaryAbelian 2 (W ⧸ center W)
  projection : stabilizer R a →* SL
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.ker = (Q R a).subgroupOf (stabilizer R a)
  action : SL →* MulAut (W ⧸ center W)
  conjugation : ∀ (g : stabilizer R a) (x y : W),
    (y : FreeAmalgam R) = (g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
    action (projection g) (QuotientGroup.mk' (center W) x) =
      QuotientGroup.mk' (center W) y
  faithful : Function.Injective action
  selfDual : letI := elementary
    Nonempty ((Offenders.linearize action).Equiv (Offenders.linearize action).dual)
  offending : letI := elementary
    Representation.BinaryOffender.IsFFModule (Offenders.linearize action)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
