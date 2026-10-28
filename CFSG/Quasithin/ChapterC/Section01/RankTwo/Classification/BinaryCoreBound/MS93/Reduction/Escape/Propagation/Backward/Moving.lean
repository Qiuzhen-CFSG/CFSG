module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Normality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Far
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Symmetry

/-!
# Moving symmetry and far propagation

The normal-subgroup and three-subgroup argument proves moving symmetry from
the product stage and preceding source inputs. The far exclusion follows by
transporting the product stage to the vertex four before the endpoint and
contradicting critical noncommutation. A local conjugator and the resulting
normal Z-product then put every moving radius group in the kernel two before
the endpoint. This constructs all three fields of MovingFacts; ProductFacts
remains the explicit preceding-stage input to be supplied by Backward assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(ii)--(iii), p.888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Assemble both far assertions from moving symmetry and the product stage. -/
theorem movingFacts_of_symmetric (source : LocalSource L R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (rigidity : RigidityFacts geometry) (products : ProductFacts geometry)
    (symmetric : ∀ p : Counterexample geometry, ∀ d,
      d ∈ movingNeighbors geometry p.a ↔ p.a ∈ movingNeighbors geometry d) :
    MovingFacts geometry := by
  refine ⟨symmetric, ?_, ?_⟩
  · intro p d hd
    obtain ⟨hi⟩ := initial p
    exact far_not_moving_of_symmetric p (rigidity.six_lt p) hi products symmetric hd
  · intro p d hd
    obtain ⟨hi⟩ := initial p
    exact radius_bound_of_symmetric source p (rigidity.six_lt p) hi products symmetric hd

/-- Original MS93 (4.3.7)(ii)--(iii), from (i) and the preceding source inputs.
Moving symmetry and both far clauses are conclusions, not hypotheses. -/
theorem movingFacts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p)
    (edge : EdgeTransfer geometry) (rigidity : RigidityFacts geometry)
    (products : ProductFacts geometry) : MovingFacts geometry :=
  movingFacts_of_symmetric source initial rigidity products
    (moving_symmetric source hb modules initial control edge products)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
