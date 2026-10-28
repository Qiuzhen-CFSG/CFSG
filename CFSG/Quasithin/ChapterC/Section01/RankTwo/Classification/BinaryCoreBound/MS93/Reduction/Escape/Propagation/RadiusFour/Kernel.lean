module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Kernel.Normality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Kernel.Intersection

/-!
# The two kernel bounds completing MS93 (4.3.8)

The normal-radius contradiction excludes containment of the radius-four
ball in the fourth predecessor's kernel. The final xi-conjugate argument
then places its intersection with that kernel in the second predecessor's
kernel. ForwardFacts retains precisely the explicitly supplied preceding
commutation, nonmovement, and radius-join conclusions; no later escape
or classification result is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), printed p.889, final two paragraphs of (4.3.8). This module stops
before the final contradiction for (4.3).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Both literal kernel bounds in (4.3.8), conditional only on the stated
preceding stages. The normalization-transfer premise is not needed here. -/
theorem kernelBounds (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (backward : BackwardFacts geometry)
    (forward : ForwardFacts geometry) : KernelBounds geometry := by
  have hnot (p : Counterexample geometry) (d : Vertex R) (hd : Before p.a p.a' d 4) :
      ¬ VBall R p.a 4 ≤ Q R d :=
    Kernel.ball_not_le source hb modules initial control edge rigidity backward forward p hd
  exact {
    not_le := hnot
    intersection_le := fun p d hd =>
      Kernel.intersection_le_of_not_le source hb rigidity backward p hd (hnot p d hd)
  }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
