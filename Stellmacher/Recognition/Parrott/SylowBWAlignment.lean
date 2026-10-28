module

public import Stellmacher.Recognition.Parrott.SylowBWSquareInputs
public import Stellmacher.Recognition.Parrott.SylowBWIntrinsicQuadraticModel
public import Theory.GroupAction.FiveFourQuadraticOrthogonality

/-!
# Aligning b with the outer action chain

For every supplied action frame, the actual core square map sends the class
of b to the displacement of the class of w by the square of the outer actor.
The two core quotients are elementary of order sixteen, so five-four quadratic
orthogonality makes their central commutator pairing trivial. Its evaluation
is exactly [b,w]=1 in the ambient group. Applying this to the existing action
frame construction preserves every supplied mark and gives the required frame.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p.678, the choice preceding equation (2).
-/

open Subgroup
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Equation (2) for b,w holds for every supplied outer action frame. -/
public theorem ParrottSylowActionData.b_commutator_w
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z) :
    Tits.parrottCommutator n.b f.w = 1 := by
  obtain ⟨hV, hVcard, hW, hWcard⟩ := parrott_core_quadratic_quotients h
  let := hV
  let := hW
  obtain ⟨φ, hφ, d, g, β, ω, hg, hdisp, hne, hpair⟩ :=
    f.exists_bw_quadratic_model h
  exact hpair.mp (d.square_displacement_orthogonality hVcard hWcard φ hφ
    g hg β ω hdisp hne)

/-- The supplied normalizer data admit an action frame satisfying [b,w]=1,
with the original t, v, elementary subgroup and Sylow subgroup unchanged. -/
public theorem ParrottNormalizerFusionData.exists_sylow_action_commutator_bw
    (n : ParrottNormalizerFusionData e)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    ∃ f : ParrottSylowActionData n, Tits.parrottCommutator n.b f.w = 1 := by
  obtain ⟨f⟩ := n.exists_sylow_action h hN
  exact ⟨f, f.b_commutator_w h⟩

end Stellmacher.Recognition
