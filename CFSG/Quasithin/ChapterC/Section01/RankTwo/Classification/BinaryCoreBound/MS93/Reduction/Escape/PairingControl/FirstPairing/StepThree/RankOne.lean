module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant

/-!
# The rank-one route to the alpha-side edge displacement

The opposite moving coordinates supply a compatible line residual fixing
Z_delta modulo the original radical Z[V,Q]. Two-perfect idempotence lifts
this fixation to normalization of K = [Z_delta,Q_alpha]. The delta-side
edge calculation makes K an elementary four-group, and step (1) places it
outside the fixed core. Residual recognition therefore gives K ≤ U_alpha.
The index-two action on U_alpha/K identifies K with the alpha displacement.

This proves the rank-one identification in MS93 (4.3.2)(3), printed p.884,
from the stated earlier module, normalization, initial and orientation
inputs. Neither H = U nor coordinates on Vcirc/U are assumed. The other
conclusions of step (3) remain with its assembly module.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The moving commutator is the alpha-side displacement at every incident
edge, using compatible opposite coordinates modulo Z[V,Q]. -/
theorem alpha_commutator (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (orientations : ∀ a, color R a = false → Nonempty (MovingOrientationAt a))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∀ t d, Adjacent R p.a t → Adjacent R d t → d ∈ movingNeighbors geometry p.a →
      ⁅Z R d, Q R p.a⁆ = edgeDisplacement p.a t := by
  obtain ⟨o⟩ := orientations p.a p.color_a
  obtain ⟨ip⟩ := initial p
  intro t d hat hdt hd
  obtain ⟨flag, hfix⟩ := RankOne.exists_lineResidual_fixed_neighbor source hb modules
    initial p bad o t d hat hdt hd
  apply alpha_commutator_of_le_U source hb modules initial p bad p.a t d p.color_a
    hat hdt hd
  exact RankOne.small_invariant_le_U source geometry hb modules p.a p.color_a o flag
    ⁅Z R d, Q R p.a⁆
    (moving_commutator_le_B hb p.color_a hd o)
    (moving_commutator_elementary source modules p.color_a hd)
    (moving_commutator_card_at p (by omega) initial bad p.a t d p.color_a hat hdt hd).le
    (normalizer_commutator_ge_right _ _)
    (moving_commutator_not_le_fixed hb transfer ip bad hd)
    (RankOne.moving_commutator_normalized_of_radical_fixed source hb p.color_a hd
      o flag hfix)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
