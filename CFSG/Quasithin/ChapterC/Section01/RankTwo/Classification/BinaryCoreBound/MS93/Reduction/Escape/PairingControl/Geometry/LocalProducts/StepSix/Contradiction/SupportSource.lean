module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Support
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Start-Z support in MS93 (4.3.2)(6)

If K lies in U_back but not in Z_start, the natural-module supplement
identity gives Z_back = K join (Z_back intersect Z_start). If K centralizes
Z_endpoint, the first factor has trivial commutator with Z_endpoint, while
the second has commutator in Z_start because the endpoint normalizes that
layer. Moreover Z_back lies in Q_start and centralizes Z_start. Thus the
commutator-preimage subgroup contains both factors and gives the required
bound for their join, with its normalizer premise verified.

The start-Z obstruction therefore places every endpoint-centralizing
subgroup of U_back in Z_start. Applied to R_4 this supports the nontrivial
R_mu branch. Applied to the fourth natural intersection, its order four
identifies it with the original edge plane and contradicts that edge's
escape from the endpoint kernel.

The first target on printed p.885 is Z_alpha followed by a comma, not
Z_alpha'. These source variants preserve the separate endpoint-target
conditional interfaces in Support.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank
two* (1993), (4.3.2)(6), printed p.885.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}
namespace EscapingWitness
variable {p : Counterexample geometry} {d : Vertex R} (w : EscapingWitness p d)

/-- The supplement calculation bounds the commutator in the starting Z-layer. -/
theorem back_commutator_le_start_of_not_le (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R w.choice.back)
    (hC : K ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)))
    (hnot : ¬ K ≤ Z R p.a) : ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a := by
  have hbackC : Z R w.choice.back ≤ centralizer (Z R p.a : Set (FreeAmalgam R)) :=
    ((moving_Z_le_V w.choice.moving).trans (geometry.V_le_Q hb p.a p.color_a)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes p.a p.color_a)))
  have hendN : Z R p.a' ≤ normalizer (Z R p.a : Set (FreeAmalgam R)) :=
    p.end_Z_le_start_stabilizer.trans (Z_normalized R p.a)
  have hstart : ⁅Z R p.a, Z R p.a'⁆ ≤ Z R p.a :=
    le_normalizer_iff_commutator_le_left.mp hendN
  have hpre : Z R w.choice.back ≤
      commutatorPreimage (Z R w.choice.back) (Z R p.a') (Z R p.a) := by
    conv_lhs => rw [w.back_Z_eq_sup_of_not_le source hb modules facts initial bad K hK hnot]
    apply sup_le
    · exact le_commutatorPreimage (hK.trans (U_le_Z _))
        (by rw [commutator_eq_bot_iff_le_centralizer.mpr hC]; exact bot_le)
    · exact le_commutatorPreimage inf_le_left
        ((commutator_mono inf_le_right le_rfl).trans hstart)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      (hbackC.trans (Subgroup.centralizer_le_normalizer _)))

/-- The corrected obstruction forces support in Z_start. -/
theorem centralizing_back_natural_le_Z_of_start_obstruction (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R w.choice.back)
    (hC : K ≤ centralizer (Z R p.a' : Set (FreeAmalgam R))) : K ≤ Z R p.a := by
  by_contra hnot
  exact obstruction (w.back_commutator_le_start_of_not_le source hb modules facts
    initial bad K hK hC hnot)

/-- R_4 support from the start-Z obstruction for this witness's backward choice. -/
theorem Rfour_le_Z_of_start_obstruction (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (hd : Before p.a p.a' d 4)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a) :
    w.toRadiusWitness.Rfour ≤ Z R p.a :=
  w.centralizing_back_natural_le_Z_of_start_obstruction source hb modules facts initial bad
    obstruction _ (w.toRadiusWitness.Rfour_le_backward_natural source facts hd)
    (w.toRadiusWitness.Rfour_centralizes_endpoint source modules hlarge hd)

/-- The order-four intersection equals the original edge plane. -/
theorem fourth_intersection_eq_start_of_card_four_of_start_obstruction
    (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a)
    (hcard : Nat.card (U R w.choice.back ⊓ U R w.fourth : Subgroup (FreeAmalgam R)) = 4)
    (hC : U R w.choice.back ⊓ U R w.fourth ≤
      centralizer (Z R p.a' : Set (FreeAmalgam R))) :
    U R w.choice.back ⊓ U R w.fourth = U R w.choice.back ⊓ U R p.a := by
  have hZ := w.centralizing_back_natural_le_Z_of_start_obstruction
    source hb modules facts initial bad obstruction _ inf_le_left hC
  rw [w.back_natural_inf_start_natural source hb modules facts initial bad]
  have hle : U R w.choice.back ⊓ U R w.fourth ≤ edgeDisplacement p.a w.choice.edge := by
    rw [← w.back_natural_inf_start_Z source hb modules facts initial bad]
    exact le_inf inf_le_left hZ
  let : Finite (U R p.a) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at p.a p.color_a]; decide)
  let : Finite (edgeDisplacement p.a w.choice.edge) := Finite.of_injective
    (inclusion (Initial.edge_le_natural source p.a w.choice.edge p.color_a w.choice.adjacent_start))
    (inclusion_injective _)
  exact eq_of_le_of_card_ge hle (by
    rw [hcard, FirstPairing.StepThree.edge_card p (by omega) initial
      p.a w.choice.edge p.color_a w.choice.adjacent_start])

/-- The corrected support argument contradicts the original escaping edge. -/
theorem false_of_fourth_intersection_of_start_obstruction (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a)
    (hcard : Nat.card (U R w.choice.back ⊓ U R w.fourth : Subgroup (FreeAmalgam R)) = 4)
    (hC : U R w.choice.back ⊓ U R w.fourth ≤
      centralizer (Z R p.a' : Set (FreeAmalgam R))) : False := by
  apply w.choice.escapes
  have he := w.fourth_intersection_eq_start_of_card_four_of_start_obstruction
    source hb modules facts initial bad obstruction hcard hC
  rw [w.back_natural_inf_start_natural source hb modules facts initial bad] at he
  rw [← modules.natural.centralizer p.a' p.end_color]
  exact le_inf
    ((Initial.edge_le_natural source p.a w.choice.edge p.color_a w.choice.adjacent_start).trans
      ((U_le_Z p.a).trans
        (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).1))
    ((he ▸ hC).trans (centralizer_le (U_le_Z p.a')))

end EscapingWitness
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
