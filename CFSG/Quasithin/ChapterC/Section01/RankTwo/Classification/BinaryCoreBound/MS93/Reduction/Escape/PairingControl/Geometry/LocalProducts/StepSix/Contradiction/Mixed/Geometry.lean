module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Preliminaries

/-!
# The fourth-vertex edge plane in MS93 step (6)

The critical pair (alpha-4, alpha'-4) puts alpha-4 in the moving
neighborhood of alpha-2. Step (3), transported from the original genuine
counterexample, identifies their natural intersection with the intervening
edge displacement and gives its order four. The mixed actors lie in the
backward kernel, so their commutator is contained in this plane.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

namespace EscapingWitness
variable {p : Counterexample geometry} {d : Vertex R} (w : EscapingWitness p d)

/-- Critical forward nonnormality supplies movement at the actual backward vertex. -/
theorem fourth_moving_at_back (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (hd : Before p.a p.a' d 4) :
    w.fourth ∈ movingNeighbors geometry w.choice.back := by
  apply Selection.Six.critical_start_moving_at_second source hb modules
    w.fourth_color w.toRadiusWitness.back_color w.critical w.fourth_back_distance
  obtain ⟨h₁, h₂⟩ := w.toRadiusWitness.back_before hd
  have hf := w.fourth_back_distance
  omega

/-- Step (3) identifies the fourth/backward intersection with their shared edge. -/
theorem fourth_natural_intersection_eq_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hd : Before p.a p.a' d 4) :
    U R w.choice.back ⊓ U R w.fourth = edgeDisplacement w.choice.back w.third := by
  have hm := w.fourth_moving_at_back source hb modules hd
  have h := Continuation.moving_natural_intersection source hb modules facts p initial bad
    w.toRadiusWitness.back_color w.back_adjacent w.fourth_adjacent hm
  rw [inf_comm]
  apply le_antisymm ((inf_le_inf_left _ (U_le_Z w.choice.back)).trans h.le)
  exact le_inf (h.ge.trans inf_le_left)
    (Initial.edge_le_natural source _ _ w.toRadiusWitness.back_color w.back_adjacent)

/-- The order comes from the fourth/backward edge, independently of the
later equality with the original starting edge. -/
theorem fourth_natural_intersection_card (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hd : Before p.a p.a' d 4) :
    Nat.card (U R w.choice.back ⊓ U R w.fourth : Subgroup (FreeAmalgam R)) = 4 := by
  rw [w.fourth_natural_intersection_eq_edge source hb modules facts initial bad hd]
  exact FirstPairing.StepThree.edge_card p (by omega) initial _ _
    w.toRadiusWitness.back_color w.back_adjacent

/-- The literal mixed actor is Z_mu joined with Z_(alpha'-2). -/
theorem mixed_commutator_le_fourth_intersection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hd : Before p.a p.a' d 4) (hzero : w.Rmu = ⊥) :
    ⁅Z R w.fourth, Z R w.mu ⊔ Z R p.c⁆ ≤ U R w.choice.back ⊓ U R w.fourth := by
  rw [w.fourth_natural_intersection_eq_edge source hb modules facts initial bad hd,
    ← facts.edge_eq _ _ _ w.toRadiusWitness.back_color w.back_adjacent
      w.fourth_adjacent (w.fourth_moving_at_back source hb modules hd),
    ← FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega) initial bad
      _ _ _ w.toRadiusWitness.back_color w.back_adjacent w.fourth_adjacent
      (w.fourth_moving_at_back source hb modules hd)]
  exact commutator_mono le_rfl (w.mixed_actors_le_back_kernel source modules hd hzero)

omit [Finite M] in
/-- Both printed factors lie in the radius at alpha'-4. -/
theorem mixed_actors_le_endpoint_radius (hd : Before p.a p.a' d 4) :
    Z R w.mu ⊔ Z R p.c ≤ V R d := by
  apply sup_le (moving_Z_le_V w.mu_moving)
  apply le_iSup_of_le p.c
  apply le_iSup_of_le (show (cosetGraph R).dist p.c d ≤ 2 from ?_)
  · exact le_rfl
  · rw [SimpleGraph.dist_comm, before_distance (geometry := geometry) hd p.before (by decide)]

/-- Local normalization at alpha'-4 bounds the mixed commutator by its radius. -/
theorem mixed_commutator_le_endpoint_radius (source : LocalSource L R)
    (hd : Before p.a p.a' d 4) :
    ⁅Z R w.fourth, Z R w.mu ⊔ Z R p.c⁆ ≤ V R d := by
  apply (commutator_mono le_rfl (w.mixed_actors_le_endpoint_radius hd)).trans
  exact le_normalizer_iff_commutator_le_right.mp
    ((source.critical_Z_le_stabilizer geometry _ w.fourth_color _ w.critical).1.trans
      (V_normalized d))

/-- The strict distance bound makes the entire mixed commutator centralize Z_alpha'. -/
theorem mixed_commutator_centralizes_endpoint (source : LocalSource L R)
    (hlarge : 6 < geometry.b R) (hd : Before p.a p.a' d 4) :
    ⁅Z R w.fourth, Z R w.mu ⊔ Z R p.c⁆ ≤
      centralizer (Z R p.a' : Set (FreeAmalgam R)) := by
  have hQ : V R d ≤ Q R p.a' :=
    V_le_Q_of_distance (endpoint_color hd) (by rw [hd.1]; exact hlarge)
  exact ((w.mixed_commutator_le_endpoint_radius source hd).trans hQ).trans
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.a' p.end_color)))

end EscapingWitness
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
