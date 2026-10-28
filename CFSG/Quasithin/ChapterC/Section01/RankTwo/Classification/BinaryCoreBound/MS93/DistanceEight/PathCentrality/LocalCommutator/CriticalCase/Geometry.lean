module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Source

/-!
# The backward critical configuration in MS93 (4.4.1)

The selected backward vertex is in the actual G_c-orbit of the original
vertex a. Its two-edge walk is retained, and its noncontainment constructs
a shortest critical replacement with the same overlapping subwalk. The
orbit relation preserves the entire local span, hence its expanded natural
section condition and failure of fixedness of the displacement.

The witness also retains the nontrivial triple commutator in claim (2).
Critical minimality and b > 4 show that the radius-two group at the new
endpoint centralizes the old endpoint Z-layer. Consequently the whole
backward displacement cannot lie in that radius-two group.

There is no witness-existence theorem here. The two cases in the selection
on p.891, including the (1.5)/(1.6) argument inside B_c, remain to be proved.
B_c is the fixed preimage on V_c/Z_c; D_c is fixedCore, a different group.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), claim (2), p.891, and the start of p.892.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- Conjugating the seed within the same local stabilizer leaves its orbit span unchanged. -/
theorem span_eq_of_local_conjugator {a c : Vertex R} {g : FreeAmalgam R}
    (hg : g ∈ stabilizer R c) : localZSpan R (act R g a) c = localZSpan R a c := by
  have one_way (a : Vertex R) (g : FreeAmalgam R) (hg : g ∈ stabilizer R c) :
      localZSpan R (act R g a) c ≤ localZSpan R a c := by
    apply iSup_le
    intro h
    rw [← act_mul]
    exact le_iSup (fun k : stabilizer R c => Z R (act R k a))
      ⟨g * h, (stabilizer R c).mul_mem hg h.property⟩
  apply le_antisymm (one_way a g hg)
  have hh := one_way (act R g a) g⁻¹ ((stabilizer R c).inv_mem hg)
  simpa only [← act_mul, mul_inv_cancel, act_one] using hh

/-- The actual orbit, walk, critical noncontainment and triple commutator required by claim (2). No existence is assumed in the source inputs. -/
structure BackwardWitness (R : Subgroup M) (geometry : Geometry R) (a c : Vertex R) where
  endpoint : Vertex R
  path : CriticalPath R geometry c endpoint
  backward : Vertex R
  conjugator : FreeAmalgam R
  local_conjugator : conjugator ∈ stabilizer R c
  conjugator_image : act R conjugator a = backward
  backwardWalk : (cosetGraph R).Walk backward c
  backward_length : backwardWalk.length = 2
  noncontainment : ¬ Z R backward ≤ Q R (path.walk.getVert (path.walk.length - 2))
  triple_ne : ⁅⁅Z R backward, Q R c⁆, Z R endpoint⁆ ≠ ⊥

namespace BackwardWitness
variable {a c : Vertex R} (w : BackwardWitness R geometry a c)

/-- The vertex alpha'-2 on the retained original critical path. -/
def predecessor : Vertex R := w.path.walk.getVert (w.path.walk.length - 2)

/-- The selected backward span is the original span, at the same center. -/
theorem span_eq : localZSpan R w.backward c = localZSpan R a c := by
  rw [← w.conjugator_image]
  exact span_eq_of_local_conjugator w.local_conjugator

/-- Transport the full quotient-section condition, without replacing it by a dimension tag. -/
theorem hasNaturalSection_iff : HasNaturalSection R w.backward c ↔
    HasNaturalSection R a c := by
  simp only [HasNaturalSection, w.span_eq]

/-- The backward vertex has the original M-color. -/
theorem backward_color (ha : color R a = false) : color R w.backward = false := by
  rw [← w.conjugator_image, action_preserves_color]
  exact ha

/-- The ordered-pair orbit preserves the exact distance two. -/
theorem backward_distance (hd : (cosetGraph R).dist a c = 2) :
    (cosetGraph R).dist w.backward c = 2 := by
  have hfix : act R w.conjugator c = c := w.local_conjugator
  simpa only [w.conjugator_image, hfix, hd] using dist_act R w.conjugator a c

/-- Failure of fixedness transports along the retained local orbit. -/
theorem displacement_not_le_fixed (hb : 2 < geometry.b R)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c) :
    ¬ ⁅Z R w.backward, Q R c⁆ ≤ fixedCore R c := by
  intro h
  apply hn
  apply (span_commutator_le_fixed_iff w.path.start_color hd.le hb).mp
  have hh := (span_commutator_le_fixed_iff w.path.start_color
    (w.backward_distance hd).le hb).mpr h
  rwa [w.span_eq] at hh

/-- Prepend the actual two-edge walk and shorten the old path by two edges. -/
def shifted (ha : color R a = false) (hb : 2 ≤ geometry.b R) :
    CriticalPath R geometry w.backward w.predecessor :=
  w.path.prepend_two hb (w.backward_color ha) w.backwardWalk
    w.backward_length w.noncontainment

/-- Every vertex on the common subwalk is retained at its shifted position. -/
theorem shifted_overlap (ha : color R a = false) (hb : 2 ≤ geometry.b R)
    {i : ℕ} (hi : i ≤ w.path.walk.length - 2) :
    (w.shifted ha hb).walk.getVert (i + 2) = w.path.walk.getVert i :=
  w.path.prepend_two_overlap hb (w.backward_color ha) w.backwardWalk
    w.backward_length w.noncontainment hi

/-- Evenness of the critical distance puts the predecessor in the M-orbit. -/
theorem predecessor_color : color R w.predecessor = false := by
  have he : Even w.path.walk.length := by
    rw [w.path.shortest, w.path.critical.1]
    exact geometry.even c w.path.start_color
  apply (w.path.vertex_color (Nat.sub_le _ _)).mpr
  rw [Nat.even_iff] at he ⊢
  omega

/-- The predecessor is exactly two edges before the endpoint. -/
theorem predecessor_distance (hb : 2 ≤ geometry.b R) :
    (cosetGraph R).dist w.predecessor w.endpoint = 2 := by
  change (cosetGraph R).dist (w.path.walk.getVert _) w.endpoint = 2
  rw [w.path.dist_end]
  have hl := w.path.length_eq_b
  omega

/-- Critical minimality puts the predecessor Z-layer in the original center kernel. -/
theorem predecessor_Z_le_center_kernel (hb : 0 < geometry.b R) :
    Z R w.predecessor ≤ Q R c := by
  apply Z_le_Q_of_dist_lt R w.predecessor
    (geometry.exists_critical _ w.predecessor_color)
  rw [geometry.distance_constant _ w.predecessor_color, SimpleGraph.dist_comm]
  change (cosetGraph R).dist c (w.path.walk.getVert _) < geometry.b R
  rw [w.path.dist_start (Nat.sub_le _ _), w.path.length_eq_b]
  omega

/-- When b > 4, the entire predecessor radius group centralizes the endpoint Z-layer. -/
theorem predecessor_V_centralizes_endpoint (hb : 4 < geometry.b R) :
    ⁅V R w.predecessor, Z R w.endpoint⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_trans (V_le_Q_of_dist_add_two_lt R (geometry := geometry) w.predecessor_color ?_)
  · exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes w.endpoint w.path.end_color))
  · rw [w.predecessor_distance (by omega)]
    exact hb

/-- The nontrivial triple commutator prevents trapping the whole backward displacement. -/
theorem displacement_not_le_predecessor_V (hb : 4 < geometry.b R) :
    ¬ ⁅Z R w.backward, Q R c⁆ ≤ V R w.predecessor := by
  intro h
  apply w.triple_ne
  apply le_bot_iff.mp
  exact (commutator_mono h le_rfl).trans
    (w.predecessor_V_centralizes_endpoint hb).le

end BackwardWitness

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
