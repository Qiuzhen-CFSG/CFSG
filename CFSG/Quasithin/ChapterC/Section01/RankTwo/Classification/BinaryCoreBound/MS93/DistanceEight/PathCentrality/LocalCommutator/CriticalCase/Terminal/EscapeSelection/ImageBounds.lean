module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.ImageBounds.Involutions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Conditional assembly of both terminal image bounds

The first bound follows by excluding a small involution on the full radius
quotient. For the second, transport the original ordered pair to the backward
center, retaining its conjugator, failure of fixedness and full local-span
nonnaturality. Apply the earlier inside-B selector to the shifted critical
path. Its predecessor is exactly the vertex four before the old endpoint,
so the same first-bound argument applies.

Two genuine source inputs remain explicit: recognition of the original
local span from a small full-radius involution, and the fixed-path inside-B
selection from claim (2). The latter has its existing independent owner.
This module does not claim the unconditional two bounds until both inputs
are discharged. It uses neither the later (4.4) conclusions nor a universal
nonnaturality hypothesis.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), printed pp.891--892.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection.ImageBounds
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The two image bounds with precisely the full-radius involution exclusion and the
fixed-path inside-B selector left explicit. The selector is the earlier
source claim (2), already owned by the backward-selection task. -/
theorem image_bounds_of_involution_obstruction_and_selection
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (hnone : ¬ HasNaturalSection R a c)
    (w : BackwardWitness R geometry a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hnat : ¬ HasSmallRadiusInvolution c)
    (select : ∀ (r x e : Vertex R), color R r = false → color R x = false →
      (cosetGraph R).dist r x = 2 →
      ⁅Z R r, Q R x⁆ ≤ B R x (geometry.Z_normal x) →
      ¬ ⁅Z R r, Q R x⁆ ≤ fixedCore R x → ¬ HasNaturalSection R r x →
      ⁅⁅localZSpan R r x, Q R x⁆, Ltilde R x⁆ ≤ Z R x →
      ∀ p : CriticalPath R geometry x e,
      ∃ g ∈ stabilizer R x,
        ¬ Z R (act R g r) ≤ Q R (p.walk.getVert (p.walk.length - 2)) ∧
        ⁅⁅Z R (act R g r), Q R x⁆, Z R e⁆ ≠ ⊥) :
    2 < (Q R c).relIndex (V R w.predecessor) ∧
      2 < (Q R w.backward).relIndex (V R (fourBeforeEndpoint w)) := by
  refine ⟨predecessor_image_gt_two_of_no_small_involution common hb ha hd w hnat, ?_⟩
  obtain ⟨g₀, hg₀⟩ := exists_mVertex_of_color R hc
  obtain ⟨g₁, hg₁⟩ := exists_mVertex_of_color R (w.backward_color ha)
  let k := g₀⁻¹ * g₁
  have hk : act R k c = w.backward := by
    simp only [k, hg₀, hg₁, act_mVertex, mul_inv_cancel_left]
  let r := act R k a
  have hr : color R r = false := by rw [action_preserves_color]; exact ha
  have hdr : (cosetGraph R).dist r w.backward = 2 := by
    rw [← hk, dist_act]
    exact hd
  have hnr : ¬ ⁅Z R r, Q R w.backward⁆ ≤ fixedCore R w.backward := by
    rw [← hk, Z_act, Q_act, Escape.PairingControl.FirstPairing.fixedCore_act,
      ← map_commutator, map_le_map_iff_of_injective (MulAut.conj k⁻¹).injective]
    exact hn
  have hnoner : ¬ HasNaturalSection R r w.backward := by
    rw [← hk, hasNaturalSection_act_iff]
    exact hnone
  have hallr := all_fixed_at_any_center (by omega) hc hall (w.backward_color ha)
  have htr : ⁅⁅localZSpan R r w.backward, Q R w.backward⁆, Ltilde R w.backward⁆ ≤
      Z R w.backward :=
    (commutator_mono (commutator_mono (localZSpan_le_V R hdr.le) le_rfl) le_rfl).trans
      (radius_triple_le_Z_at_any_center (by omega) hc hall (w.backward_color ha))
  let p := w.shifted ha (by omega : 2 ≤ geometry.b R)
  obtain ⟨g, hg, hcrit, htriple⟩ := select r w.backward w.predecessor hr
    (w.backward_color ha) hdr (hallr r (by rwa [SimpleGraph.dist_comm])) hnr hnoner htr p
  have hfix : act R g w.backward = w.backward := hg
  have hdg : (cosetGraph R).dist (act R g r) w.backward = 2 := by
    rw [← hfix, dist_act]
    exact hdr
  obtain ⟨q, hq⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist
    (act R g r) w.backward
  let w' : BackwardWitness R geometry r w.backward := {
    endpoint := w.predecessor
    path := p
    backward := act R g r
    conjugator := g
    local_conjugator := hg
    conjugator_image := rfl
    backwardWalk := q
    backward_length := hq.trans hdg
    noncontainment := hcrit
    triple_ne := htriple }
  have hpred : w'.predecessor = fourBeforeEndpoint w := by
    change p.walk.getVert (p.walk.length - 2) = _
    have he : p.walk.length - 2 = w.path.walk.length - 4 + 2 := by
      rw [p.length_eq_b, w.path.length_eq_b]
      omega
    rw [he]
    exact w.shifted_overlap ha (by omega) (by omega)
  have hnat' : ¬ HasSmallRadiusInvolution w.backward :=
    fun hs => hnat (small_radius_involution_at_any_center (w.backward_color ha) hc hs)
  simpa only [hpred] using
    predecessor_image_gt_two_of_no_small_involution common hb hr hdr w' hnat'

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection.ImageBounds
