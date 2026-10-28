module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EscapeComparison

/-!
# The literal critical-path inputs to the chief-factor argument

When the forward critical seed image has order at least q², the arbitrary
degree reciprocal comparison gives the same lower bound in reverse.
The escaping-actor comparison puts the commutator of the entire penultimate
radius kernel with the reverse seed in the full starting seed. The radius
image theorem supplies q³ as its index budget, including distance four.
All actors, kernels and central attachments remain the original ones.

These are the inputs used in `RadiusChief` to prove radius centrality.
Source: Meierfrankenfeld--Stellmacher (1993), (3.3) and (5.2)(i), p.914.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- At a large critical image, the whole penultimate radius kernel has
endpoint commutator in the full starting seed. -/
theorem Input.replacement_large_critical_radius_commutator
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F ^ 2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ⁅V d.radical a ⊓ Q d.radical (path.walk.getVert (path.walk.length-2)),
      Z d.radical z⁆ ≤ Z d.radical a := by
  let Y := V d.radical a ⊓ Q d.radical (path.walk.getVert (path.walk.length-2))
  have hYQ : Y ≤ Q d.radical a := inf_le_left.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hc : Y ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color)))).trans
      (centralizer_le (critical_commutator_le_start_seed path))
  have hbound : ⁅Z d.radical z,Y⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ := by
    by_contra hbad
    have hi := h.replacement_critical_index_lt_square_of_escape d path (by omega)
      Y (truncated_radius_le_endpoint_stabilizer path (by omega)) hc hbad
    omega
  rw [commutator_comm]
  exact hbound.trans (critical_commutator_le_start_seed path)

/-- Large critical images are large in both directions, at the original field degree. -/
theorem Input.replacement_large_critical_reverse_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (hlarge : Nat.card F ^ 2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    Nat.card F ^ 2 ≤ (Q d.radical a).relIndex (Z d.radical z) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry hedge a path.start_color
        (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
  by_contra! hsmall
  have he := (h.replacement_small_critical_indices_eq_field d rev hb hsmall).2
  have hq : 1 < Nat.card F := by
    rw [h.field_card]
    exact one_lt_pow₀ (by decide) (by have := h.nonbinary; omega)
  rw [he] at hlarge
  nlinarith

/-- The index budget on the same penultimate radius kernel is q³. -/
theorem Input.replacement_critical_radius_image_le_cube
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    (Q d.radical (path.walk.getVert (path.walk.length-2))).relIndex
      (V d.radical a) ≤ Nat.card F ^ 3 := by
  have hl := path.length_eq_b
  apply h.replacement_radius_image_le_cube d geometry hb path.start_color
  · apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even (geometry.b d.radical) := geometry.even (alpha d.radical) rfl
    rw [hl]
    rw [Nat.even_iff] at he ⊢
    omega
  · rw [path.dist_start (Nat.sub_le _ _),hl]
    omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
