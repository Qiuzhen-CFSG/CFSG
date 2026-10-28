module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedTwist
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexOrbit
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanEscape

/-!
# Both same-orbit spans have nonfixed derived groups

An actual midpoint-stabilizer conjugator puts the critical terminal seed
in the reciprocal full span. Criticality makes that span escape the starting
kernel. The crossed commutator bound in the fixed-radius branch then makes
the original full span escape the midpoint kernel as well.

If either derived group lay in the opposite fixed core, its commutator
with its generating seed would be residual-fixed. Rigidity of the original
natural cover makes that commutator trivial, forcing the forbidden kernel
containment. No seed budget, naturality of either full span, large critical
image, or identification of native movement with the full core is assumed.
Source: the final graph obstruction in MS93 (3.10)(i), printed pp.880--881.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem seed_containing_actor_le_kernel_of_fixed_derived
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {e : Vertex d.radical} (he : color d.radical e=false)
    (W : Subgroup (FreeAmalgam d.radical))
    (hWS : W ≤ stabilizer d.radical e) (hZW : Z d.radical e ≤ W)
    (hderived : ⁅W,W⁆ ≤ fixedCore d.radical e) :
    W ≤ Q d.radical e := by
  have hfixed : ⁅W,U d.radical e⁆ ≤
      centralizer (Ltilde d.radical e : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono le_rfl ((U_le_Z e).trans hZW)).trans hderived).trans inf_le_right
  have hzero : ⁅W,U d.radical e⁆=⊥ :=
    (h.replacement_natural_commutator_fixed_iff d geometry hb he W (U d.radical e)
      hWS le_rfl).mp hfixed
  have hZzero : ⁅W,Z d.radical e⁆=⊥ := by
    rw [commutator_comm,h.replacement_Z_commutator_eq_U d geometry hb he W hWS,
      commutator_comm,hzero]
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hZzero
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) e he
  intro x hx
  rw [←hC]
  exact ⟨hWS hx,hcentral hx⟩

/-- The actual critical endpoints lie in one midpoint-stabilizer orbit.
In the fixed-radius branch, both literal full spans escape the opposite
kernels, and both derived groups escape the opposite fixed cores. -/
theorem Input.replacement_distance_four_same_orbit_span_noncentrality
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let e := path.walk.getVert 2
    let W₁ := localZSpan d.radical e a
    let W₂ := localZSpan d.radical a e
    (¬ W₁ ≤ Q d.radical e) ∧ (¬ W₂ ≤ Q d.radical a) ∧
      (¬ ⁅W₁,W₁⁆ ≤ fixedCore d.radical e) ∧
      (¬ ⁅W₂,W₂⁆ ≤ fixedCore d.radical a) := by
  let e := path.walk.getVert 2
  let W₁ := localZSpan d.radical e a
  let W₂ := localZSpan d.radical a e
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hW₁V : W₁ ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,hd])
  have hW₁Q : W₁ ≤ Q d.radical a :=
    hW₁V.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hW₂Q : W₂ ≤ Q d.radical e := localZSpan_le_Q d.radical he hd.le (by omega)
  have hW₁S : W₁ ≤ stabilizer d.radical e :=
    hW₁Q.trans (Q_le_stabilizer_of_dist_two d.radical a e path.start_color hd)
  have hW₂S : W₂ ≤ stabilizer d.radical a :=
    hW₂Q.trans (Q_le_stabilizer_of_dist_two d.radical e a he (by
      rw [SimpleGraph.dist_comm,hd]))
  have hZzW : Z d.radical z ≤ W₂ := by
    rw [←hga]
    exact le_iSup (fun r : stabilizer d.radical e => Z d.radical (act d.radical r a)) ⟨g,hg⟩
  have hZzQ : ¬ Z d.radical z ≤ Q d.radical a :=
    (critical_reverse d.radical geometry
      (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
      a path.start_color (by
        have hpos : 0 < geometry.b d.radical := by omega
        exact lt_of_lt_of_eq hpos (geometry.distance_constant a path.start_color).symm)
      z path.end_color path.critical).2
  have hescape₂ : ¬ W₂ ≤ Q d.radical a := fun ht => hZzQ (hZzW.trans ht)
  have hescape₁ : ¬ W₁ ≤ Q d.radical e := by
    intro ht
    obtain ⟨_,_,_,_,hcross,_⟩ :=
      h.replacement_distance_four_normal_spans_of_radius_fixed d path hb hfixed
    change ⁅W₁ ⊓ Q d.radical e,W₂⁆ ≤ Z d.radical a at hcross
    rw [inf_eq_left.mpr ht] at hcross
    exact midpoint_span_not_le_B h d path hb4
      (actual_normal_radius_fixed h d hb4 path.start_color W₁ W₂ hW₁V
        (localZSpan_normalized d.radical e a) hW₂S hescape₂ hcross)
  exact ⟨hescape₁,hescape₂,
    fun hh => hescape₁ (seed_containing_actor_le_kernel_of_fixed_derived h d
      geometry hb4 he W₁ hW₁S (Z_le_localZSpan d.radical e a) hh),
    fun hh => hescape₂ (seed_containing_actor_le_kernel_of_fixed_derived h d
      geometry hb4 path.start_color W₂ hW₂S (Z_le_localZSpan d.radical a e) hh)⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
