module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalSpanData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanWhole
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanDerived
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# Whole natural span and actual derived lifting in the unequal branch

The unequal source selector constructs both seed budgets on its second
critical path and retains the actual midpoint conjugator. These discharge
all numerical and orbit premises of whole-span recognition and the native
derived theorem. The same literal span and native residual commutator occur
in both conclusions. Its midpoint-kernel index is bounded internally by
the proved span-image theorem, so that intersection has the full derived group.

No field, quotient marking, natural action, seed budget, endpoint orbit,
or small-index derived-group premise is supplied to this consumer.
The fixed-radius and actual unequal-mover branch remain explicit.
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

/-- The actual unequal branch supplies a whole natural span, its native
derived bound and exact derived lifting through the midpoint kernel. -/
theorem Input.replacement_distance_four_unequal_root_span_whole
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hne : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2)) :
    ∃ g ∈ Ltilde d.radical u,
      let v := act d.radical g⁻¹ a
      let s := act d.radical g⁻¹ (back.walk.getVert 1)
      Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
      Ltilde d.radical u ≤
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2) ∧
      ∃ next : CriticalPath d.radical geometry v a,
        next.walk.getVert 1=s ∧ next.walk.getVert 2=u ∧
        (∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i) ∧
        distanceFourRootSpanWhole geometry v u a n ∧
        let W := localZSpan d.radical u v
        let P := ⁅W,Ltilde d.radical v⁆
        W=P ⊔ Z d.radical u ∧ ⁅W,W⁆=⁅P,P⁆ ∧
          Nat.card (⁅W,W⁆ : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F ∧
          ⁅P ⊓ Q d.radical u,P ⊓ Q d.radical u⁆=⁅W,W⁆ := by
  obtain ⟨g,hg,hus,hvs,hres,next,hfirst,hnextmid,hover,hbudget,hlast⟩ :=
    h.replacement_distance_four_unequal_root_span_data d path hb back hmid hfixed hne
  let v := act d.radical g⁻¹ a
  let W := localZSpan d.radical u v
  let P := ⁅W,Ltilde d.radical v⁆
  have hgv : act d.radical g v=a := by
    dsimp only [v]
    rw [←act_mul,inv_mul_cancel,act_one]
  have hfixed_v := radius_fixed_at d path.start_color next.start_color hfixed
  have hgmid : g ∈ stabilizer d.radical (next.walk.getVert 2) := by
    rw [hnextmid]
    exact Ltilde_le_stabilizer u hg
  have hi : (B d.radical v (geometry.Z_normal v)).relIndex
      (U d.radical (next.walk.getVert 2)) ≤ Nat.card F := by
    simpa only [hnextmid] using hbudget
  have hj : (B d.radical (next.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical a) ≤ Nat.card F := by simpa only [hnextmid] using hlast
  have hwhole := h.replacement_distance_four_root_span_whole d next hb g hgmid hgv
    hfixed_v hi hj
  have hderived := h.replacement_distance_four_root_span_derived d next hb g hgmid hgv
    hfixed_v hi hj
  have himage := h.replacement_distance_four_root_span_image d next hb hfixed_v hi
  rw [hnextmid] at hwhole hderived himage
  have hPW : P ≤ W := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer v).trans (localZSpan_normalized d.radical u v))
  have hWV : W ≤ V d.radical v := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,←hnextmid]
    exact (next.dist_start (by rw [next.length_eq_b,hb]; omega)).le)
  let := finite_stabilizer d.radical v
  let : Finite W := Finite.of_injective
    (inclusion (hWV.trans ((geometry.V_le_Q (by omega) v next.start_color).trans
      (fun _ hx => hx.1)))) (inclusion_injective _)
  have hindex : ((Q d.radical u).subgroupOf P).index ≤ Nat.card F :=
    ((Q d.radical u).relIndex_le_of_le_right hPW index_ne_zero_of_finite).trans himage
  exact ⟨g,hg,hus,hvs,hres,next,hfirst,hnextmid,hover,hwhole,
    hderived.1,hderived.2.1,hderived.2.2.1,hderived.2.2.2 (Q d.radical u) hindex⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
