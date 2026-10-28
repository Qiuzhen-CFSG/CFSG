module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanImage
public import Theory.GroupTheory.CommutatorPreimage
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# The original prescribed root pair fixes the full span kernel modulo Z

Let back run from v through a to e and retain the original r in G_a
carrying e to v. For W = <Z_a^{G_v}>, the full-span commutator identity
puts [W intersect Q_a,Z_e intersect Q_v] in Z_a. Fixed radius at a and v
makes this subgroup central in both stabilizers. The same r transfers
centrality from v to e, and full-seed natural-cover vanishing kills it.
The critical fixed-intersection theorem then gives [W intersect Q_a,Z_e]
<= Z_v, including the whole endpoint attachment.

The original companion path and k inverse times r prove the same bound
for Z_(k e). The actual B_v(U_a) budget bounds their joined fixed-preimage
index by q. No terminal budget at a, span naturality, or Q0 identity enters.
Source: the commutator and fixed-index step of MS93 (5.12)(3), printed p.927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem prescribed_inner_stabilizer
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha
  rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
    h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]

/-- The original midpoint orbit makes the whole span kernel commute with
the full critical root intersection, hence fixes its endpoint modulo Z_v. -/
theorem Input.replacement_distance_four_prescribed_span_endpoint_fixed
    {geometry : Geometry d.radical} {a e v : Vertex d.radical}
    (back : CriticalPath d.radical geometry v e) (hb : geometry.b d.radical=4)
    (hmid : back.walk.getVert 2=a)
    (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hre : act d.radical r e=v)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let C := localZSpan d.radical a v ⊓ Q d.radical a
    ⁅C,Z d.radical e ⊓ Q d.radical v⁆=⊥ ∧ ⁅C,Z d.radical e⁆ ≤ Z d.radical v := by
  let W := localZSpan d.radical a v
  let C := W ⊓ Q d.radical a
  let A := Z d.radical e ⊓ Q d.radical v
  let D := ⁅C,A⁆
  have hl := back.length_eq_b
  have ha : color d.radical a=false := by
    rw [←hmid]
    exact (back.vertex_color (by omega)).mpr (by decide)
  have hva : (cosetGraph d.radical).dist v a=2 := by
    rw [←hmid]
    exact back.dist_start (by omega)
  have hae : (cosetGraph d.radical).dist a e=2 := by
    rw [←hmid,back.dist_end,back.length_eq_b,hb]
  have hWV : W ≤ V d.radical v := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,hva])
  have hWQ : W ≤ Q d.radical v :=
    hWV.trans (geometry.V_le_Q (by omega) v back.start_color)
  have hAV : A ≤ V d.radical a := inf_le_left.trans
    (le_iSup_of_le e (le_iSup_of_le (by rw [SimpleGraph.dist_comm,hae] :
      (cosetGraph d.radical).dist e a ≤ 2) le_rfl))
  have hCSe : C ≤ stabilizer d.radical e := inf_le_right.trans
    (Q_le_stabilizer_of_dist_two d.radical a e ha hae)
  have hfixedv := radius_fixed_at d ha back.start_color hfixed
  have hWcomm := full_span_commutator h d (by omega : 4 ≤ geometry.b d.radical)
    back.start_color hva hfixedv
  have hDZa : D ≤ Z d.radical a :=
    (commutator_mono inf_le_left inf_le_right).trans (hWcomm.1.le.trans hWcomm.2)
  have hDLa : D ≤ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    change ⁅C,A⁆ ≤ _
    rw [commutator_comm]
    exact ((commutator_mono hAV inf_le_right).trans hfixed).trans inf_le_right
  have hDSa : D ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←prescribed_inner_stabilizer h d geometry (by omega) ha]
    exact sup_le (le_centralizer_iff.mp hDLa)
      (le_centralizer_iff.mp (hDZa.trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a ha))))
  have hDLv : D ≤ centralizer (Ltilde d.radical v : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono (inf_le_left.trans hWV) inf_le_right).trans hfixedv).trans inf_le_right
  have hDSv : D ≤ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←prescribed_inner_stabilizer h d geometry (by omega) back.start_color]
    exact sup_le (le_centralizer_iff.mp hDLv)
      (le_centralizer_iff.mp (hDSa.trans (centralizer_le
        (Q_le_stabilizer_of_dist_two d.radical v a back.start_color hva))))
  have hDr : D.map (MulAut.conj r).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hDSa hr))
  have hrinv : act d.radical r⁻¹ v=e := by
    rw [←hre,←act_mul,mul_inv_cancel,act_one]
  have hDSe : D ≤ centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj r).toMonoidHom) hDSv).trans
      (map_centralizer_le_centralizer_image _ _)
    change D.map (MulAut.conj r).toMonoidHom ≤ centralizer
      ((stabilizer d.radical v).map (MulAut.conj r).toMonoidHom : Set _) at hh
    have hSmap : stabilizer d.radical (act d.radical r⁻¹ v)=
        (stabilizer d.radical v).map (MulAut.conj r).toMonoidHom := by
      simpa only [inv_inv] using stabilizer_act d.radical r⁻¹ v
    rw [hDr,←hSmap,hrinv] at hh
    exact hh
  have hzero : ⁅C,A⁆=⊥ :=
    (full_seed_commutator_fixed_iff h d geometry (by omega) back.end_color C A
      hCSe inf_le_left).mp (hDSe.trans (centralizer_le (Ltilde_le_stabilizer e)))
  refine ⟨hzero,?_⟩
  rw [commutator_comm]
  exact (h.replacement_critical_fixed_intersection_displacement d back (by omega)
    C hCSe (inf_le_left.trans hWQ) (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (critical_commutator_le_start_seed back)

/-- Both unchanged full endpoints have joined fixed-preimage index at most
q on the original midpoint span, using its actual seed budget at v. -/
theorem Input.replacement_distance_four_prescribed_span_pair_fixed_index
    {geometry : Geometry d.radical} {a e v : Vertex d.radical}
    (back : CriticalPath d.radical geometry v e) (hb : geometry.b d.radical=4)
    (hmid : back.walk.getVert 2=a)
    (r k : FreeAmalgam d.radical)
    (hr : r ∈ stabilizer d.radical a) (hk : k ∈ stabilizer d.radical a)
    (hre : act d.radical r e=v)
    (companion : CriticalPath d.radical geometry v (act d.radical k e))
    (hcmid : companion.walk.getVert 2=a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hbudget : (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical a) ≤ Nat.card F) :
    let W := localZSpan d.radical a v
    ⁅W ⊓ Q d.radical a,Z d.radical e⁆ ≤ Z d.radical v ∧
      ⁅W ⊓ Q d.radical a,Z d.radical (act d.radical k e)⁆ ≤ Z d.radical v ∧
      (commutatorPreimage W (Z d.radical e ⊔ Z d.radical (act d.radical k e))
        (Z d.radical v)).relIndex W ≤ Nat.card F := by
  let W := localZSpan d.radical a v
  let C := W ⊓ Q d.radical a
  have h₁ := (h.replacement_distance_four_prescribed_span_endpoint_fixed d back hb
    hmid r hr hre hfixed).2
  have hkr : act d.radical (k⁻¹*r) (act d.radical k e)=v := by
    rw [←act_mul,mul_inv_cancel_left]
    exact hre
  have h₂ := (h.replacement_distance_four_prescribed_span_endpoint_fixed d companion hb
    hcmid (k⁻¹*r) ((stabilizer d.radical a).mul_mem
      ((stabilizer d.radical a).inv_mem hk) hr) hkr hfixed).2
  refine ⟨h₁,h₂,?_⟩
  have hjoin : ⁅C,Z d.radical e ⊔ Z d.radical (act d.radical k e)⁆ ≤ Z d.radical v := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (stabilizer d.radical v)
      (Z d.radical e) (Z d.radical (act d.radical k e)) C (Z d.radical v)
      (Z_normalized d.radical v)
      (back.endpoint_Z_le_start_stabilizer (by omega))
      (companion.endpoint_Z_le_start_stabilizer (by omega))
      (by rw [commutator_comm]; exact h₁) (by rw [commutator_comm]; exact h₂)
  have hpre : C ≤ commutatorPreimage W
      (Z d.radical e ⊔ Z d.radical (act d.radical k e)) (Z d.radical v) :=
    le_commutatorPreimage inf_le_left hjoin
  have hl := back.length_eq_b
  have ha : color d.radical a=false := by
    rw [←hmid]
    exact (back.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a v=2 := by
    rw [←hmid,SimpleGraph.dist_comm]
    exact back.dist_start (by omega)
  have hWS : W ≤ stabilizer d.radical v := (localZSpan_le_V d.radical hd.le).trans
    ((geometry.V_le_Q (by omega) v back.start_color).trans (fun _ hx => hx.1))
  let := finite_stabilizer d.radical v
  let : Finite W := Finite.of_injective (inclusion hWS) (inclusion_injective _)
  have hi := relIndex_le_of_le_left hpre (L := W) index_ne_zero_of_finite
  rw [show C=W ⊓ Q d.radical a from rfl,inf_relIndex_left] at hi
  have himage := h.replacement_distance_four_root_span_image d back hb
    (radius_fixed_at d ha back.start_color hfixed) (by simpa only [hmid] using hbudget)
  rw [hmid] at himage
  exact hi.trans himage

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
