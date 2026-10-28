module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSplitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Assembly

/-!
# Full local normal spans in the fixed-radius branch

At the literal midpoint e of a distance-four critical path starting at a,
take the full spans V1 = <Z_e^{G_a}> and V2 = <Z_a^{G_e}>. If [V_a,Q_a]
lies in the actual fixed core D_a, the full stabilizer normalizes [Z_e,Q_a]:
its residual component centralizes this subgroup and its kernel normalizes
it. Thus [V1,Q_a] = [Z_e,Q_a] lies in Z_e. Transport of the same radius
hypothesis to e proves the reciprocal equality and both intersection bounds.

All seeds, kernels, spans and fixed attachments remain the literal ones.
The fixed-core hypothesis is the preceding case in MS93 (5.12)(2), printed
pp.925--926. It is stronger than the established RadiusChief conclusion
[V_a,Q_a] <= C(V_a); this file does not eliminate its negation or construct
the later FF module and natural recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

omit [Finite H] in
private theorem radius_fixed_at {a e : Vertex d.radical}
    (ha : color d.radical a = false) (he : color d.radical e = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅V d.radical e,Q d.radical e⁆ ≤ fixedCore d.radical e := by
  obtain ⟨u,hu⟩ := exists_mVertex_of_color d.radical ha
  obtain ⟨w,hw⟩ := exists_mVertex_of_color d.radical he
  let g := u⁻¹*w
  have hg : act d.radical g a=e := by
    rw [hu,act_mVertex,mul_inv_cancel_left,←hw]
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfixed
  rwa [map_commutator,←V_act,←Q_act,←Escape.EdgeTransfer.fixedCore_act,hg] at hh

include h in
private theorem full_span_commutator
    {geometry : Geometry d.radical} (hb : 4 ≤ geometry.b d.radical)
    {a e : Vertex d.radical} (ha : color d.radical a = false)
    (hd : (cosetGraph d.radical).dist a e = 2)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅localZSpan d.radical e a,Q d.radical a⁆ = ⁅Z d.radical e,Q d.radical a⁆ ∧
      ⁅Z d.radical e,Q d.radical a⁆ ≤ Z d.radical e := by
  have hdist : (cosetGraph d.radical).dist e a ≤ 2 := by
    rw [SimpleGraph.dist_comm,hd]
  have hZV : Z d.radical e ≤ V d.radical a :=
    (Z_le_localZSpan d.radical e a).trans (localZSpan_le_V d.radical hdist)
  have hDC : ⁅Z d.radical e,Q d.radical a⁆ ≤
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono hZV le_rfl).trans hfixed).trans inf_le_right
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha
  have hS : Ltilde d.radical a ⊔ Q d.radical a = stabilizer d.radical a := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hND : stabilizer d.radical a ≤ normalizer
      ((⁅Z d.radical e,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rw [←hS]
    exact sup_le ((le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _))
      (normalizer_commutator_ge_right _ _)
  have hspan : ⁅localZSpan d.radical e a,Q d.radical a⁆ ≤
      ⁅Z d.radical e,Q d.radical a⁆ := by
    rw [LocalCommutator.span_commutator_eq_conjugates (geometry := geometry) ha hdist (by omega)]
    apply iSup_le
    intro g
    exact (mem_normalizer_iff_map_conj_eq.mp
      (hND ((stabilizer d.radical a).inv_mem g.property))).le
  refine ⟨le_antisymm hspan (commutator_mono (Z_le_localZSpan d.radical e a) le_rfl),?_⟩
  exact le_normalizer_iff_commutator_le_left.mp
    ((Q_le_stabilizer_of_dist_two d.radical a e ha hd).trans
      (Z_normalized d.radical e))

include h in
/-- In the literal fixed-radius branch of MS93 (5.12)(2), the two full
midpoint normal spans have their seed commutators and reciprocal intersection
bounds. The single starting fixed-core premise supplies both directions. -/
theorem Input.replacement_distance_four_normal_spans_of_radius_fixed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical = 4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let e := path.walk.getVert 2
    let V1 := localZSpan d.radical e a
    let V2 := localZSpan d.radical a e
    ⁅V1,Q d.radical a⁆ = ⁅Z d.radical e,Q d.radical a⁆ ∧
      ⁅Z d.radical e,Q d.radical a⁆ ≤ Z d.radical e ∧
      ⁅V2,Q d.radical e⁆ = ⁅Z d.radical a,Q d.radical e⁆ ∧
      ⁅Z d.radical a,Q d.radical e⁆ ≤ Z d.radical a ∧
      ⁅V1 ⊓ Q d.radical e,V2⁆ ≤ Z d.radical a ∧
      ⁅V2 ⊓ Q d.radical a,V1⁆ ≤ Z d.radical e := by
  let e := path.walk.getVert 2
  have hl := path.length_eq_b
  have he : color d.radical e = false := (path.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a e = 2 := path.dist_start (by omega)
  have hfixed_e := radius_fixed_at d path.start_color he hfixed
  obtain ⟨h1,h1Z⟩ := full_span_commutator h d (by omega : 4 ≤ geometry.b d.radical)
    path.start_color hd hfixed
  obtain ⟨h2,h2Z⟩ := full_span_commutator h d (by omega : 4 ≤ geometry.b d.radical)
    he (by rw [SimpleGraph.dist_comm]; exact hd) hfixed_e
  refine ⟨h1,h1Z,h2,h2Z,?_,?_⟩
  · calc
      ⁅localZSpan d.radical e a ⊓ Q d.radical e,localZSpan d.radical a e⁆ ≤
          ⁅Q d.radical e,localZSpan d.radical a e⁆ := commutator_mono inf_le_right le_rfl
      _ = ⁅localZSpan d.radical a e,Q d.radical e⁆ := commutator_comm _ _
      _ ≤ Z d.radical a := h2.le.trans h2Z
  · calc
      ⁅localZSpan d.radical a e ⊓ Q d.radical a,localZSpan d.radical e a⁆ ≤
          ⁅Q d.radical a,localZSpan d.radical e a⁆ := commutator_mono inf_le_right le_rfl
      _ = ⁅localZSpan d.radical e a,Q d.radical a⁆ := commutator_comm _ _
      _ ≤ Z d.radical e := h1.le.trans h1Z

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
