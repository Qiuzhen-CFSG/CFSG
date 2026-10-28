module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusFixedTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusChief
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexPathSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport

/-!
# The actual large-image midpoint detects radius fixedness

The midpoint normal span is nontrivial modulo the full fixed preimage by
the actual moving-index theorem. Any actual large critical image gives the chief
fixed-or-covering alternative, so this span contains the whole moved radius.
Consequently fixed-core containment of the midpoint seed commutator implies
the same containment for the full radius, by RadiusFixedTransfer.

This proves the inference used in the nonfixed branch of MS93 (5.12)(2),
printed p.925. It does not assume a natural radius section, and it does not
exclude the nonfixed branch or distance four.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit h [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem large_path_at_base
    {geometry : Geometry d.radical} {c y : Vertex d.radical}
    (largePath : CriticalPath d.radical geometry c y)
    (hlarge : Nat.card F^2 ≤ (Q d.radical y).relIndex (Z d.radical c)) :
    ∃ y₀, ∃ _ : CriticalPath d.radical geometry (alpha d.radical) y₀,
      Nat.card F^2 ≤ (Q d.radical y₀).relIndex (Z d.radical (alpha d.radical)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical largePath.start_color
  have hbase : act d.radical g⁻¹ (mVertex d.radical g)=alpha d.radical := by
    rw [act_mVertex,mul_inv_cancel]
    rfl
  refine ⟨act d.radical g⁻¹ y,?_⟩
  rw [←hbase]
  refine ⟨largePath.act g⁻¹,?_⟩
  rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
  exact hlarge

private theorem base_moving_le_span
    {geometry : Geometry d.radical} {a z y : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (ha : a=alpha d.radical)
    (hb : geometry.b d.radical = 4)
    (largePath : CriticalPath d.radical geometry (alpha d.radical) y)
    (hlarge : Nat.card F^2 ≤ (Q d.radical y).relIndex (Z d.radical (alpha d.radical))) :
    Vcirc d.radical a ≤ localZSpan d.radical (path.walk.getVert 2) a := by
  subst a
  let a := alpha d.radical
  let e := path.walk.getVert 2
  let W := localZSpan d.radical e a
  let f := embedM d.radical
  let W₀ := W.comap f
  have hb2 : 2 < geometry.b d.radical := by omega
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have hd : (cosetGraph d.radical).dist e a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact path.dist_start (by omega)
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical hd.le
  have hWS : W ≤ stabilizer d.radical a := hWV.trans (geometry.V_local a rfl hb2)
  have hWr : W ≤ f.range := hWS.trans_eq (stabilizer_m_base d.radical)
  have hWm : W₀.map f = W := map_comap_eq_self hWr
  let : W₀.Normal := by
    refine ⟨?_⟩
    intro x hx g
    change f (g*x*g⁻¹) ∈ W
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp
      (localZSpan_normalized d.radical e a (by
        change f g ∈ stabilizer d.radical (mVertex d.radical 1)
        rw [stabilizer_m_base]
        exact ⟨g,rfl⟩)) (f x)).mp hx
  have hVm : (chiefRadius d).map f = V d.radical a :=
    map_comap_eq_self ((geometry.V_local a rfl hb2).trans_eq (stabilizer_m_base d.radical))
  have hZm : (chiefSeed d).map f = Z d.radical a :=
    map_comap_eq_self ((Z_le_stabilizer d.radical a).trans_eq (stabilizer_m_base d.radical))
  have hZW : Z d.radical a ≤ W := LocalCommutator.center_Z_le_span rfl hd
  have hnotB : ¬ W ≤ B d.radical a (geometry.Z_normal a) := by
    intro hh
    have hi := h.replacement_path_moving_index_ge_field d path hb4
    have hu : U d.radical e ≤ B d.radical a (geometry.Z_normal a) :=
      (DistanceEight.U_le_Z d.radical e).trans ((Z_le_localZSpan d.radical e a).trans hh)
    rw [relIndex_eq_one.mpr hu] at hi
    exact (not_le_of_gt (Finite.one_lt_card (α := F))) hi
  rcases h.replacement_critical_radius_residual_dichotomy d largePath hb4 hlarge W₀
    (comap_mono hWV) with hfix | hcover
  · have hh := map_mono (f := f) hfix
    rw [map_commutator,hWm,←Ltilde_alpha,hZm] at hh
    exact (hnotB (radius_le_B_of_commutator geometry hb2 rfl W hWV hh)).elim
  · have hh := map_mono (f := f) hcover
    rw [map_commutator,hVm,←Ltilde_alpha,Subgroup.map_sup,hWm,hZm,sup_eq_left.mpr hZW] at hh
    exact hh

/-- An actual large critical image anywhere in the same geometry makes the
prescribed midpoint span contain the whole moved radius. The two actual
paths are transported independently; no common orbit is assumed. -/
theorem Input.replacement_distance_four_moving_le_midpoint_span_of_large_path
    {geometry : Geometry d.radical} {a z c y : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical = 4)
    (largePath : CriticalPath d.radical geometry c y)
    (hlarge : Nat.card F^2 ≤ (Q d.radical y).relIndex (Z d.radical c)) :
    Vcirc d.radical a ≤ localZSpan d.radical (path.walk.getVert 2) a := by
  obtain ⟨y₀,largePath₀,hlarge₀⟩ := large_path_at_base d largePath hlarge
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical path.start_color
  have hbase : act d.radical g⁻¹ (mVertex d.radical g)=alpha d.radical := by
    rw [act_mVertex,mul_inv_cancel]
    rfl
  let p₀ := path.act g⁻¹
  have hh := base_moving_le_span h d p₀ hbase hb largePath₀ hlarge₀
  have hmid : p₀.walk.getVert 2=act d.radical g⁻¹ (path.walk.getVert 2) := by
    exact actWalk_getVert d.radical g⁻¹ path.walk 2
  rw [hmid,Vcirc_act,LocalCommutator.CriticalCase.localZSpan_act] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp hh

/-- In the presence of an actual large critical path, fixed-core containment
on the literal midpoint seed detects fixed-core containment for the full radius. -/
theorem Input.replacement_distance_four_midpoint_fixed_iff_radius_fixed_of_large_path
    {geometry : Geometry d.radical} {a z c y : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical = 4)
    (largePath : CriticalPath d.radical geometry c y)
    (hlarge : Nat.card F^2 ≤ (Q d.radical y).relIndex (Z d.radical c)) :
    ⁅Z d.radical (path.walk.getVert 2),Q d.radical a⁆ ≤ fixedCore d.radical a ↔
      ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a := by
  have hl := path.length_eq_b
  have hd : (cosetGraph d.radical).dist (path.walk.getVert 2) a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact path.dist_start (by omega)
  constructor
  · intro hseed
    have hspan := (LocalCommutator.span_commutator_le_fixed_iff
      (geometry := geometry) path.start_color hd.le (by omega)).mpr hseed
    apply h.replacement_radius_fixed_transfer d geometry (by omega) a path.start_color
      (Q d.radical a) le_rfl (Q_normal d.radical a)
    exact (commutator_mono
      (h.replacement_distance_four_moving_le_midpoint_span_of_large_path d path hb largePath hlarge)
      le_rfl).trans hspan
  · intro hfixed
    exact (commutator_mono
      ((Z_le_localZSpan d.radical (path.walk.getVert 2) a).trans
        (localZSpan_le_V d.radical hd.le)) le_rfl).trans hfixed

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
