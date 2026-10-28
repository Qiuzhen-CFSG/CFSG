module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusChiefInput
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.SourcePaths

/-!
# Actual shifts at large nonbinary critical images

MS3 makes some neighboring seed join nonnormal in the original vertex
stabilizer. The replacement's actual simple component and critical endpoint
supply an escaping conjugate of that join. If the critical image has order
at least q², the proved radius-displacement bound forces the conjugated
seed outside the penultimate kernel. The native graph construction then
gives a backward critical path with every overlap vertex identified.
Reversing the same critical pair constructs its forward shift.

These paths are on the minimum characteristic replacement at the original
field degree. They do not assert the special Thompson-subgroup choices
in (5.5)--(5.6), or that the newly shifted pair again has a large image.
The root-image case is treated explicitly in `RootEscape`.
Source: Meierfrankenfeld--Stellmacher (1993), (2.1)(vii), (3.3),
and the displacement branch of (5.7), printed pp.856, 867, 919.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual characteristic replacement supplies the escaping neighboring
join, with its original edge and local conjugator retained. -/
theorem Input.replacement_exists_critical_neighbor_escape
    {geometry : Geometry d.radical} {a t z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 2 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) :
    ∃ u, Adjacent d.radical u t ∧
      ¬ stabilizer d.radical a ≤ normalizer
        ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ x ∈ stabilizer d.radical a,
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical u ⊔ Z d.radical a).map (MulAut.conj x⁻¹).toMonoidHom) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  have hstr := h.replacement_component_image_structure d
  let : ((pResidual 2 d.overgroup).map q).Normal := by
    rw [h.replacement_residual d]
    exact hstr.2.1
  let : IsSimpleGroup ((pResidual 2 d.overgroup).map q) := by
    rw [h.replacement_residual d]
    exact hstr.2.2.1
  let : IsQuasisimple ((pResidual 2 d.overgroup).map q) := by
    rw [h.replacement_residual d]
    exact hstr.2.2.2.1
  have hcent : centralizer ((pResidual 2 d.overgroup).map q : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [h.replacement_residual d]
    exact hstr.2.2.2.2
  have hne : Z d.radical a ≠ ⊥ := by
    intro he
    exact path.critical.2 (he ▸ bot_le)
  exact exists_critical_neighbor_join_escape
    (h.replacement_characteristic d) (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_residual_edge_generation d)
    q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hcent
    geometry hb (MSCentralOrbit.edgeCentralizerCondition d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)
      (h.replacement_omegaOrbit_centralizer d)) path.start_color hat hne path

/-- A large critical image constructs an actual backward critical path at
every nonbinary degree, preserving all overlapping vertices. -/
theorem Input.replacement_large_critical_backward_path
    {geometry : Geometry d.radical} {a t z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hlarge : Nat.card F ^ 2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ u x, Adjacent d.radical u t ∧ x ∈ stabilizer d.radical a ∧
      Adjacent d.radical a (act d.radical x t) ∧
      Adjacent d.radical (act d.radical x u) (act d.radical x t) ∧
      (∃ back : CriticalPath d.radical geometry (act d.radical x u)
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act d.radical x t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
      ¬ V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
  obtain ⟨u,hut,_,x,hx,hescape⟩ :=
    h.replacement_exists_critical_neighbor_escape d path (by omega) hat
  have hdisp := h.replacement_large_critical_radius_commutator d path hb hlarge
  have hxa : act d.radical x a = a := hx
  have hatx : Adjacent d.radical a (act d.radical x t) := by
    rw [←hxa]
    exact (adjacent_act_iff d.radical x _ _).mpr hat
  have hutx := (adjacent_act_iff d.radical x _ _).mpr hut
  have hnot : ¬ Z d.radical (act d.radical x u) ≤
      Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    intro hbad
    apply hescape
    rw [Subgroup.map_sup,←Z_act d.radical x u,←Z_act d.radical x a,hxa]
    have hzZ := (path.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized d.radical a)
    have hd : ⁅Z d.radical z,Z d.radical (act d.radical x u)⁆ ≤ Z d.radical a := by
      rw [commutator_comm]
      exact (commutator_mono (le_inf (le_sup_left.trans
        (neighbor_seed_join_le_radius hatx hutx)) hbad) le_rfl).trans hdisp
    apply le_normalizer_iff.mpr
    intro v hv y hy
    have hm : (Z d.radical (act d.radical x u) ⊔ Z d.radical a).map
        (MulAut.conj v).toMonoidHom ≤ Z d.radical (act d.radical x u) ⊔ Z d.radical a := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨w,hw,rfl⟩
        have hc := hd (commutator_mem_commutator hv hw)
        change v*w*v⁻¹ ∈ Z d.radical (act d.radical x u) ⊔ Z d.radical a
        rw [show v*w*v⁻¹ = ⁅v,w⁆*w by simp [commutatorElement_def,mul_assoc]]
        exact mul_mem (mem_sup_right hc) (mem_sup_left hw)
      · rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hzZ hv)]
        exact le_sup_right
    exact hm (mem_map_of_mem (MulAut.conj v).toMonoidHom hy)
  refine ⟨u,x,hut,hx,hatx,hutx,?_,?_⟩
  · exact exists_backward_path_of_not_le geometry (by omega) path hatx hutx hnot
  · exact fun hV => hnot ((le_sup_left.trans
      (neighbor_seed_join_le_radius hatx hutx)).trans hV)

/-- The large-image shift is a literal overlapping link in the existing
path iteration API. No source (5.5)/(5.6) selection is claimed. -/
theorem Input.replacement_large_critical_backward_link
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F ^ 2 ≤ (Q d.radical p.last).relIndex (Z d.radical p.first)) :
    ∃ q : CriticalSegment geometry,
      BackwardLink geometry (fun _ _ _ => True) p q := by
  have hlen : 1 ≤ p.path.walk.length := by rw [p.path.length_eq_b]; omega
  have hadj : Adjacent d.radical p.first (p.path.walk.getVert 1) := by
    have hh := p.path.walk.adj_getVert_succ (show 0 < p.path.walk.length by omega)
    simpa using (cosetGraph_adj d.radical _ _).mp hh
  obtain ⟨u,x,hut,hx,hatx,hutx,⟨back,hback,hover⟩,_⟩ :=
    h.replacement_large_critical_backward_path d p.path hb hadj hlarge
  refine ⟨⟨act d.radical x u,_,back⟩,⟨⟨_,trivial,hatx,hutx,hback⟩,?_,?_⟩⟩
  · simp only [p.path.length_eq_b]
  · intro i hi
    exact hover i (by rw [p.path.length_eq_b]; omega)

/-- Reversing the same critical pair constructs the genuine forward shift,
with the original two-edge overlap, at every nonbinary degree. -/
theorem Input.replacement_large_critical_forward_path
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F ^ 2 ≤ (Q d.radical p.last).relIndex (Z d.radical p.first)) :
    ∃ q : CriticalSegment geometry,
      q.first = p.path.walk.getVert 2 ∧
      (∀ i, i + 2 ≤ geometry.b d.radical →
        q.path.walk.getVert i = p.path.walk.getVert (i+2)) ∧
      (cosetGraph d.radical).dist q.last p.last = 2 := by
  have hC := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d)
    (h.replacement_omegaOrbit_centralizer d)
  let pr := p.reverse hC (by omega)
  have hrev := h.replacement_large_critical_reverse_index d p.path (by omega) hlarge
  obtain ⟨r,hr⟩ := h.replacement_large_critical_backward_link d pr hb hrev
  let q := r.reverse hC (by omega)
  have hfirst : q.first = p.path.walk.getVert 2 := by
    change r.last = p.path.walk.getVert 2
    rw [hr.last_eq]
    change p.path.walk.reverse.getVert (geometry.b d.radical - 2) = _
    rw [SimpleGraph.Walk.getVert_reverse,p.path.length_eq_b]
    congr 1
    omega
  refine ⟨q,hfirst,?_,?_⟩
  · intro i hi
    change r.path.walk.reverse.getVert i = p.path.walk.getVert (i+2)
    rw [SimpleGraph.Walk.getVert_reverse,r.path.length_eq_b]
    have ho := hr.overlap (geometry.b d.radical-i-2) (by omega)
    have hidx : geometry.b d.radical-i-2+2 = geometry.b d.radical-i := by omega
    rw [hidx] at ho
    rw [ho]
    change p.path.walk.reverse.getVert (geometry.b d.radical-i-2) = _
    rw [SimpleGraph.Walk.getVert_reverse,p.path.length_eq_b]
    congr 1
    omega
  · have ho := hr.overlap 0 (by omega)
    have ho' : r.path.walk.getVert 2 = p.last := by simpa [pr,CriticalSegment.reverse] using ho
    change (cosetGraph d.radical).dist r.first p.last = 2
    rw [←ho']
    exact r.path.dist_start (by rw [r.path.length_eq_b]; omega)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
