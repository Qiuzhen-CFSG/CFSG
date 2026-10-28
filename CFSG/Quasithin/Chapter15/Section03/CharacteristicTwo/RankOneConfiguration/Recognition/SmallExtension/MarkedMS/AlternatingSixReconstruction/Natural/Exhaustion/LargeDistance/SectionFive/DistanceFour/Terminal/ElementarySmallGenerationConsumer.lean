module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedEdges
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallKernel

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementaryCubeSelector

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementaryCubeSelector

/-!
# Generation in the elementary distance-four branch

For an incident cube, a subgroup with projected order greater than two admits
another incident cube which generates the full component stabilizer with both
the original cube and that subgroup.  The proof retains the first-edge marking
when applying the finite symmetric-group selector, then lifts generation through
the exact two-core kernel and transports it along the amalgam graph.

The final theorem applies this to the two distinct backward critical kernels in
the strict-forward, small-opposite branch.  It retains the actual backward shift,
its cubic and both endpoint seeds.  This is the generation step in MS93,
(5.12)(3), pp. 926–927, using the incident-edge argument of (5.6).

The `import all` dependencies are deliberate internal proof splits: the local
lifting and selector proofs unfold the existing marking and conjugator bodies.
Their public definitions remain unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

private theorem cube_nonline_neighbor_base
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (W : Subgroup (FreeAmalgam d.radical))
    (hW : W ≤ Q d.radical (p.walk.getVert 1))
    (hcard : 2 < (Q d.radical (alpha d.radical)).relIndex W) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical (alpha d.radical) ∧
      Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  obtain ⟨E,w,hEm,hEi,hEk⟩ := cube_first_edge_marking s u hfull p
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  have hAe : (Z d.radical z).comap (embedM d.radical) ≤ E := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hEm]
    apply (map_comap_le _ _).trans
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant z p.end_color]
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    have hp := replacementDistance_pos h d
    change p.walk.length-1 < replacementDistance h d
    omega
  have haE : a ∈ (D 6).map (MulAut.conj w).toMonoidHom := hEi ▸ map_mono hAe ha
  obtain ⟨k,b,_,_,_,hanchor,_,_,c,hcD,hkc⟩ :=
    CubePairedEdges.marked_edge_pair_with_cube w a haE hswap
  obtain ⟨g,hg⟩ := s.surjective (k*u⁻¹)
  let C := d.radical.map (MulAut.conj g).toMonoidHom
  let A := W.comap (embedM d.radical)
  have hC : C.map s.projection = (D 6).map (MulAut.conj k).toMonoidHom := by
    have he : s.projection.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (k*u⁻¹)).toMonoidHom.comp s.projection := by
      apply MonoidHom.ext
      intro v
      change s.projection (g*v*g⁻¹)=(k*u⁻¹)*s.projection v*(k*u⁻¹)⁻¹
      rw [map_mul,map_mul,map_inv,hg]
    change (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection = _
    rw [map_map,he,←map_map,hfull,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change (k*u⁻¹)*(u*v*u⁻¹)*(k*u⁻¹)⁻¹=k*v*k⁻¹
    group
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ C := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hAE : A ≤ E := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    exact ((map_comap_le _ _).trans hW).trans_eq hEm.symm
  have hAG : W ≤ (embedM d.radical).range := by
    rw [←hEm] at hW
    exact hW.trans (map_le_range _ _)
  have hAm : A.map (embedM d.radical) = W := map_comap_eq_self hAG
  have hAc : 2 < Nat.card (A.map s.projection) := by
    rw [←relIndex_ker,s.projection_kernel]
    have hh := relIndex_map_map_of_injective (pCore 2 d.overgroup) A (embedM_injective d.radical)
    rw [hAm,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at hh
    exact hh ▸ hcard
  have hgen : C ⊔ A = ⊤ := by
    apply elementary_cube_generation_lift_of_cube_eq s.projection s.surjective w c C A hker
    · exact hC.trans (by simpa only [elementaryDConjugator,CubePairedEdges.cubeGenerationConjugator] using hkc)
    · exact (map_mono hAE).trans_eq hEi
    · exact hcD.symm
    · exact hAc
  have hEC : E ⊔ C = ⊤ := by
    apply map_injective_of_ker_le s.projection (hEk.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hEi,hC,map_top_of_surjective s.projection s.surjective]
    exact hanchor
  let f := (embedM d.radical g)⁻¹
  let t := act d.radical f (beta d.radical)
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = C.map (embedM d.radical) := by
    rw [Q_act,Q_beta,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change f⁻¹*embedM d.radical v*(f⁻¹)⁻¹=embedM d.radical (g*v*g⁻¹)
    simp only [f,inv_inv,map_mul,map_inv]
  refine ⟨t,?_,?_,?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hEC
    rw [Subgroup.map_sup,hEm,←ht,←MonoidHom.range_eq_map] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rw [Subgroup.map_sup,hAm,←ht,←MonoidHom.range_eq_map] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm

/-- A subgroup of an incident cube with image order greater than two has a
compatible incident cube generating the full component stabilizer. -/
theorem cube_nonline_neighbor
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (W : Subgroup (FreeAmalgam d.radical))
    (hW : W ≤ Q d.radical (p.walk.getVert 1))
    (hcard : 2 < (Q d.radical a).relIndex W) :
    ∃ t, Adjacent d.radical a t ∧
      Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical a ∧
      Q d.radical t ⊔ W = stabilizer d.radical a := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  let f := (MulAut.conj j).toMonoidHom
  have hs' : (Q d.radical (act d.radical j⁻¹ z)).relIndex
      (Z d.radical (act d.radical j⁻¹ a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hsmall
  have hw' : W.map f ≤ Q d.radical ((p.act j⁻¹).walk.getVert 1) := by
    simp only [CriticalPath.act,actWalk_getVert,Q_act,inv_inv]
    exact map_mono hW
  have hc' : 2 < (Q d.radical (act d.radical j⁻¹ a)).relIndex (W.map f) := by
    rw [Q_act,inv_inv,relIndex_map_map_of_injective _ _ (MulAut.conj j).injective]
    exact hcard
  have base := cube_nonline_neighbor_base s hc u hfull (z := act d.radical j⁻¹ z)
  rw [←hbase] at base
  obtain ⟨t,hat,hfirst,hgen⟩ := base (p.act j⁻¹) hs' (W.map f) hw' hc'
  have hWW : (W.map f).map (MulAut.conj j⁻¹).toMonoidHom = W := by
    rw [map_map]
    have hid : (MulAut.conj j⁻¹).toMonoidHom.comp f = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro v
      change j⁻¹*(j*v*j⁻¹)*(j⁻¹)⁻¹=v
      group
    rw [hid,map_id]
  refine ⟨act d.radical j t,?_,?_,?_⟩
  · have hh := (adjacent_act_iff d.radical j _ _).mpr hat
    simpa only [hcancel] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj j⁻¹).toMonoidHom) hfirst
    simpa only [Subgroup.map_sup,←Q_act,←stabilizer_act,CriticalPath.act,
      actWalk_getVert,hcancel] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj j⁻¹).toMonoidHom) hgen
    simpa only [Subgroup.map_sup,←Q_act,←stabilizer_act,hWW,hcancel] using hh

include e hz hn in
/-- The actual paired backward critical kernels in the strict-forward,
small-opposite cube branch generate the selected stabilizer with a compatible
incident edge. The projected-order premise is discharged by their proven
distinctness, retaining the same cubic and both literal endpoint seeds. -/
theorem cube_strict_small_opposite_generation_knownSimple
    (hb : replacementDistance h d = 4)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hopposite : (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical z) ≤ 2) :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      q.cubic ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
      ∃ r : CriticalPath d.radical (replacementGeometry h d) q.start
          (act d.radical q.cubic (p.walk.getVert 2)),
        r.walk.getVert 1 = q.edge ∧ r.walk.getVert 2 = a ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≠
          Z d.radical q.start ⊓ Q d.radical (act d.radical q.cubic (p.walk.getVert 2)) ∧
        ∃ t, Adjacent d.radical q.start t ∧
          Q d.radical q.edge ⊔ Q d.radical t = stabilizer d.radical q.start ∧
          Q d.radical t ⊔ Z d.radical (p.walk.getVert 2) ⊔
            Z d.radical (act d.radical q.cubic (p.walk.getVert 2)) =
              stabilizer d.radical q.start := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨q,hq,hx,r,hr1,hr2,hne,hlarge⟩ :=
    cube_strict_small_opposite_distinct_kernels_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u him p hstrict hopposite
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨p',hp'⟩ : ∃ p' : CriticalPath d.radical (replacementGeometry h d) q.start
      (p.walk.getVert 2), p'.walk.getVert 1 = q.edge := by
    have hh : ∃ p' : CriticalPath d.radical (replacementGeometry h d) q.start
        (p.walk.getVert (p.walk.length-2)), p'.walk.getVert 1 = q.edge := ⟨q.path,q.first⟩
    have hl2 : p.walk.length - 2 = 2 := by omega
    rw [hl2] at hh
    exact hh
  have endpoint_le {w : Vertex d.radical}
      (v : CriticalPath d.radical (replacementGeometry h d) q.start w)
      (hv : v.walk.getVert 1 = q.edge) : Z d.radical w ≤ Q d.radical q.edge := by
    apply Z_le_Q_of_dist_lt d.radical w ((replacementGeometry h d).exists_critical w v.end_color)
    rw [←hv,SimpleGraph.dist_comm,v.dist_end,(replacementGeometry h d).distance_constant w v.end_color]
    have hh : v.walk.length = replacementDistance h d := v.length_eq_b
    change v.walk.length-1 < replacementDistance h d
    omega
  let W := Z d.radical (p.walk.getVert 2) ⊔
    Z d.radical (act d.radical q.cubic (p.walk.getVert 2))
  have hW : W ≤ Q d.radical (p'.walk.getVert 1) := by
    rw [hp']
    exact sup_le (endpoint_le p' hp') (endpoint_le r hr1)
  obtain ⟨t,ht,hfirst,hgen⟩ := cube_nonline_neighbor s hc u hfull p'
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p') W hW hlarge
  refine ⟨q,hq,hx,r,hr1,hr2,hne,t,ht,?_,?_⟩
  · simpa only [hp'] using hfirst
  · simpa only [W,sup_assoc] using hgen

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
