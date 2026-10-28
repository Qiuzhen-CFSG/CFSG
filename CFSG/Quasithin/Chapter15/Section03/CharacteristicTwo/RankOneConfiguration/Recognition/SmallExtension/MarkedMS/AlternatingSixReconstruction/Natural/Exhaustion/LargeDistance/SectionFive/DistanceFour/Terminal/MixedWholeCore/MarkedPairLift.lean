module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedPair
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.CubeFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.CentralGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEndpoint

/-!
# The marked mixed paired conjugator on the actual graph

The same paired conjugator now normalizes the entire original first-edge
seed. Its quotient normalizes the enclosing three-pair cube; equality of
mixed-plane and cube fixed spaces and forced central generation transport
that condition to the full edge omega center.

Both generation identities and all central attachments are retained.
Source: MS93 (5.12)(3), printed pp.926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
open MixedEndpoint
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

theorem strict_marked_paired_generation_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hcross : Q d.radical t ⊔ Q d.radical (p.walk.getVert 1) =
      stabilizer d.radical (alpha d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ x ∈ stabilizer d.radical (alpha d.radical),
      Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical (alpha d.radical) ∧
      Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
        stabilizer d.radical (alpha d.radical) ∧
      x ∈ normalizer (Z d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) := by
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  have hsplit := strict_original_omega_centrally_generated_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u him p hstrict
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have him' : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨E,v,hEm,hEk,hEi⟩ := edge_preimage s u him' hat
  obtain ⟨F,w,hFm,hFk,hFi⟩ := edge_preimage s u him' hfirst
  have hFE : E ⊔ F = ⊤ := by
    apply map_injective (embedM_injective d.radical)
    rw [Subgroup.map_sup,hEm,hFm,←MonoidHom.range_eq_map]
    exact hcross.trans (stabilizer_m_base d.radical)
  have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range := stabilizer_m_base d.radical
  let A := (Z d.radical a').comap (embedM d.radical)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  obtain ⟨a,ha,hAi⟩ := small_critical_image_eq_swap s hc p hsmall
  change A.map s.projection = zpowers a at hAi
  have hAF : A ≤ F := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hAm,hFm]
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    change 4-1 < replacementDistance h d
    omega
  have haF : a ∈ plus.map (MulAut.conj w).toMonoidHom := by
    rw [←hFi]
    exact map_mono hAF (hAi ▸ mem_zpowers a)
  have hcross' : plus.map (MulAut.conj v).toMonoidHom ⊔
      plus.map (MulAut.conj w).toMonoidHom = ⊤ := by
    have hh := congrArg (Subgroup.map s.projection) hFE
    simpa only [Subgroup.map_sup,hEi,hFi,map_top_of_surjective _ s.surjective] using hh
  obtain ⟨k,hpair,hend,hkn⟩ := mixed_marked_pair v w a ha haF hcross'
  obtain ⟨g,hgk⟩ := s.surjective k
  have hmap (C : Subgroup d.overgroup) (j : d.overgroup) :
      (C.map (MulAut.conj j).toMonoidHom).map s.projection =
        (C.map s.projection).map (MulAut.conj (s.projection j)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change s.projection (j*z*j⁻¹) = s.projection j*s.projection z*(s.projection j)⁻¹
    simp only [map_mul,map_inv]
  have hpair' : E ⊔ E.map (MulAut.conj g).toMonoidHom = ⊤ := by
    apply map_injective_of_ker_le s.projection (hEk.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hmap,hEi,hgk,map_top_of_surjective _ s.surjective]
    exact hpair
  have hend' : E ⊔ A ⊔ A.map (MulAut.conj g⁻¹).toMonoidHom = ⊤ := by
    apply map_injective_of_ker_le s.projection (hEk.trans (le_sup_left.trans le_sup_left)) le_top
    rw [Subgroup.map_sup,Subgroup.map_sup,hmap,hEi,hAi,map_inv,hgk,
      MonoidHom.map_zpowers,map_top_of_surjective _ s.surjective]
    exact hend
  have hmap' (C : Subgroup d.overgroup) (j : d.overgroup) :
      (C.map (MulAut.conj j).toMonoidHom).map (embedM d.radical) =
        (C.map (embedM d.radical)).map (MulAut.conj (embedM d.radical j)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change embedM d.radical (j*z*j⁻¹) =
      embedM d.radical j*embedM d.radical z*(embedM d.radical j)⁻¹
    simp only [map_mul,map_inv]
  refine ⟨embedM d.radical g,?_,?_,?_,?_⟩
  · rw [hbase]
    exact ⟨g,rfl⟩
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hpair'
    rw [Subgroup.map_sup,hmap',hEm,←MonoidHom.range_eq_map,←hbase] at hh
    simpa only [Q_act,inv_inv] using hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hend'
    rw [Subgroup.map_sup,Subgroup.map_sup,hmap',hEm,hAm,←MonoidHom.range_eq_map,
      ←hbase,map_inv] at hh
    simpa only [Z_act] using hh

  · have hgn := cube_normalizer_preserves_edge_omega s hsplit F
      (s.projection_kernel ▸ hFk) w hFi g (by rwa [hgk])
    have hn := le_normalizer_map (embedM d.radical) (mem_map_of_mem _ hgn)
    have hseed : (omegaCenter F).map (embedM d.radical) = Z d.radical (p.walk.getVert 1) := by
      have ht : color d.radical (p.walk.getVert 1) = true := by
        have hh := adjacent_color_ne d.radical hfirst
        change false ≠ color d.radical (p.walk.getVert 1) at hh
        exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
      rw [←omegaCenter_map _ _ (embedM_injective d.radical),hFm,Z,if_neg (by simp [ht])]
      rfl
    rwa [hseed] at hn

/-- The actual strict alpha-based mixed path admits one marked paired
conjugator, retaining the backward shift, kernel containment and full seed
intersection normalization required by the source. -/
theorem strict_selected_marked_pair_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) =
          stabilizer d.radical (alpha d.radical) ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical (alpha d.radical) ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
          Q d.radical (act d.radical x (p.walk.getVert 2)) ∧
        x ∈ normalizer ((Z d.radical (alpha d.radical) ⊓
          Z d.radical (p.walk.getVert 2) : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  obtain ⟨q⟩ := mixed_strict_backward_shift_knownSimple hb u him p hstrict
  obtain ⟨x,hx,hpair,hend,hnorm⟩ := strict_marked_paired_generation_knownSimple
    hb u him p q.adjacent_start q.generation hstrict
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hkernel := mixed_backward_kernel_le_every_conjugate_knownSimple hb u him p q x hx
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hmid : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have him' : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hinter := mixed_strict_seed_intersection_eq_edge s (by omega) u him'
    p.start_color hfirst hmid hstrict
  refine ⟨q,x,hx,hpair,hend,by simpa only [hl] using hkernel,?_⟩
  rwa [hinter]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
