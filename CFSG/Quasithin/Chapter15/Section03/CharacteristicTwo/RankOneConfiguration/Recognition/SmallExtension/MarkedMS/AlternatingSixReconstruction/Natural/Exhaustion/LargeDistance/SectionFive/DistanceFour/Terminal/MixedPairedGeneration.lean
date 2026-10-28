module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.LargeImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSmallSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEndpoint
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEndpoint

/-!
# Paired mixed-plane generation at distance four

A small critical endpoint is a transposition in the marked symmetric quotient.
The finite mixed-plane pairing therefore supplies one conjugator for both the
edge-pair and two-endpoint generation identities at distance four. Both full
endpoint seeds, the original quotient and every central attachment are retained.
The original Sylow witness supplies the relative-normalizer generating edge.

Source: MS93 (5.6), (5.12)(1),(3), printed pp.917--918,924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
open MixedEndpoint
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- A selected relative-normalizer edge admits one actual conjugator for
both source generation requirements: the two full edge kernels, and the
edge kernel together with the two endpoint seeds. -/
private theorem mixed_small_paired_generation_base
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical)) :
    ∃ x ∈ stabilizer d.radical (alpha d.radical),
      Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical (alpha d.radical) ∧
      Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
        stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have him' : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨E,v,hEm,hEk,hEi⟩ := edge_preimage s u him' hat
  have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range := stabilizer_m_base d.radical
  let A := (Z d.radical a').comap (embedM d.radical)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  obtain ⟨a,ha,hAi⟩ := small_critical_image_eq_swap s hc p hsmall
  change A.map s.projection = zpowers a at hAi
  have hNg : normalizer (E : Set d.overgroup) ⊔ A = ⊤ := by
    apply map_injective (embedM_injective d.radical)
    rw [Subgroup.map_sup,SylowNormalizer.normalizer_embed,hEm,hAm,←MonoidHom.range_eq_map,
      ←hbase]
    exact hgen
  have hNi : normalizer (plus.map (MulAut.conj v).toMonoidHom : Set S) ⊔ zpowers a = ⊤ := by
    apply top_unique
    have hh := congrArg (Subgroup.map s.projection) hNg
    rw [Subgroup.map_sup,hAi,map_top_of_surjective _ s.surjective] at hh
    rw [←hh,←hEi]
    exact sup_le_sup (le_normalizer_map s.projection) le_rfl
  obtain ⟨k,hpair,hend⟩ := mixed_simultaneous_pair v a ha hNi
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
  refine ⟨embedM d.radical g,?_,?_,?_⟩
  · rw [hbase]
    exact ⟨g,rfl⟩
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hpair'
    rw [Subgroup.map_sup,hmap',hEm,←MonoidHom.range_eq_map,←hbase] at hh
    simpa only [Q_act,inv_inv] using hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hend'
    rw [Subgroup.map_sup,Subgroup.map_sup,hmap',hEm,hAm,←MonoidHom.range_eq_map,
      ←hbase,map_inv] at hh
    simpa only [Z_act] using hh


include e hz hn in
/-- One actual conjugator supplies both generation identities at the selected
relative-normalizer edge of a distance-four critical path. -/
theorem mixed_four_paired_endpoint_generation_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical)) :
    ∃ x ∈ stabilizer d.radical (alpha d.radical),
      Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical (alpha d.radical) ∧
      Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
        stabilizer d.radical (alpha d.radical) :=
  mixed_small_paired_generation_base (by omega) u him p
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p) hat hgen

include e hz hn in
/-- The original mixed radical supplies the generating edge and both paired
endpoint identities on its literal critical path. -/
theorem mixed_four_exists_paired_generation_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
          stabilizer d.radical (alpha d.radical) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨P,hP⟩ := large_distance_mixed_original_sylow_knownSimple hb2 u him
  obtain ⟨t,hat,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 P hP p
  exact ⟨t,hat,hgen,mixed_four_paired_endpoint_generation_knownSimple hb u him p hat hgen⟩

include e hz hn in
/-- Paired generation at any component vertex, transported with one literal
conjugator for both edge and endpoint identities. -/
theorem mixed_four_paired_endpoint_generation_at_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hat : Adjacent d.radical a t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a) ⊔ Z d.radical z = stabilizer d.radical a) :
    ∃ x ∈ stabilizer d.radical a,
      Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical a ∧
      Q d.radical t ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
        stabilizer d.radical a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hrestore (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have he : act d.radical g (alpha d.radical) = a := by rw [←hbase,hrestore]
  have q := p.act g⁻¹
  rw [hbase] at q
  have hat0 : Adjacent d.radical (alpha d.radical) (act d.radical g⁻¹ t) := by
    simpa only [hbase] using (adjacent_act_iff d.radical g⁻¹ a t).mpr hat
  have hgen0 : (normalizer (Q d.radical (act d.radical g⁻¹ t) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical (act d.radical g⁻¹ z) =
        stabilizer d.radical (alpha d.radical) := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hgen
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective] at hh
    simpa only [←hbase,Q_act,stabilizer_act,Z_act,inv_inv] using hh
  obtain ⟨x,hx,hpair,hend⟩ :=
    mixed_four_paired_endpoint_generation_knownSimple hb u him q hat0 hgen0
  let y := g⁻¹*x*g
  have hy : y ∈ stabilizer d.radical a := by
    change act d.radical y a = a
    have hxf : act d.radical x (alpha d.radical) = alpha d.radical := hx
    dsimp only [y]
    rw [act_mul,act_mul,hbase,hxf,he]
  have hback (v : Vertex d.radical) :
      act d.radical g (act d.radical x⁻¹ (act d.radical g⁻¹ v)) =
        act d.radical y⁻¹ v := by
    rw [←act_mul,←act_mul]
    congr 1
    dsimp only [y]
    group
  have hfwd (v : Vertex d.radical) :
      act d.radical g (act d.radical x (act d.radical g⁻¹ v)) =
        act d.radical y v := by
    simp only [←act_mul,y,mul_assoc]
  refine ⟨y,hy,?_,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hpair
    rw [Subgroup.map_sup,←Q_act,←Q_act,←stabilizer_act,hrestore,he,hback] at hh
    exact hh
  · have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hend
    rw [Subgroup.map_sup,Subgroup.map_sup,←Q_act,←Z_act,←Z_act,←stabilizer_act,
      hrestore,hrestore,he,hfwd] at hh
    exact hh

include e hz hn in
/-- Every original mixed critical path at distance four has a paired
edge/endpoint generating configuration, with all earlier premises discharged. -/
theorem mixed_four_exists_paired_generation_at_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    ∃ t, Adjacent d.radical a t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a) ⊔ Z d.radical z = stabilizer d.radical a ∧
      ∃ x ∈ stabilizer d.radical a,
        Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical a ∧
        Q d.radical t ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical a := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨P,hP⟩ := large_distance_mixed_original_sylow_knownSimple hb2 u him
  obtain ⟨t,hat,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 P hP p
  exact ⟨t,hat,hgen,mixed_four_paired_endpoint_generation_at_knownSimple hb u him p hat hgen⟩

include e hz hn in
/-- Apply the paired generation to the literal selected backward edge. The
same shift retains its strict slice, both original transporters and agreement;
the two endpoint actors are not identified with each other. -/
theorem mixed_strict_backward_paired_generation_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      ∃ x ∈ stabilizer d.radical a,
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) = stabilizer d.radical a ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical a := by
  obtain ⟨q⟩ := mixed_strict_backward_shift_at_knownSimple hb u him p hstrict
  refine ⟨q,by rwa [q.index_eq],?_⟩
  exact mixed_four_paired_endpoint_generation_at_knownSimple hb u him p
    q.adjacent_start q.relative_generation

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
