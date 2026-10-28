module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowLarge
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedStrict

/-!
# Large critical images for all original Sylow replacements

The actual original Sylow subgroup restricts to a Sylow subgroup of the
replacement overgroup and normalizes the replacement radical. Its symmetric
image contains a conjugate point core. The restricted even endpoint actor
therefore generates the starting stabilizer with a relative edge normalizer,
including when the replacement is properly contained in that Sylow subgroup.

If every conjugate of an eligible neighboring seed under this relative
normalizer lay in the predecessor core, its orbit span would have commutator
with the controlled actor inside the starting seed. Generation makes the
span, joined with that seed, locally normal; the existing action lemma then
puts it in the Baumann slice, contradicting eligibility. An escaping orbit
element is realized in the edge holomorph. The resulting backward critical
path retains both geometric actors, the original normalizer actor, pointwise
agreement on the whole edge kernel, every overlapping vertex and the exact
slice index. Conjugation transports all this data to every original vertex.

Above distance four the proved mixed-plane exclusion supplies the original
Sylow hypothesis. Thus the backward paths, whole-radius escape and forward
extensions now cover every large critical image, with no premise on the
replacement image order. Both moved-cover orders and all central attachments
are retained. Small critical images, the terminal original-Sylow exclusion
and the remaining distance-four estimates still belong to the final assembly;
this module does not prove LargeDistanceInput.

The two `import all` dependencies reuse the internal quotient-generation and
normalized-radius lemmas without changing their public boundaries.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), relative normalizers on printed p.881, (5.2), (5.5)--(5.8), and Section 7,
printed pp.914--920 and 932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)

private theorem generating_neighbor_of_even_actor
    (s : FullSymmetricAction h e hz hn d)
    (hb : 2 < replacementDistance h d)
    (P : Sylow 2 M) (hP : (P : Subgroup M) = T)
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ (W.comap (embedM d.radical)).map s.projection)
    (hao : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) := by
  have hkex : ∃ k : alternatingGroup (Fin 6),
      ((normalizer (d.radical : Set d.overgroup)).map s.projection).map (MulAut.conj k.val).toMonoidHom ⊔ zpowers a = ⊤ := by
    obtain ⟨u,hpoint⟩ := SylowNormalizer.point_core_in_normalizer s hb P hP
    obtain ⟨k,hk⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates
      u ⟨a,haeven⟩ ((Subgroup.orderOf_coe ⟨a,haeven⟩).symm.trans hao)
    exact ⟨k,top_unique (hk ▸ sup_le_sup_right (map_mono hpoint) _)⟩
  obtain ⟨k,hk⟩ := hkex
  have hkL : k.val ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  let A := W.comap (embedM d.radical)
  have hm : (normalizer (d.radical.map (MulAut.conj g).toMonoidHom : Set d.overgroup)).map s.projection =
      ((normalizer (d.radical : Set d.overgroup)).map s.projection).map (MulAut.conj k.val).toMonoidHom := by
    rw [←map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k.val*s.projection x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ normalizer (d.radical.map (MulAut.conj g).toMonoidHom : Set d.overgroup) := by
    rw [s.projection_kernel,←hQ]
    exact (map_mono (replacement_core_le_radical h d)).trans (d.radical.map (MulAut.conj g).toMonoidHom).le_normalizer
  have hgen : normalizer (d.radical.map (MulAut.conj g).toMonoidHom : Set d.overgroup) ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hk]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  let f := (embedM d.radical g)⁻¹
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
  refine ⟨act d.radical f (beta d.radical),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff d.radical f (alpha d.radical) (beta d.radical)).mpr
      (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = W :=
      map_comap_eq_self (hWG.trans_eq (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range :=
      stabilizer_m_base d.radical
    rw [Subgroup.map_sup,SylowNormalizer.normalizer_embed,hmapA,←MonoidHom.range_eq_map,
      ←hbase] at hh
    have hmapR : (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) =
        Q d.radical (act d.radical f (beta d.radical)) := by
      rw [Q_act,Q_beta,map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change embedM d.radical (g*x*g⁻¹)=f⁻¹*embedM d.radical x*(f⁻¹)⁻¹
      simp only [f,inv_inv,map_mul,map_inv]
    rwa [hmapR] at hh

include e hz hn

/-- The restricted endpoint actor generates with an actual relative edge normalizer
in every original Sylow branch, including proper replacement radicals. -/
theorem large_image_controlled_neighbor_knownSimple
    (hb : 2 < replacementDistance h d)
    (P : Sylow 2 M) (hP : (P : Subgroup M) = T)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,a,ha,hao,haeven⟩ := critical_radius_even_actor s hc hb p hlarge
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) :=
    (hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical)
  refine ⟨W,hWU,hbound,?_,generating_neighbor_of_even_actor s hb P hP W hWG a ha hao haeven⟩
  intro hWQ
  have hWker : W.comap (embedM d.radical) ≤ s.projection.ker := by
    rw [s.projection_kernel]
    have hh := comap_mono (f := embedM d.radical) hWQ
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hbot := (Subgroup.map_eq_bot_iff (W.comap (embedM d.radical))).mpr hWker
  have hone : a=1 := by
    have hh : a ∈ (⊥ : Subgroup (Equiv.Perm (Fin 6))) := hbot ▸ ha
    exact hh
  rw [hone,orderOf_one] at hao
  omega

private theorem relative_orbit_escapes
    (s : FullSymmetricAction h e hz hn d)
    (hb : 2 < replacementDistance h d)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (hWne : ¬ W ≤ Q d.radical (alpha d.radical))
    (hbound : ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
      Z d.radical (alpha d.radical))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ W =
          stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical),
      ¬ (Z d.radical c).map (MulAut.conj g).toMonoidHom ≤
        Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical (alpha d.radical)
  let D := conjugateSpanBy (Z d.radical c) N
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hDV : D ≤ V d.radical (alpha d.radical) :=
    conjugateSpanBy_le (le_iSup_of_le c (le_iSup_of_le hdist le_rfl))
      (inf_le_right.trans (DistanceEight.V_normalized d.radical _))
  by_contra! hbad
  have hDP : D ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [show D = conjugateSpanBy (Z d.radical c) N from rfl,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun g => hbad g g.property)
  have hmove : ⁅D,W⁆ ≤ Z d.radical (alpha d.radical) :=
    (commutator_mono (le_inf hDV hDP) le_rfl).trans hbound
  have hDB := MixedStrict.generated_radius_le_slice s hb rfl D N W hDV inf_le_right
    hWG hWne (le_normalizer_conjugateSpanBy _ _) hgen hmove
  exact hel ((DistanceEight.U_le_Z d.radical c).trans
    ((le_conjugateSpanBy (Z d.radical c) N).trans hDB))

private theorem relative_controlled_backward_shift
    (s : FullSymmetricAction h e hz hn d)
    (hb : 2 < replacementDistance h d)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (hWne : ¬ W ≤ Q d.radical (alpha d.radical))
    (hbound : ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
      Z d.radical (alpha d.radical))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ W =
          stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ k ∈ stabilizer d.radical t,
      ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical),
        (∀ x ∈ Q d.radical t, (MulAut.conj k⁻¹) x = (MulAut.conj g) x) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical k c)
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k c)) =
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  obtain ⟨g,hg,hout⟩ := relative_orbit_escapes s hb p W hWG hWne hbound hat hct hgen hel
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical c ≤ Q d.radical t :=
    ((Z_le_VBall d.radical c 2).trans ((replacementGeometry h d).V_le_Q hb c hcol)).trans
      (Q_le_adjacent_h d.radical ht hct)
  obtain ⟨j,hj,he⟩ := Escape.Propagation.Backward.Products.holomorph_realizes t c hcol hct g hg.1
  have hZ : Z d.radical (act d.radical j⁻¹ c) =
      (Z d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [Z_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree hZt he
  have hU : U d.radical (act d.radical j⁻¹ c) =
      (U d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [U_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree
      ((DistanceEight.U_le_Z d.radical c).trans hZt) he
  have hct' : Adjacent d.radical (act d.radical j⁻¹ c) t := by
    have hfix : act d.radical j⁻¹ t = t := (stabilizer d.radical t).inv_mem hj
    simpa only [hfix] using (adjacent_act_iff d.radical j⁻¹ c t).mpr hct
  let w : (cosetGraph d.radical).Walk (act d.radical j⁻¹ c) (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct')
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hbad : ¬ Z d.radical (act d.radical j⁻¹ c) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2)) := by rwa [hZ]
  have hcolor : color d.radical (act d.radical j⁻¹ c) = false := by
    rw [action_preserves_color,hcol]
  let q := p.prepend_two (Nat.le_of_lt hb) hcolor w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨j⁻¹,(stabilizer d.radical t).inv_mem hj,g,hg,by simpa only [inv_inv] using he,q,hqt,
    fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,?_⟩
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hg.2)
  rw [hU,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hB]

/-- A prescribed eligible seed is shifted backward using the restricted even
actor. Both geometric transporters and the original relative-normalizer actor
are retained, with agreement on the entire edge kernel and the exact slice index. -/
theorem large_image_backward_shift_knownSimple
    (hb : 2 < replacementDistance h d)
    (P : Sylow 2 M) (hP : (P : Subgroup M) = T)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        act d.radical x (p.walk.getVert 1) = t ∧
        ∃ k ∈ stabilizer d.radical t,
          ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
              stabilizer d.radical (alpha d.radical),
            (∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (act d.radical k (act d.radical x delta))
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical (act d.radical k (act d.radical x delta))) =
              (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical delta) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ := large_image_controlled_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP p hlarge
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) :=
    (hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical)
  have hgenZ : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) := by
    apply le_antisymm
    · exact sup_le inf_le_right
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
          (replacementDistance_pos h d) p.critical)
    · exact hgen.symm.le.trans (sup_le_sup_left
        (hWU.trans (DistanceEight.U_le_Z d.radical a')) _)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  have hct : Adjacent d.radical (act d.radical x delta) t := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x delta (p.walk.getVert 1)).mpr hdelta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x delta)) =
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical delta) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,hB]
  have helc : ¬ U d.radical (act d.radical x delta) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    rw [U_act,←hB] at hh
    exact hel ((map_le_map_iff_of_injective (MulAut.conj x⁻¹).injective).mp hh)
  obtain ⟨k,hk,g,hg,hagree,q,hq1,hover,hidx⟩ := relative_controlled_backward_shift
    s hb p W hWG hWne hbound hat hct hgen helc
  exact ⟨t,hat,hgenZ,x,hx,hxt,k,hk,g,hg,hagree,q,hq1,hover,hidx.trans hi⟩

/-- Conjugate the same prescribed-seed construction to every original component
vertex, retaining both geometric actors, the relative-normalizer actor, its full
edge-kernel agreement, all walk overlaps and the exact slice index. -/
theorem large_image_backward_shift_at_knownSimple
    (hb : 2 < replacementDistance h d)
    (P : Sylow 2 M) (hP : (P : Subgroup M) = T)
    {a a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical a t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a) ⊔ Z d.radical a' =
          stabilizer d.radical a ∧
      ∃ x ∈ stabilizer d.radical a,
        act d.radical x (p.walk.getVert 1) = t ∧
        ∃ k ∈ stabilizer d.radical t,
          ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
              stabilizer d.radical a,
            (∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (act d.radical k (act d.radical x delta))
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical (act d.radical k (act d.radical x delta))) =
              (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical delta) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_image_backward_shift_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP
    (a' := act d.radical j⁻¹ a') (delta := act d.radical j⁻¹ delta)
  rw [←hbase] at base
  have hi : 4 ≤ (Q d.radical (act d.radical j⁻¹ a')).relIndex
      (Z d.radical (act d.radical j⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hd : Adjacent d.radical (act d.radical j⁻¹ delta) ((p.act j⁻¹).walk.getVert 1) := by
    simpa only [CriticalPath.act,actWalk_getVert] using
      (adjacent_act_iff d.radical j⁻¹ delta (p.walk.getVert 1)).mpr hdelta
  have hel' : ¬ U d.radical (act d.radical j⁻¹ delta) ≤
      B d.radical (act d.radical j⁻¹ a) ((replacementGeometry h d).Z_normal _) := by
    intro he
    rw [U_act,Escape.PairingControl.FirstPairing.B_act hb j⁻¹ a p.start_color] at he
    exact hel ((map_le_map_iff_of_injective (MulAut.conj _).injective).mp he)
  obtain ⟨t,hat,hgen,x,hx,hxt,k,hk,g,hg,hagree,q,hq1,hover,hidx⟩ := base (p.act j⁻¹) hi hd hel'
  let f := (MulAut.conj j⁻¹).toMonoidHom
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hact (y : FreeAmalgam d.radical) (v : Vertex d.radical) :
      act d.radical (f y) (act d.radical j v) = act d.radical j (act d.radical y v) := by
    simp only [f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,←act_mul]
    congr 1
    group
  have hstart : act d.radical j (act d.radical k (act d.radical x (act d.radical j⁻¹ delta))) =
      act d.radical (f k) (act d.radical (f x) delta) := by
    rw [←hact,←hact,hcancel]
  have hend : act d.radical j ((p.act j⁻¹).walk.getVert ((p.act j⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    simp only [CriticalPath.act,actWalk_length,actWalk_getVert,hcancel]
  have hB : (B d.radical (act d.radical j⁻¹ a) ((replacementGeometry h d).Z_normal _)).map f =
      B d.radical a ((replacementGeometry h d).Z_normal _) := by
    rw [←Escape.PairingControl.FirstPairing.B_act hb j _ (p.act j⁻¹).start_color,hcancel]
  have hex : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical j (act d.radical k (act d.radical x (act d.radical j⁻¹ delta))))
      (act d.radical j ((p.act j⁻¹).walk.getVert ((p.act j⁻¹).walk.length-2))),
      r.walk.getVert 1 = act d.radical j t ∧
      (∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i) ∧
      (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical j (act d.radical k (act d.radical x (act d.radical j⁻¹ delta))))) =
      (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta) := by
    refine ⟨q.act j,?_,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical j) hq1
    · intro i hi'
      have hh := congrArg (act d.radical j) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi'))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using hh
    · calc
        _ = (B d.radical (act d.radical j⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (act d.radical k (act d.radical x (act d.radical j⁻¹ delta)))) := by
          rw [←hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj j⁻¹).injective]
        _ = (B d.radical (act d.radical j⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (act d.radical j⁻¹ delta)) := hidx
        _ = _ := by
          rw [Escape.PairingControl.FirstPairing.B_act hb j⁻¹ a p.start_color,U_act,
            relIndex_map_map_of_injective _ _ (MulAut.conj j⁻¹⁻¹).injective]
  rw [hstart,hend] at hex
  refine ⟨act d.radical j t,?_,?_,f x,?_,?_,f k,?_,f g,?_,?_,hex⟩
  · simpa only [hcancel] using (adjacent_act_iff d.radical j _ _).mpr hat
  · have hh := congrArg (Subgroup.map f) hgen
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ (MulAut.conj j⁻¹).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj j⁻¹).bijective,
      ←Q_act,←stabilizer_act,←Z_act,hcancel,hcancel] at hh
    exact hh
  · have hh := mem_map_of_mem f hx
    change f x ∈ (stabilizer d.radical (act d.radical j⁻¹ a)).map f at hh
    rwa [←stabilizer_act,hcancel] at hh
  · have hh := congrArg (act d.radical j) hxt
    rw [←hact] at hh
    simpa only [CriticalPath.act,actWalk_getVert,hcancel] using hh
  · rw [stabilizer_act]
    exact mem_map_of_mem f hk
  · constructor
    · rw [Q_act,←map_normalizer_eq_of_bijective _ (MulAut.conj j⁻¹).bijective]
      exact mem_map_of_mem f hg.1
    · have hh := mem_map_of_mem f hg.2
      change f g ∈ (stabilizer d.radical (act d.radical j⁻¹ a)).map f at hh
      rwa [←stabilizer_act,hcancel] at hh
  · intro v hv
    rw [Q_act] at hv
    obtain ⟨v,hv,rfl⟩ := hv
    have he := congrArg f (hagree v hv)
    change f (k⁻¹*v*(k⁻¹)⁻¹) = f (g*v*g⁻¹) at he
    change (f k)⁻¹*f v*((f k)⁻¹)⁻¹ = f g*f v*(f g)⁻¹
    simpa only [map_mul,map_inv] using he

/-- Above distance four the original radical is already known to be Sylow.
Thus every large-image critical path has a backward extension without any
extra Sylow or radical-image premise. -/
theorem four_lt_large_image_backward_path_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a) ⊔ Z d.radical a' =
          stabilizer d.radical a ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨⟨P,hP⟩,_⟩ := MixedExclusion.four_lt_original_sylow_large_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨delta,hdelta,hel⟩ := exists_eligible_neighbor_at_edge s hc (by omega) p.start_color ha1
  obtain ⟨t,hat,hgen,x,hx,hxt,k,hk,g,hg,hagree,q,hq1,hover,hidx⟩ :=
    large_image_backward_shift_at_knownSimple (e := e) (hz := hz) (hn := hn)
      (by omega) P hP p hlarge hdelta hel
  have hct : Adjacent d.radical (act d.radical k (act d.radical x delta)) t := by
    have hh := (adjacent_act_iff d.radical x delta (p.walk.getVert 1)).mpr hdelta
    rw [hxt] at hh
    have hfix : act d.radical k t = t := hk
    simpa only [hfix] using (adjacent_act_iff d.radical k _ t).mpr hh
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hlo := critical_start_slice_index_two_le s hc (by omega) q
  rw [hqa] at hlo
  exact ⟨_,t,hat,hct,hgen,q,hq1,hover,hlo⟩

/-- The whole radius at the starting vertex escapes the predecessor core
along a large-image critical path. -/
theorem four_lt_large_image_radius_escape_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨c,t,hat,hct,_,q,_⟩ := four_lt_large_image_backward_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := a)
  intro hbad
  exact q.critical.2 (((Z_le_localZSpan d.radical _ _).trans
    (localZSpan_le_V d.radical hdist)).trans hbad)

/-- The same large critical path extends forward by two edges and drops
its first two edges. Its original endpoint is the new predecessor, and
every shared vertex is retained. -/
theorem four_lt_large_image_forward_extension_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ k ≤ p.walk.length-2, q.walk.getVert k = p.walk.getVert (k+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hec : (cosetGraph d.radical).dist a' (p.walk.getVert 2) + 2 =
      (replacementGeometry h d).b d.radical := by
    rw [SimpleGraph.dist_comm,p.dist_end,p.length_eq_b]
    change replacementDistance h d - 2 + 2 = replacementDistance h d
    omega
  let r : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hlarge' : 4 ≤ (Q d.radical a).relIndex (Z d.radical a') :=
    reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge
  have hescape := four_lt_large_image_radius_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hlarge'
  have hpre : r.walk.getVert (r.walk.length-2) = p.walk.getVert 2 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-2) = _
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse]
    congr 1
    omega
  rw [hpre] at hescape
  obtain ⟨z,hz,hze,hcrit⟩ := exists_critical_shift d.radical p.end_color hec hescape
  have hrev : CriticalPair d.radical (p.walk.getVert 2) z
      ((replacementGeometry h d).exists_critical _ hcol) := by
    apply critical_reverse d.radical (replacementGeometry h d) (edgeCentralizerCondition s hc)
      z hz _ _ hcol hcrit
    rw [(replacementGeometry h d).distance_constant z hz]
    exact replacementDistance_pos h d
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a' z
  have hvlen : v.length = 2 := hv.trans (SimpleGraph.dist_comm.trans hze)
  let w := (p.walk.drop 2).append v
  have hwlen : w.length = p.walk.length := by
    simp only [w,SimpleGraph.Walk.length_append,SimpleGraph.Walk.drop_length,hvlen]
    omega
  let q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z :=
    ⟨hcol,w,by rw [hwlen,p.length_eq_b,hrev.1,
      (replacementGeometry h d).distance_constant _ hcol]; rfl,hrev⟩
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert i = p.walk.getVert (i+2) := by
    change w.getVert i = _
    rw [SimpleGraph.Walk.getVert_append',SimpleGraph.Walk.drop_length,if_pos hi,
      SimpleGraph.Walk.drop_getVert,Nat.add_comm 2 i]
  refine ⟨z,q,by simpa only [SimpleGraph.dist_comm] using hze,hover,?_⟩
  change w.getVert (w.length-2) = a'
  rw [hwlen]
  change q.walk.getVert (p.walk.length-2) = a'
  rw [hover _ le_rfl,show p.walk.length-2+2 = p.walk.length by omega,p.walk.getVert_length]


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
