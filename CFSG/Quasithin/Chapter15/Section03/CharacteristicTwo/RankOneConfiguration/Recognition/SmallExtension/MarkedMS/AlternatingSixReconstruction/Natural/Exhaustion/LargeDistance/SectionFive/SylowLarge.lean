module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowRestriction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths

/-!
# Critical paths in the order-sixteen original Sylow branch

An order-sixteen radical image in the literal symmetric quotient is Sylow
and self-normalizing. The original radical is consequently Sylow as well,
and its restriction to the replacement overgroup equals the replacement
radical. Transport to each original edge identifies the relative normalizer
with the full edge kernel. The existing relative-normalizer generation
therefore gives full edge-kernel generation for every critical path.

For a large critical image, the restricted endpoint actor contains an even
involution. A conjugate point core contained in the Sylow image generates
with that involution. Lifting the same conjugator gives a generating edge
for the controlled actor. The radius-intersection commutator estimate then
constructs backward critical paths, including a version retaining a
prescribed eligible seed and its transporter. The selected paths retain
every overlapping vertex and have nontrivial starting slice. They prove
whole-radius escape and, on reversing the path, forward extension by two
edges at every original component vertex.

The statements retain both moved covers, all central attachments and the
actual replacement graph. They supply the large-critical-image path branch;
small-image shifts, the terminal original-Sylow exclusions and the remaining
distance-four estimates are still required for LargeDistanceInput.

The three `import all` dependencies intentionally reuse the internal Sylow
normalizer, graph embedding and controlled-actor kernel proofs within this
Section 5 implementation, without changing their existing public boundaries.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.8), (5.2), (5.5)--(5.8), and Section 7, printed pp.877--879,
914--920 and 932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowLarge
local notation "S" => Equiv.Perm (Fin 6)

private theorem image_sylow (A : Subgroup S) (hp : IsPGroup 2 A)
    (hcard : Nat.card A = 16) :
    ∃ W : Sylow 2 S, (W : Subgroup S) = A := by
  obtain ⟨W,hW⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S W sylow
  have he := congrArg (fun P : Sylow 2 S => Nat.card (P : Subgroup S)) hg
  change Nat.card ((W : Subgroup S).map (MulAut.conj g).toMonoidHom) = Nat.card sylowCarrier at he
  rw [card_map_of_injective (MulAut.conj g).injective,card_sylowCarrier] at he
  exact ⟨W,(eq_of_le_of_card_ge hW (by rw [he,hcard])).symm⟩

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)

include e hz hn in
/-- The original radical is Sylow, and its literal restriction equals the replacement radical. -/
theorem sixteen_original_restriction_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    (∃ P : Sylow 2 M, (P : Subgroup M) = T) ∧
      d.radical = (T).subgroupOf d.overgroup ∧
      (∃ W : Sylow 2 d.overgroup, (W : Subgroup d.overgroup) = d.radical) := by
  have hs : ∃ P : Sylow 2 M, (P : Subgroup M) = T := by
    by_contra hns
    rcases nonsylow_radical_image_maximal_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns with ⟨g,hg⟩ | ⟨g,hg⟩
    · rw [hg,card_map_of_injective (MulAut.conj g).injective,pointCore_card] at hcard
      omega
    · rw [hg,card_map_of_injective (MulAut.conj g).injective] at hcard
      have hc : Nat.card (CFSG.Quasithin.ChapterB.Offenders.D 6) = 8 := card_disjointTranspositions 3
      omega
  obtain ⟨P,hP⟩ := hs
  obtain ⟨hW,_,hprod,_⟩ := SylowRestriction.original_sylow_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP
  rw [hcard] at hprod
  have hi : d.radical.relIndex ((T).subgroupOf d.overgroup) = 1 := by omega
  have he : d.radical = (T).subgroupOf d.overgroup :=
    le_antisymm (comap_mono (map_subtype_le d.subgroup)) (relIndex_eq_one.mp hi)
  exact ⟨⟨P,hP⟩,he,he ▸ hW⟩

/-- The full replacement radical is self-normalizing in its actual overgroup. -/
theorem sixteen_radical_normalizer_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    normalizer (d.radical : Set d.overgroup) = d.radical := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hcard' : Nat.card (d.radical.map s.projection) = 16 := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨W,hW⟩ := image_sylow _ ((replacement_radical_isPGroup h d).map s.projection) hcard'
  have he : normalizer (d.radical.map s.projection : Set S) = d.radical.map s.projection := by
    rw [←hW,SylowRestriction.sylow_normalizer]
  have hh := congrArg (Subgroup.comap s.projection) he
  rwa [comap_normalizer_eq_of_surjective _ s.surjective,comap_map_eq,
    s.projection_kernel,sup_eq_left.mpr (replacement_core_le_radical h d)] at hh

include e hz hn in
/-- Every original edge has relative normalizer equal to its full edge kernel. -/
theorem sixteen_edge_relative_normalizer_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a = Q d.radical t := by
  have hbse : normalizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical) = Q d.radical (beta d.radical) := by
    rw [Q_beta,←SylowNormalizer.normalizer_embed, sixteen_radical_normalizer_knownSimple hb hcard]
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have hm := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbse
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      ←Q_act,←stabilizer_act] at hm
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hm
  · rw [hg.1] at ha
    cases ha

include e hz hn in
/-- Every critical endpoint generates the starting stabilizer with a full edge kernel. -/
theorem sixteen_critical_generating_neighbor_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ t, Adjacent d.radical a t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a := by
  obtain ⟨⟨P,hP⟩,_,_⟩ := sixteen_original_restriction_knownSimple hb hcard
  obtain ⟨t,hat,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP p
  rw [sixteen_edge_relative_normalizer_knownSimple hb hcard p.start_color hat] at hgen
  exact ⟨t,hat,hgen⟩

private theorem sixteen_generating_neighbor_of_even_actor
    (s : FullSymmetricAction h e hz hn d)
    (hcard : Nat.card (d.radical.map s.projection) = 16)
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ (W.comap (embedM d.radical)).map s.projection)
    (hao : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  have hkex : ∃ k : alternatingGroup (Fin 6),
      (d.radical.map s.projection).map (MulAut.conj k.val).toMonoidHom ⊔ zpowers a = ⊤ := by
    obtain ⟨W₀,hW₀⟩ := image_sylow _ ((replacement_radical_isPGroup h d).map s.projection) hcard
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq S sylow W₀
    have hpoint : pointCore.map (MulAut.conj u).toMonoidHom ≤ d.radical.map s.projection := by
      rw [←hW₀,←hu]
      exact map_mono (CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.le.trans
        exceptional_le_sylowCarrier)
    obtain ⟨k,hk⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates
      u ⟨a,haeven⟩ ((Subgroup.orderOf_coe ⟨a,haeven⟩).symm.trans hao)
    exact ⟨k,top_unique (hk ▸ sup_le_sup_right (map_mono hpoint) _)⟩
  obtain ⟨k,hk⟩ := hkex
  have hkL : k.val ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  let A := W.comap (embedM d.radical)
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k.val*s.projection x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ d.radical.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hgen : d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
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
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    have hmapR : (d.radical.map (embedM d.radical)).map (MulAut.conj f⁻¹).toMonoidHom =
        (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM d.radical x*(f⁻¹)⁻¹=embedM d.radical (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

/-- The restricted even endpoint actor generates with an actual full edge kernel. -/
theorem sixteen_large_image_controlled_neighbor_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,a,ha,hao,haeven⟩ := critical_radius_even_actor s hc hb p hlarge
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) :=
    (hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical)
  have hcard' : Nat.card (d.radical.map s.projection) = 16 := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  refine ⟨W,hWU,hbound,?_,sixteen_generating_neighbor_of_even_actor s hcard' W hWG a ha hao haeven⟩
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

/-- A prescribed eligible first-edge seed gives a literal backward critical path. -/
theorem sixteen_large_image_backward_shift_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ k ≤ p.walk.length-2, q.walk.getVert (k+2) = p.walk.getVert k) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ := sixteen_large_image_controlled_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hlarge
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have helc : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hel
    change U d.radical (act d.radical g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply helc
    apply (DistanceEight.U_le_Z d.radical c).trans
    apply backward_kernel_le_slice_of_controlled_actor s hb p W hWU hWne hbound hat hct hgen
      (Z d.radical c) le_rfl hbad
    exact (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (by exact Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hgenZ : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
          (replacementDistance_pos h d) p.critical)
    · rw [←hgen]
      exact sup_le_sup_left (hWU.trans (DistanceEight.U_le_Z d.radical a')) _
  exact ⟨t,hat,hgenZ,g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩

/-- The controlled actor supplies a backward critical path with full edge-kernel
generation and a nontrivial starting slice. -/
theorem sixteen_large_image_backward_path_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ c t, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ k ≤ p.walk.length-2, q.walk.getVert (k+2) = p.walk.getVert k) ∧
        2 ≤ (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ := sixteen_large_image_controlled_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hlarge
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply hel
    apply (DistanceEight.U_le_Z d.radical c).trans
    apply backward_kernel_le_slice_of_controlled_actor s hb p W hWU hWne hbound hat hct hgen
      (Z d.radical c) le_rfl hbad
    exact (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hover (k : ℕ) (hk : k ≤ p.walk.length-2) :
      q.walk.getVert (k+2) = p.walk.getVert k := p.prepend_two_overlap _ _ _ _ _ hk
  have hqa : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hlo := critical_start_slice_index_two_le s hc hb q
  rw [hqa] at hlo
  have hgenZ : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
          (replacementDistance_pos h d) p.critical)
    · rw [←hgen]
      exact sup_le_sup_left (hWU.trans (DistanceEight.U_le_Z d.radical a')) _
  exact ⟨c,t,hat,hct,hgenZ,q,hqt,hover,hlo⟩

/-- Transport the selected backward path, its generating edge and its slice
index to every original component vertex. -/
theorem sixteen_large_image_backward_path_at_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ k ≤ p.walk.length-2, q.walk.getVert (k+2) = p.walk.getVert k) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := sixteen_large_image_backward_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hl : 4 ≤ (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (act d.radical g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  obtain ⟨c,t,hat,hct,hgen,q,hqt,hover,hindex⟩ := base (p.act g⁻¹) hl
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hB : (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) := by
    rw [←Escape.PairingControl.FirstPairing.B_act hb g _ (p.act g⁻¹).start_color,hcancel]
  have hidx : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g c)) =
      (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) := by
    rw [←hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
  have hex : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g c)
      (act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act d.radical g t ∧
      (∀ k ≤ p.walk.length-2, r.walk.getVert (k+2) = p.walk.getVert k) ∧
      2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g c)) := by
    refine ⟨q.act g,?_,?_,hidx.symm ▸ hindex⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical g) hqt
    · intro k hk
      have hh := congrArg (act d.radical g) (hover k (by
        simpa only [CriticalPath.act,actWalk_length] using hk))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using hh
  have hend : act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act d.radical g ((actWalk d.radical g⁻¹ p.walk).getVert
      ((actWalk d.radical g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hex
  refine ⟨act d.radical g c,act d.radical g t,?_,?_,?_,hex⟩
  · simpa only [hcancel] using (adjacent_act_iff d.radical g _ _).mpr hat
  · exact (adjacent_act_iff d.radical g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he


/-- The whole radius at the starting vertex escapes the predecessor core
along a large-image critical path. -/
theorem sixteen_large_image_radius_escape_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨c,t,hat,hct,_,q,_⟩ := sixteen_large_image_backward_path_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hlarge
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
theorem sixteen_large_image_forward_extension_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ k ≤ p.walk.length-2, q.walk.getVert k = p.walk.getVert (k+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
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
  have hescape := sixteen_large_image_radius_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r hlarge'
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


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowLarge
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
