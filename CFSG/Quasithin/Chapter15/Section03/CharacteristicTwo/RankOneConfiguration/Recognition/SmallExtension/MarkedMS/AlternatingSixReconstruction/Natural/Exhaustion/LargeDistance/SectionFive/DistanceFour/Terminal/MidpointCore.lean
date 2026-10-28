module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullSeedBackward
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.LargeMovementFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane

/-!
# Whole midpoint-core movement on large distance-four paths

Both endpoint seeds of a four-edge critical path lie in the midpoint
radius. Source (5.2)(ii) puts their commutator in the midpoint omega-center,
so the entire midpoint core fixes their displacement. The six-letter
large-displacement fixer theorem makes this core act quadratically on
the starting natural module. Its action lifts to either full moving cover.
The central edge attachment has zero movement, giving the same quadratic
identity on the entire starting seed.

Consequently its full midpoint-core commutator lies in the midpoint
omega-center, is normalized by the first edge and contains the critical
commutator. Normal closure extends this estimate to the selected span.
The actual full-seed backward application retains one endpoint restriction,
its index and central attachment, its exact critical commutator, and the
same selected path. In that application the original nonsylow hypothesis
supplies the large backward image. The core estimates themselves impose
no Sylow, radical-image, or cover-order restriction.

This establishes midpoint-core control in the large-image branch of
MS93 (5.12)(2). It does not bound the derived subgroup of the whole
residual core [Q,Ltilde], exclude large slices, or assert DistanceFourInput.
The Sylow small-backward exclusion and the terminal contradiction remain.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2)(ii), and (5.12)(2), printed pp.867,914--915,925--926;
the characteristic replacement is the literal one from Section 7.
The internal imports reuse the existing natural edge coordinates and
full-seed attachment identity without changing their public boundaries.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem cover_large_fixer_natural
    (A P : Subgroup d.overgroup) (hAR : A ≤ d.radical) (hPR : P ≤ d.radical)
    (hc : 2 < (pCore 2 d.overgroup).relIndex A)
    (hf : P ≤ centralizer ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup)) :
    ∀ g ∈ P, ∀ k ∈ P, ∀ v : natural (Fin 6),
      naturalRepresentation (Fin 6) (s.projection k)
        (naturalRepresentation (Fin 6) (s.projection g) v-v) =
        naturalRepresentation (Fin 6) (s.projection g) v-v := by
  let := replacementMoved_normal h d
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hnatural := LargeMovementFixer.two_group_large_fixer_quadratic
    (d.radical.map s.projection) (A.map s.projection) (P.map s.projection)
    ((replacement_radical_isPGroup h d).map s.projection) (map_mono hAR) (map_mono hPR)
    (by rwa [←relIndex_ker,s.projection_kernel])
    (by
      rintro _ ⟨g,hg,rfl⟩ _ ⟨a,ha,rfl⟩ v
      obtain ⟨w,rfl⟩ := coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d) v
      have hw : coverAction s (s.projection a) w-w ∈ commutatorSpace (replacementMoved d) A := by
        rw [commutatorSpace_eq (replacementMoved d) s.projection s.surjective hker]
        exact Submodule.subset_span ⟨s.projection a,mem_map_of_mem _ ha,w,Submodule.mem_top,rfl⟩
      have hfix : coverAction s (s.projection g) (coverAction s (s.projection a) w-w) =
          coverAction s (s.projection a) w-w := by
        let v' : Additive (replacementMoved d) := coverAction s (s.projection a) w-w
        have hv' : (v'.toMul : d.overgroup) ∈ ⁅replacementMoved d,A⁆ := hw
        have hh := (mem_fixedSpace_image (replacementMoved d) s.projection s.surjective hker P v').mpr
          ((le_centralizer_iff.mp hf) hv')
        exact hh ⟨s.projection g,mem_map_of_mem _ hg⟩
      have hh := congrArg (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)) hfix
      simpa only [coverMap_equivariant,map_sub] using hh)
  intro g hg k hk v
  exact hnatural _ (mem_map_of_mem _ hg) _ (mem_map_of_mem _ hk) v

private theorem cover_lift_quadratic {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (τ : Representation (ZMod 2) S Y) (hm : SixCover.IsNaturalOrCore τ (MonoidHom.id S))
    (g k : S)
    (hquad : ∀ v : natural (Fin 6), naturalRepresentation (Fin 6) k
      (naturalRepresentation (Fin 6) g v-v) = naturalRepresentation (Fin 6) g v-v)
    (v : Y) : τ k (τ g v-v)=τ g v-v := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · apply E.injective
    simpa only [hE,map_sub,MonoidHom.id_apply] using hquad (E v)
  · have hcore : coreRepresentation (Fin 6) k
        (coreRepresentation (Fin 6) g (E v)-E v) = coreRepresentation (Fin 6) g (E v)-E v := by
      apply SixCover.six_core_fixed_of_natural_fixed
      simpa only [map_sub,coreToNatural_equivariant] using hquad (coreToNatural (Fin 6) (E v))
    apply E.injective
    simpa only [hE,map_sub,MonoidHom.id_apply] using hcore

include s in
private theorem cover_large_fixer_quadratic
    (A P : Subgroup d.overgroup) (hAR : A ≤ d.radical) (hPR : P ≤ d.radical)
    (hc : 2 < (pCore 2 d.overgroup).relIndex A)
    (hf : P ≤ centralizer ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup)) :
    ⁅replacementMoved d,P⁆ ≤ centralizer (P : Set d.overgroup) := by
  let := replacementMoved_normal h d
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hnatural := cover_large_fixer_natural s A P hAR hPR hc hf
  have hquad (g k : d.overgroup) (hg : g ∈ P) (hk : k ∈ P) (v : Additive (replacementMoved d)) :
      coverAction s (s.projection k) (coverAction s (s.projection g) v-v) =
        coverAction s (s.projection g) v-v :=
    cover_lift_quadratic (coverAction s) (cover_model s) _ _ (hnatural g hg k hk) v
  apply commutator_le.mpr
  intro v hv r hr k hk
  have hm : ⁅v,r⁆ ∈ replacementMoved d :=
    (commutator_le_left (replacementMoved d) P) (commutator_mem_commutator hv hr)
  let w : Additive (replacementMoved d) := Additive.ofMul ⟨⁅v,r⁆,hm⟩
  have he : coverAction s (s.projection k) w=w := by
    dsimp only [w]
    rw [NormalElementaryQuotient.vector_commutator (replacementMoved d)
      s.projection s.surjective hker ⟨v,hv⟩ r]
    have hh := hquad r k hr hk (Additive.ofMul ⟨v,hv⟩)
    change coverAction s (s.projection k)
      (Additive.ofMul ⟨v,hv⟩-coverAction s (s.projection r) (Additive.ofMul ⟨v,hv⟩)) =
      Additive.ofMul ⟨v,hv⟩-coverAction s (s.projection r) (Additive.ofMul ⟨v,hv⟩)
    simpa only [map_sub,neg_sub] using congrArg Neg.neg hh
  have he' := congrArg (fun a : Additive (replacementMoved d) => (a.toMul : d.overgroup)) he
  rw [coverAction_conjugate] at he'
  exact mul_inv_eq_iff_eq_mul.mp he'

include s in
/-- An edge actor fixing the full movement of a large image acts
quadratically on the entire incident seed, including its central attachment. -/
theorem edge_large_fixer_quadratic
    (hc : DistanceTwo.CentralLayer d)
    {c t : Vertex d.radical} (hcCol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A P : Subgroup (FreeAmalgam d.radical))
    (hAT : A ≤ Q d.radical t) (hPT : P ≤ Q d.radical t)
    (hiA : 2 < (Q d.radical c).relIndex A)
    (hf : P ≤ centralizer ((⁅U d.radical c,A⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical c,P⁆ ≤ centralizer (P : Set (FreeAmalgam d.radical)) := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc hcCol hct
  have hTG : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hPm : (P.comap i).map i = P := map_comap_eq_self ((hPT.trans hTG).trans_eq hir.symm)
  have hAm : (A.comap i).map i = A := map_comap_eq_self ((hAT.trans hTG).trans_eq hir.symm)
  have hAR : A.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hAm,hiR]
  have hPR : P.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hPm,hiR]
  have hi' : 2 < (pCore 2 d.overgroup).relIndex (A.comap i) := by
    rw [←relIndex_map_map_of_injective _ _ hi,hiQ,hAm]
    exact hiA
  have hcomm : (⁅replacementMoved d,A.comap i⁆).map i = ⁅U d.radical c,A⁆ := by
    rw [map_commutator,hiU,hAm]
  have hf' : P.comap i ≤ centralizer ((⁅replacementMoved d,A.comap i⁆ :
      Subgroup d.overgroup) : Set d.overgroup) := by
    intro p hp v hv
    apply hi
    simp only [map_mul]
    exact hf hp (i v) (hcomm ▸ mem_map_of_mem i hv)
  have hquad := (map_mono (f := i) (cover_large_fixer_quadratic s (A.comap i) (P.comap i)
    hAR hPR hi' hf')).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [map_commutator,hiU,hPm] at hquad
  change ⁅U d.radical c,P⁆ ≤ centralizer ((P.comap i).map i : Set (FreeAmalgam d.radical)) at hquad
  rw [hPm] at hquad
  rwa [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) hcCol hct P hPT]

include s in
/-- The whole midpoint core acts quadratically on the starting seed of a
large distance-four critical path, for every original radical image. -/
theorem large_midpoint_core_quadratic
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ⁅Z d.radical a,Q d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (Q d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hQcT : Q d.radical c ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hct
  have hZa'Qc : Z d.radical a' ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  apply edge_large_fixer_quadratic s hc p.start_color hat (Z d.radical a')
    (Q d.radical c) (hZa'Qc.trans hQcT) hQcT
  · have hh := reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge
    omega
  · apply le_centralizer_iff.mp
    have haV : Z d.radical a ≤ V d.radical c :=
      le_iSup_of_le a (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl)
    have ha'V : Z d.radical a' ≤ V d.radical c :=
      le_iSup_of_le a' (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_end,hl]) le_rfl)
    have hRX : ⁅U d.radical a,Z d.radical a'⁆ ≤ X d.radical c :=
      (commutator_mono ((DistanceEight.U_le_Z d.radical a).trans haV) ha'V).trans
        (radius_bounds_general s hc hb2 hcCol a a').2.1
    exact hRX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)

include s in
/-- The entire midpoint-core movement lies in the moving cover and midpoint
omega-center, is normalized by the first edge, and contains the critical
commutator. All groups refer to the same critical path. -/
theorem large_midpoint_movement
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    let H := ⁅Z d.radical a,Q d.radical (p.walk.getVert 2)⁆
    H ≤ U d.radical a ∧ H ≤ X d.radical (p.walk.getVert 2) ∧
      Q d.radical (p.walk.getVert 1) ≤ normalizer (H : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical a,Z d.radical a'⁆ ≤ H := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let H := ⁅Z d.radical a,Q d.radical c⁆
  change H ≤ U d.radical a ∧ H ≤ X d.radical c ∧
    Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) ∧
    ⁅Z d.radical a,Z d.radical a'⁆ ≤ H
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hQcT : Q d.radical c ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hct
  have hTGa : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hTGc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hHU : H ≤ U d.radical a := by
    dsimp only [H]
    rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat _ hQcT]
    exact le_normalizer_iff_commutator_le_left.mp
      ((hQcT.trans hTGa).trans (U_normalized a))
  have hZaQc : Z d.radical a ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb2
  have hHQ : H ≤ Q d.radical c := (hHU.trans (DistanceEight.U_le_Z d.radical a)).trans hZaQc
  have hfixed := large_midpoint_core_quadratic s hc hb p hlarge
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hHX : H ≤ X d.radical c := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQ hx,
      elemPow_eq_one_of_isElementaryAbelian x ((hHU.trans (DistanceEight.U_le_Z d.radical a)) hx),
      hfixed hx⟩
  have hTN : Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅Z d.radical a,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)).map _ = _
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (hTGa hx)),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical c (hTGc hx))]
  have hZa'Qc : Z d.radical a' ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  exact ⟨hHU,hHX,hTN,commutator_mono le_rfl hZa'Qc⟩

include s in
/-- Normal closure under the midpoint stabilizer extends the endpoint
estimate to the whole selected span and the whole midpoint core. -/
theorem large_selected_span_core_commutator_le_X
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ⁅localZSpan d.radical a (p.walk.getVert 2),Q d.radical (p.walk.getVert 2)⁆ ≤
      X d.radical (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hZaG : Z d.radical a ≤ stabilizer d.radical c := by
    apply Z_le_stabilizer_of_dist_le
    rw [p.dist_start (by omega),(replacementGeometry h d).distance_constant _ p.start_color]
    change 2 ≤ replacementDistance h d
    omega
  have hbound := (large_midpoint_movement s hc hb p hlarge).2.1
  rw [localZSpan_eq_conjugates]
  apply commutator_iSup_le_of_relative_normal (stabilizer d.radical c) (Q d.radical c) _ _
    (X_normalized d.radical c)
  · intro g
    have hm : (stabilizer d.radical c).map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom =
        stabilizer d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical c).le_normalizer
        ((stabilizer d.radical c).inv_mem g.property))
    exact (map_mono hZaG).trans_eq hm
  · intro g
    have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) hbound
    have hQ : (Q d.radical c).map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = Q d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical c
        ((stabilizer d.radical c).inv_mem g.property))
    have hX : (X d.radical c).map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = X d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (X_normalized d.radical c
        ((stabilizer d.radical c).inv_mem g.property))
    rwa [map_commutator,hQ,hX] at hm

include e hz hn in
/-- The controlled full endpoint restriction and the chosen backward path
also have midpoint-core control. The nonsylow branch supplies the large
backward image; no new fixedness or normality premise is assumed. -/
theorem large_image_full_seed_core_backward_knownSimple
    (hb : replacementDistance h d = 4)
    (hns : ¬ ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ (W : Subgroup (FreeAmalgam d.radical)) (t c : Vertex d.radical),
      Z d.radical (p.walk.getVert 3) ≤ W ∧ W ≤ Z d.radical a' ∧
      W.relIndex (Z d.radical a') ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),W⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
        q.walk.getVert 3 = p.walk.getVert 1 ∧
        4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ⁅(Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔ Z d.radical (alpha d.radical),W⁆ =
          ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ∧
        ⁅localZSpan d.radical c (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
          X d.radical (alpha d.radical) ∧
        (let H := ⁅Z d.radical c,Q d.radical (alpha d.radical)⁆;
          H ≤ U d.radical c ∧ H ≤ X d.radical (alpha d.radical) ∧
          Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) ∧
          ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤ H) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hindex,hcritical,_,_,t,c,hat,hct,_,hgen,q,hq1,hq2,hq3,
    _,hstrict,_,_,hDexact,_,_,_,hlargeq⟩ :=
    large_image_full_seed_backward_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hlargeq' := hlargeq hns
  have hspan := large_selected_span_core_commutator_le_X s hc hb q hlargeq'
  have hmovement := large_midpoint_movement s hc hb q hlargeq'
  rw [hq2] at hspan
  rw [hq1,hq2] at hmovement
  exact ⟨W,t,c,hFE,hWZ,hindex,hcritical,hat,hct,hgen hns,q,hq1,hq2,hq3,
    hlargeq',hstrict,hDexact,hspan,hmovement⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
