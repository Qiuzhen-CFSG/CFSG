module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalNormalization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalLines
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Distance-six terminal normalization

For the image-sixteen branch, failure of terminal normalization at distance
six leaves two possible critical commutator lines. The existing orbit-path
argument handles the distinct-line alternative. In the coincident alternative,
the escaped central attachment forces the moved cover to be the full
augmentation core. A coordinate calculation for a transposition shows that
an actor centralizing it cannot move its fixed hyperplane into that same
transposition line. Since the reverse restricted actor centralizes the
critical actor, coincident lines would then vanish, contradicting the
nontrivial critical commutator. This supplies the distance-six case alongside
the established distance-greater-than-six normalization argument, while
retaining both covers and the literal original-radical path and transporter.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii) and (5.10), printed pp.866--867 and 922--923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive

private theorem core_fixed_line_zero (t : S) (ht : t.IsSwap) (B : Subgroup S)
    (hc : B ≤ centralizer ({t} : Set S))
    (hline : subspaceCommutator (coreRepresentation (Fin 6))
      (fixedSpace (coreRepresentation (Fin 6)) (zpowers t)) B ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ (zpowers t)) :
    subspaceCommutator (coreRepresentation (Fin 6))
      (fixedSpace (coreRepresentation (Fin 6)) (zpowers t)) B = ⊥ := by
  obtain ⟨i,j,hij,rfl⟩ := ht
  let ρ := coreRepresentation (Fin 6)
  have hmove : subspaceCommutator ρ ⊤ (zpowers (Equiv.swap i j)) ≤
      Submodule.span (ZMod 2) {pairWord i j} := by
    rw [Representation.CyclicFixedRank.commutator_eq_range]
    rintro _ ⟨v,rfl⟩
    have he : ρ (Equiv.swap i j) v-v = (v.val j-v.val i) • pairWord i j := by
      apply Subtype.ext
      funext k
      by_cases hki : k=i
      · subst k
        simp [ρ,representation_apply,pairWord,hij]
      · by_cases hkj : k=j
        · subst k
          simp [ρ,representation_apply,pairWord,hij,CharTwo.sub_eq_add,add_comm]
        · simp [ρ,representation_apply,pairWord,hki,hkj,
            Equiv.swap_apply_of_ne_of_ne hki hkj]
    change ρ (Equiv.swap i j) v-v ∈ _
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  have hfix := (mem_fixedSpace_zpowers_iff _ _ _).mp hv
  have hvij : v.val j=v.val i := by
    simpa only [coreRepresentation_apply,representation_apply,Equiv.symm_swap,Equiv.swap_apply_left] using
      congrArg (fun w : core (Fin 6) => w.val i) hfix
  have hcomm : Commute g (Equiv.swap i j) := (hc hg _ (Set.mem_singleton _)).symm
  have he := congrArg (fun f : S => f i) hcomm.inv_left.eq
  have hpre : g⁻¹ i=i ∨ g⁻¹ i=j := by
    by_contra hne
    push Not at hne
    have hx : g⁻¹ j=g⁻¹ i := by
      simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hne.1 hne.2] using he
    exact hij ((g⁻¹).injective hx).symm
  have hzero : (ρ g v-v).val i=0 := by
    change v.val (g⁻¹ i)-v.val i=0
    rcases hpre with hh|hh
    · rw [hh,sub_self]
    · rw [hh,hvij,sub_self]
  have hm : ρ g v-v ∈ Submodule.span (ZMod 2) {pairWord i j} :=
    hmove (hline (Submodule.subset_span ⟨g,hg,v,hv,rfl⟩))
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
  have ha0 : a=0 := by
    have hh := congrArg (fun w : core (Fin 6) => w.val i) ha
    simpa [pairWord,hij,hzero] using hh
  change ρ g v-v=0
  rw [←ha,ha0,zero_smul]

private theorem core_fixed_line_zero_equiv
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) S W)
    (E : W ≃ₗ[ZMod 2] core (Fin 6))
    (hE : ∀ g v, E (σ g v)=coreRepresentation (Fin 6) g (E v))
    (t : S) (ht : t.IsSwap) (B : Subgroup S)
    (hc : B ≤ centralizer ({t} : Set S))
    (hl : subspaceCommutator σ (fixedSpace σ (zpowers t)) B ≤
      subspaceCommutator σ ⊤ (zpowers t)) :
    subspaceCommutator σ (fixedSpace σ (zpowers t)) B = ⊥ := by
  let ρ := coreRepresentation (Fin 6)
  have hmap (I : Submodule (ZMod 2) W) (D : Subgroup S) :
      (subspaceCommutator σ I D).map E.toLinearMap =
      subspaceCommutator ρ (I.map E.toLinearMap) D := by
    simpa only [map_id] using (subspaceCommutator_map_embedding ρ σ
      (MonoidHom.id _) E.toLinearMap (fun g v => (hE g v).symm) D I).symm
  have hmapF : (fixedSpace σ (zpowers t)).map E.toLinearMap =
      fixedSpace ρ (zpowers t) := by
    apply le_antisymm
    · rintro _ ⟨w,hw,rfl⟩ g
      change ρ g.val (E w)=E w
      rw [←hE]
      exact congrArg E (hw g)
    · intro v hv
      obtain ⟨w,rfl⟩ := E.surjective v
      refine ⟨w,?_,rfl⟩
      intro g
      apply E.injective
      change E (σ g.val w)=E w
      rw [hE]
      exact hv g
  have hmapT : (⊤ : Submodule (ZMod 2) W).map E.toLinearMap=⊤ := by
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr E.surjective]
  have hh := Submodule.map_mono (f := E.toLinearMap) hl
  rw [hmap,hmap,hmapF,hmapT] at hh
  have hz := core_fixed_line_zero t ht B hc hh
  apply le_bot_iff.mp
  intro v hv
  have hev : E v ∈ subspaceCommutator ρ (fixedSpace ρ (zpowers t)) B := by
    rw [←hmapF,←hmap]
    exact ⟨v,hv,rfl⟩
  rw [hz] at hev
  exact E.injective ((show E v=0 from hev).trans E.map_zero.symm)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem cover32_fixed_line_zero
    (hc32 : Nat.card (replacementMoved d) = 32)
    (A B : Subgroup d.overgroup)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (hcent : B ≤ centralizer (A : Set d.overgroup))
    (hline : ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ ≤
      ⁅replacementMoved d,A⁆) :
    ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ = ⊥ := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let F := U ⊓ centralizer (A : Set d.overgroup)
  let K := ⁅F,B⁆
  have hKU : K ≤ U := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left U B)
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim U s.projection s.surjective hker] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A.map s.projection) hnA hnat
  have hF : NormalElementaryQuotient.subgroupSpace U F = fixedSpace (coverAction s) (A.map s.projection) := by
    ext v
    change ((v.toMul : d.overgroup) ∈ U ∧ (v.toMul : d.overgroup) ∈ centralizer (A : Set d.overgroup)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective hker A v).symm
  have hK : NormalElementaryQuotient.subgroupSpace U K = subspaceCommutator (coverAction s)
      (fixedSpace (coverAction s) (A.map s.projection)) (B.map s.projection) := by
    rw [NormalElementaryQuotient.subgroupSpace_commutator U s.projection s.surjective hker F B inf_le_left,hF]
    rfl
  have hU : NormalElementaryQuotient.subgroupSpace U U = ⊤ := by ext v; exact iff_of_true v.toMul.property trivial
  have hwhole : NormalElementaryQuotient.subgroupSpace U ⁅U,A⁆ =
      subspaceCommutator (coverAction s) ⊤ (A.map s.projection) := by
    rw [NormalElementaryQuotient.subgroupSpace_commutator U s.projection s.surjective hker U A le_rfl,hU]
    rfl
  rcases cover_model s with ⟨E,_⟩ | ⟨E,hE⟩
  · have h16 : Nat.card (replacementMoved d) = 16 := by
      change Nat.card (Additive (replacementMoved d)) = 16
      rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
        finrank_natural_even (Fin 6) (by decide)]
      norm_num
    omega
  · have hl : subspaceCommutator (coverAction s)
        (fixedSpace (coverAction s) (zpowers t)) (B.map s.projection) ≤
        subspaceCommutator (coverAction s) ⊤ (zpowers t) := by
      have hh := NormalElementaryQuotient.subgroupSpace_mono U hline
      rwa [hK,hwhole,he] at hh
    have hcB : B.map s.projection ≤ centralizer ({t} : Set S) := by
      rintro _ ⟨b,hb,rfl⟩ _ rfl
      obtain ⟨a,ha,rfl⟩ := ht
      simpa only [map_mul] using congrArg s.projection (hcent hb a ha)
    have hzero := core_fixed_line_zero_equiv (coverAction s) E hE t hs
      (B.map s.projection) hcB hl
    have hzeroK : NormalElementaryQuotient.subgroupSpace U K = ⊥ := by
      rw [hK,he]
      exact hzero
    apply le_bot_iff.mp
    intro x hx
    let v : Additive U := Additive.ofMul ⟨x,hKU hx⟩
    have hv : v ∈ NormalElementaryQuotient.subgroupSpace U K := hx
    rw [hzeroK] at hv
    have hv0 : v=0 := hv
    exact congrArg (fun v : Additive U => (v.toMul : d.overgroup)) hv0

include s in
private theorem moving_attachment_zero_of_sixteen
    (hc : DistanceTwo.CentralLayer d) (h16 : Nat.card (replacementMoved d)=16)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) = ⊥ := by
  let f := coverProjection h e hz hn d
  have hr : Nat.card f.range=16 := by
    rw [MonoidHom.range_eq_top.mpr (coverProjection_surjective h e hz hn d),
      Nat.card_congr (topEquiv).toEquiv]
    change Nat.card (natural (Fin 6))=16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),finrank_natural_even (Fin 6) (by decide)]
    norm_num
  have hk := f.ker.card_mul_index
  rw [index_ker,hr,h16] at hk
  have hk0 : f.ker=⊥ := Subgroup.card_eq_one.mp (by omega)
  obtain ⟨i,hi,hir,_,hiU⟩ := vertex_coordinates (h := h) hc a ha
  apply le_bot_iff.mp
  rintro x ⟨hx,hxc⟩
  rw [←hiU] at hx
  obtain ⟨v,hv,rfl⟩ := hx
  have hvC : v ∈ center d.overgroup := mem_center_iff.mpr (fun m => hi (by
    simpa only [map_mul] using hxc (i m) (hir ▸ (show i m ∈ i.range from ⟨m,rfl⟩))))
  have hvK : (⟨v,hv⟩ : replacementMoved d) ∈ f.ker := by
    rw [coverProjection_kernel_center s]
    exact hvC
  rw [hk0,mem_bot] at hvK
  have hv1 : v=1 := congrArg Subtype.val hvK
  simp only [hv1,map_one,one_mem]

include s in
private theorem critical_fixed_line_zero_of_cover32
    (hc : DistanceTwo.CentralLayer d)
    (hc32 : Nat.card (replacementMoved d)=32)
    {a a' t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a)<4)
    (hat : Adjacent d.radical a t)
    (hAt : Z d.radical a' ≤ Q d.radical t)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYt : Y ≤ Q d.radical t) (hYQ : Y ≤ Q d.radical a')
    (hline : ⁅Z d.radical a ⊓ Q d.radical a',Y⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆) :
    ⁅Z d.radical a ⊓ Q d.radical a',Y⁆ = ⊥ := by
  have hYG : Y ≤ stabilizer d.radical a := hYt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hAG : Z d.radical a' ≤ stabilizer d.radical a := hAt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hfix : Z d.radical a ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ Q d.radical a' := by
    apply le_antisymm
    · rintro x ⟨hx,hxc⟩
      refine ⟨hx,?_⟩
      rw [←C_eq_Q s hc a' p.end_color]
      exact ⟨Z_le_stabilizer_of_dist_le a _ p.critical.1.le hx,hxc⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
  have hfull := full_fixed_seed_edge_commutator (h := h) (e := e) (hz := hz)
    p.start_color hat (Z d.radical a') hAt Y hYt
  rw [hfix] at hfull
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  let A := (Z d.radical a').comap i
  let B := Y.comap i
  have hmA : A.map i = Z d.radical a' := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmB : B.map i = Y := map_comap_eq_self (hYG.trans_eq hir.symm)
  have hmK : (⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆).map i =
      ⁅Z d.radical a ⊓ Q d.radical a',Y⁆ := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hmB,←hfull]
  have hmD : (⁅replacementMoved d,A⁆).map i = ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [map_commutator,hiU,hmA,small_critical_moving_commutator_eq s hc p hsmall]
  have hnA : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    have he := map_mono (f := i) hh
    rw [hmA,hiQ] at he
    exact (critical_reverse_pair s hc p).2 he
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  have hCA : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a' p.end_color))
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    exact ((relIndex_le_of_le_left hCA index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).1
  have hcent : B ≤ centralizer (A : Set d.overgroup) := by
    intro b hb m hm
    apply hi
    simp only [map_mul]
    exact hCA (hYQ (hmB ▸ mem_map_of_mem i hb)) _ (hmA ▸ mem_map_of_mem i hm)
  have hl : ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ ≤ ⁅replacementMoved d,A⁆ := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmK,hmD]
  have hh := congrArg (Subgroup.map i) (cover32_fixed_line_zero s hc32 A B hnA hidx hcent hl)
  rwa [hmK,Subgroup.map_bot] at hh

include e hz hn in
/-- The terminal restricted line cannot coincide with the last critical line:
the natural cover has no attachment, and the augmentation cover's fixed
hyperplane cannot move into that transposition's own line. -/
theorem three_shift_nonnormalized_lines_distinct_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆ ≠
      ⁅Z d.radical t.start,Z d.radical v⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let F := Z d.radical z ⊓ Q d.radical r.start
  change ⁅Z d.radical t.start ⊓ Q d.radical v,F⁆ ≠ ⁅Z d.radical t.start,Z d.radical v⁆
  intro heq
  have hattach := three_shift_nonnormalized_attachment_escape_knownSimple hb hcard p q r t hnorm
  have hc32 : Nat.card (replacementMoved d)=32 := by
    rcases moved_card s with h16|h32
    · have hz := moving_attachment_zero_of_sixteen s hc h16 r.path.end_color
      exact (hattach (hz ▸ bot_le)).elim
    · exact h32
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hsmall : (Q d.radical v).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have htcol : color d.radical t.edge=true := by
    have hh := adjacent_color_ne d.radical t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color d.radical t.edge <;> simp_all
  have hAt : Z d.radical v ≤ Q d.radical t.edge := by
    rw [←t.first]
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v t.path.end_color)
    rw [SimpleGraph.dist_comm,t.path.dist_end,(replacementGeometry h d).distance_constant _ t.path.end_color]
    have hl : t.path.walk.length=replacementDistance h d := t.path.length_eq_b
    change t.path.walk.length-1 < replacementDistance h d
    omega
  have hFt : F ≤ Q d.radical t.edge := inf_le_right.trans (Q_le_adjacent_h d.radical htcol t.adjacent_start)
  have hFv : F ≤ Q d.radical v := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z r.path.end_color)
    rw [(replacementGeometry h d).distance_constant _ r.path.end_color,SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length=replacementDistance h d := r.path.length_eq_b
    change r.path.walk.length-(r.path.walk.length-2) < replacementDistance h d
    omega
  have hzero := critical_fixed_line_zero_of_cover32 s hc hc32 t.path hsmall
    t.adjacent_shift hAt F hFt hFv heq.le
  have hn := critical_Z_commutator_ne_bot s hc t.path
  exact hn (heq.symm.trans hzero)

include e hz hn in
/-- At distance six, neither terminal line alternative can occur; hence the
actual endpoint seed normalizes the full restricted-kernel join. -/
theorem six_terminal_normalization_knownSimple
    (hb : replacementDistance h d = 6)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  by_contra hn
  exact three_shift_nonnormalized_lines_distinct_knownSimple (by omega) hcard p q r t hn
    (six_nonnormalized_coincident_lines_knownSimple hb hcard p q r t hr hn).1

include e hz hn in
/-- All even distances above four satisfy terminal seed normalization on
an orbit-compatible path in the image-sixteen branch. -/
theorem orbit_terminal_normalization_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  by_cases h6 : replacementDistance h d=6
  · exact six_terminal_normalization_knownSimple h6 hcard p q r t hr
  · have he := replacementDistance_even h d
    rw [Nat.even_iff] at he
    exact (SylowTerminalNormalization.three_shift_normalization_knownSimple
      (by omega) hcard p q r t).2

include e hz hn in
/-- The full omega subgroup normalizes the same literal join at every
large distance; its entire central summand is retained. -/
theorem orbit_terminal_full_omega_normalization_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    X d.radical z ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical v) ⊔ Z d.radical r.start :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let N := K ⊔ Z d.radical r.start
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hd := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hsmall : (Q d.radical z).relIndex (Z d.radical r.start) < 4 := by rw [hd.2.1]; decide
  have htcol : color d.radical t.edge = true := by
    have hh := adjacent_color_ne d.radical t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color d.radical t.edge
    · exact (hh he.symm).elim
    · rfl
  have hzv : (cosetGraph d.radical).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  have hXG : X d.radical z ⊓ Q d.radical r.start ≤ stabilizer d.radical t.start :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical htcol t.adjacent_start)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_shift))
  have hXv : X d.radical z ⊓ Q d.radical r.start ≤ stabilizer d.radical v :=
    ((inf_le_left.trans (omegaCenter_le (Q d.radical z))).trans
      (Q_le_stabilizer_of_dist_two d.radical z v r.path.end_color hzv))
  have hNK : X d.radical z ⊓ Q d.radical r.start ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_inf (hXG.trans (Z_normalized d.radical t.start))
      (hXv.trans (Q_normalized d.radical v))).trans inf_normalizer_le_normalizer_inf
  have hKQ : K ≤ Q d.radical r.start :=
    (inf_le_left.trans (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q (by omega : 2 < replacementDistance h d) r.start r.path.start_color)
  have hvG : Q d.radical v ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_two d.radical v z t.path.end_color
      (SimpleGraph.dist_comm.trans hzv)
  rcases critical_X_generation_or_normalization s hc r.path hsmall K
    (inf_le_right.trans hvG) hKQ hNK with hgen | hnorm
  · have hNG : N ≤ stabilizer d.radical z := sup_le (inf_le_right.trans hvG)
      (Z_le_stabilizer_of_dist_le r.start _ r.path.critical.1.le)
    change X d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical))
    change X d.radical z = _ at hgen
    rw [hgen]
    exact sup_le ((DistanceEight.U_le_Z d.radical z).trans
      (orbit_terminal_normalization_knownSimple hb hcard p q r t hr))
      ((inf_le_right.trans (centralizer_le hNG)).trans (Subgroup.centralizer_le_normalizer _))
  · exact hnorm

include e hz hn in
/-- The whole intermediate core lies in the last small mover, including
critical distance six. -/
theorem orbit_terminal_core_containment_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    Q d.radical r.start ≤
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4 := by
  exact ((SylowTerminalKernel.three_shift_kernel_control_knownSimple hb hcard p q r t).2.2.2.2.1
    (orbit_terminal_normalization_knownSimple hb hcard p q r t hr)).1

include e hz hn in
/-- The original radical constructs an orbit-compatible chain, discharging
terminal normalization and the whole intermediate-core containment at every
distance greater than four in the order-sixteen radical-image branch. -/
theorem original_radical_orbit_terminal_normalization_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q₀ : BackwardShift (h := h) p,
      act d.radical q₀.transporter (beta d.radical) = q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom = Q d.radical q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      ∃ c c', ∃ v₀ : CriticalPath d.radical (replacementGeometry h d) c c',
      SylowTerminalPath.ShiftChain (h := h) q₀.path v₀ (replacementDistance h d) ∧
      ∃ (q : BackwardShift (h := h) v₀) (r : BackwardShift (h := h) q.path)
        (t : BackwardShift (h := h) r.path),
      SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d) ∧
      let z := q.path.walk.getVert (q.path.walk.length-2)
      let v := r.path.walk.getVert (r.path.walk.length-2)
      let N := (Z d.radical t.start ⊓ Q d.radical v) ⊔ Z d.radical r.start
      Z d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical)) ∧
      X d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical)) ∧
      Q d.radical r.start ≤
        SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4 := by
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',v₀,hchain,q,r,t,hr,_hspan,_hdisjoint,
      _hindex,_hcentral_t,_hcentral_z,_hcentral_all,_hnon⟩ :=
    SylowTerminalPath.original_radical_terminal_path_knownSimple hb hcard p hfirst
  exact ⟨q₀,hqe,hqT,hqgen,c,c',v₀,hchain,q,r,t,hr,
    orbit_terminal_normalization_knownSimple hb hcard v₀ q r t hr,
    orbit_terminal_full_omega_normalization_knownSimple hb hcard v₀ q r t hr,
    orbit_terminal_core_containment_knownSimple hb hcard v₀ q r t hr⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
