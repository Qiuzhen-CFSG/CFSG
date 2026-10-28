module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.AttachmentMovement

public import Theory.GroupTheory.ClassTwoCommutator

/-!
# The derived line of the selected common kernel

At distance four with the literal full point-core image, let P be the
span of the midpoint seed under the starting stabilizer. When P is
nonabelian, its intersection Y with the midpoint core is exactly the
centralizer in P of the whole midpoint moving cover, and has index two.

The earlier derived bound and faithful S₆ action on P/Z(P) show that Y
is nonabelian. Indeed, an abelian index-two subgroup in a class-two
group with derived group of order at most two would give center index
at most four. The faithful S₆ action excludes that size. Consequently
Y and P have the same derived line. The full midpoint moving layer
also has centralizer index two against P and its commutator with P is
that same line.

The actual large-slice application supplies nonabelianness internally.
Its common-kernel derived line is centralized by the starting stabilizer
and is noncentral at the midpoint, as witnessed by the constructed
reciprocal critical path. It lies in the derived subgroup of the whole
midpoint two-core; this is a containment, not an upper bound on that
whole core or its residual commutator.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank
two* (1993), the selected class-two transfer in (3.10) and (5.12),
printed pp.880--881 and 924--927. This calculation retains the original
replacement graph, both moving covers and all central attachments.
Selecting two small slices, the endpoint and opposite-residual-core
estimates, the other radical-image branches and unconditional distance
two remain unproved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

private theorem center_index_le_four_of_abelian_index_two
    {F : Type*} [Group F] [Finite F] (A : Subgroup F)
    [IsMulCommutative A] (hi : A.index = 2)
    (hc : _root_.commutator F ≤ center F)
    (hd : Nat.card (_root_.commutator F) ≤ 2) :
    (center F).index ≤ 4 := by
  classical
  obtain ⟨x,hx⟩ : ∃ x : F, x ∉ A := by
    by_contra! hn
    have he : A = ⊤ := top_unique (fun x _ => hn x)
    rw [he,index_top] at hi
    omega
  have hgen : A ⊔ zpowers x = ⊤ := by
    have hs : A < A ⊔ zpowers x := lt_of_le_of_ne le_sup_left (by
      intro he
      exact hx (he ▸ (mem_sup_right (mem_zpowers x) : x ∈ A ⊔ zpowers x)))
    have hh := index_strictAnti hs
    have hp := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := A ⊔ zpowers x))
    exact index_eq_one.mp (by omega)
  have hz : A ⊓ centralizer ({x} : Set F) ≤ center F := by
    rintro z ⟨hz,hzx⟩
    have hA : A ≤ centralizer ({z} : Set F) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (A.le_centralizer hz a ha)
    have hX : zpowers x ≤ centralizer ({z} : Set F) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hzx).symm)
    have ht : (⊤ : Subgroup F) ≤ centralizer ({z} : Set F) := by
      rw [←hgen]
      exact sup_le hA hX
    exact mem_center_iff.mpr (fun g => mem_centralizer_singleton_iff.mp (ht (mem_top g)))
  have hcx : (centralizer ({x} : Set F)).index ≤ 2 := by
    rw [Subgroup.ClassTwo.centralizer_index hc x]
    exact (card_le_of_le (commutator_mono le_top le_rfl)).trans hd
  exact (index_antitone hz).trans (index_inf_le.trans
    (by simpa only [hi] using Nat.mul_le_mul_left 2 hcx))

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem moving_centralizer_at
    (hc : DistanceTwo.CentralLayer d) {c : Vertex d.radical}
    (hcol : color d.radical c = false) :
    stabilizer d.radical c ⊓ centralizer
      (U d.radical c : Set (FreeAmalgam d.radical)) = Q d.radical c := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  apply le_antisymm
  · rintro x ⟨hx,hxc⟩
    obtain ⟨m,rfl⟩ := hir ▸ hx
    rw [←hiQ]
    apply mem_map_of_mem
    rw [←moved_centralizer s]
    intro v hv
    apply hi
    simpa only [map_mul] using hxc (i v) (hiU ▸ mem_map_of_mem i hv)
  · apply le_inf (fun _ hx => hx.1)
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c hcol))).trans
        (centralizer_le (DistanceEight.U_le_Z d.radical c))

include s in
private theorem selected_span_midpoint_centralizer
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    P ⊓ centralizer (U d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) =
      P ⊓ Q d.radical (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hdist : (cosetGraph d.radical).dist (alpha d.radical) c = 2 :=
    p.dist_start (by omega)
  have hPG : P ≤ stabilizer d.radical c :=
    ((localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hdist])).trans
      (V_le_Q d.radical rfl hb)).trans
        (Q_le_stabilizer_of_dist_two d.radical _ _ rfl hdist)
  change P ⊓ centralizer (U d.radical c : Set (FreeAmalgam d.radical)) = P ⊓ Q d.radical c
  rw [←moving_centralizer_at s hc hcol,←inf_assoc,inf_eq_left.mpr hPG]

include s in
private theorem selected_span_not_le_midpoint_core
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    ¬ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤
      Q d.radical (p.walk.getVert 2) := by
  obtain ⟨_,x,hx,q,_,_,_⟩ := selected_span_conjugate_critical_path (h := h) hb p hnon
  intro hP
  apply (critical_reverse_pair s hc q).2
  apply le_trans _ hP
  rw [Z_act]
  exact ((map_mono (Z_le_localZSpan d.radical _ _)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical _ _
      ((stabilizer d.radical (alpha d.radical)).inv_mem hx))))

/-- The midpoint core cuts every nonabelian selected span in its exact
index-two centralizer of the full moving cover. -/
theorem full_point_four_selected_centralizer_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    P ⊓ centralizer (U d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) =
      P ⊓ Q d.radical (p.walk.getVert 2) ∧
    (Q d.radical (p.walk.getVert 2)).relIndex P = 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hl := p.length_eq_b.trans hb; omega)])
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective
    (inclusion (hPV.trans ((V_le_Q d.radical rfl (by omega : 2 < replacementDistance h d)).trans
      (fun _ hx => hx.1)))) (inclusion_injective _)
  have hi : (Q d.radical (p.walk.getVert 2)).relIndex P ≤ 2 :=
    full_point_four_selected_span_index_knownSimple hb u hfull p
  have hnQ := selected_span_not_le_midpoint_core s hc (by omega) p hnon
  have hp : 0 < (Q d.radical (p.walk.getVert 2)).relIndex P :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : (Q d.radical (p.walk.getVert 2)).relIndex P ≠ 1 := mt relIndex_eq_one.mp hnQ
  have he : (Q d.radical (p.walk.getVert 2)).relIndex P = 2 := by omega
  exact ⟨selected_span_midpoint_centralizer s hc (by omega) p,he⟩


/-- The common midpoint kernel of a nonabelian selected span has the
same nontrivial derived line as that whole span. -/
theorem full_point_four_selected_kernel_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let Y := P ⊓ Q d.radical (p.walk.getVert 2)
    ⁅Y,Y⁆ = ⁅P,P⁆ ∧ Nat.card (⁅Y,Y⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let Y := P ⊓ Q d.radical c
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hl := p.length_eq_b.trans hb; omega)]
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical hdist).trans ((V_le_Q d.radical rfl hb2).trans (fun _ hx => hx.1))
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hD := full_point_four_selected_span_derived_bound_knownSimple hb u hfull p
  change Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
    ⁅P,P⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) at hD
  have hm : (_root_.commutator P).map P.subtype = ⁅P,P⁆ := P.map_subtype_commutator
  have hDc : _root_.commutator P ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hD.2 (hm ▸ mem_map_of_mem P.subtype hx) y (hPG y.property)
  have hDcard : Nat.card (_root_.commutator P) ≤ 2 := by
    rw [←card_map_of_injective P.subtype_injective,hm]
    exact hD.1
  have hlarge : 4 < (center P).index := by
    let ρ := selectedSpanSymmetricAction s hc hb2 c hdist
    have hρ := selected_span_symmetric_action_injective s hb2 p hnon ρ
      (selectedSpanSymmetricAction_projection s hc hb2 c hdist)
    have hi := Nat.card_le_card_of_injective (f := fun g => (ρ g).toEquiv)
      (MulEquiv.toEquiv_injective.comp hρ)
    change Nat.card (Equiv.Perm (Fin 6)) ≤ Nat.card (Equiv.Perm (P ⧸ center P)) at hi
    rw [Nat.card_perm,Nat.card_fin,Nat.card_perm] at hi
    rw [index_eq_card]
    by_contra hn
    have hh := Nat.factorial_le (show Nat.card (P ⧸ center P) ≤ 4 by omega)
    have hs : Nat.factorial 6 = 720 := rfl
    have ht : Nat.factorial 4 = 24 := rfl
    omega
  have hYle : Y ≤ P := inf_le_left
  let A := Y.subgroupOf P
  have hi : A.index = 2 := by
    change Y.relIndex P = 2
    rw [inf_relIndex_left]
    exact (full_point_four_selected_centralizer_knownSimple hb u hfull p hnon).2
  have hne : ⁅Y,Y⁆ ≠ ⊥ := by
    intro he
    let : IsMulCommutative A := by
      apply commutator_self_eq_bot_iff.mp
      apply ((⁅A,A⁆ : Subgroup P).map_eq_bot_iff_of_injective P.subtype_injective).mp
      rw [map_commutator,map_subgroupOf_eq_of_le hYle,he]
    exact (Nat.not_le_of_gt hlarge) (center_index_le_four_of_abelian_index_two A hi hDc hDcard)
  have hYY : ⁅Y,Y⁆ ≤ ⁅P,P⁆ := commutator_mono hYle hYle
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion ((Subgroup.commutator_le_sup P P).trans (sup_le hPG hPG))) (inclusion_injective _)
  let : Finite (⁅Y,Y⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hYY) (inclusion_injective _)
  have hlo := (one_lt_card_iff_ne_bot (⁅Y,Y⁆ : Subgroup (FreeAmalgam d.radical))).mpr hne
  have hup := (card_le_of_le hYY).trans hD.1
  have heq : ⁅Y,Y⁆ = ⁅P,P⁆ := eq_of_le_of_card_ge hYY (by omega)
  have hcardY : Nat.card (⁅Y,Y⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by omega
  exact ⟨heq,hcardY⟩

/-- The full midpoint moving layer has a line as image in the selected
span's central quotient. Its commutator with the span is the same derived line. -/
theorem full_point_four_selected_moving_line_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    (centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical (p.walk.getVert 2)) = 2 ∧
      ⁅U d.radical (p.walk.getVert 2),P⁆ = ⁅P,P⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hdist : (cosetGraph d.radical).dist (alpha d.radical) c = 2 := p.dist_start (by omega)
  have hPQ : P ≤ Q d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hdist])).trans
      (V_le_Q d.radical rfl hb2)
  have hPG : P ≤ stabilizer d.radical c := hPQ.trans
    (Q_le_stabilizer_of_dist_two d.radical _ _ rfl hdist)
  have hUP : U d.radical c ≤ P := (DistanceEight.U_le_Z d.radical c).trans
    (Z_le_localZSpan d.radical _ _)
  have hle : ⁅U d.radical c,P⁆ ≤ ⁅P,P⁆ := commutator_mono hUP le_rfl
  have hPD := full_point_four_selected_span_derived_bound_knownSimple hb u hfull p
  change Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
    ⁅P,P⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) at hPD
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion ((Subgroup.commutator_le_sup P P).trans
      (sup_le (hPQ.trans (fun _ hx => hx.1)) (hPQ.trans (fun _ hx => hx.1))))) (inclusion_injective _)
  let : Finite (⁅U d.radical c,P⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hcard : Nat.card (⁅U d.radical c,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 :=
    (card_le_of_le hle).trans hPD.1
  have hnC : ¬ U d.radical c ≤ centralizer (P : Set (FreeAmalgam d.radical)) := by
    intro hh
    have hPfix := le_centralizer_iff.mp hh
    have hPQmid : P ≤ Q d.radical c := by
      have he := selected_span_midpoint_centralizer s hc hb2 p
      change P ⊓ centralizer (U d.radical c : Set (FreeAmalgam d.radical)) = P ⊓ Q d.radical c at he
      rw [inf_eq_left.mpr hPfix] at he
      exact he.le.trans inf_le_right
    exact selected_span_not_le_midpoint_core s hc hb2 p hnon hPQmid
  have hne : ⁅U d.radical c,P⁆ ≠ ⊥ := fun he =>
    hnC (commutator_eq_bot_iff_le_centralizer.mp he)
  have hlo := (one_lt_card_iff_ne_bot (⁅U d.radical c,P⁆ : Subgroup (FreeAmalgam d.radical))).mpr hne
  have heq : ⁅U d.radical c,P⁆ = ⁅P,P⁆ := eq_of_le_of_card_ge hle (by omega)
  have hi := moving_small_commutator_fixed_index s hc hcol P hPG hcard
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hp : 0 < (centralizer (P : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hni := mt relIndex_eq_one.mp hnC
  have hidx : (centralizer (P : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) = 2 := by omega
  exact ⟨hidx,heq⟩

/-- In the large-slice branch the common midpoint kernel is nonabelian,
and its derived line is central at the start but contained in the whole
midpoint core's derived subgroup. No bound on that whole core is inferred. -/
theorem full_point_four_large_slice_kernel_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let Y := P ⊓ Q d.radical (p.walk.getVert 2)
    ⁅Y,Y⁆ = ⁅P,P⁆ ∧ Nat.card (⁅Y,Y⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅P,P⁆ ≤ ⁅Q d.radical (p.walk.getVert 2),Q d.radical (p.walk.getVert 2)⁆ ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      (centralizer (P : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical (p.walk.getVert 2)) = 2 ∧
      ⁅U d.radical (p.walk.getVert 2),P⁆ = ⁅P,P⁆ ∧
      ¬ ⁅Y,Y⁆ ≤ centralizer
        (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  have hder := full_point_four_large_slice_derived_knownSimple hb u hfull p hlarge
  have hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
    intro he
    have hh := hder.2.1
    rw [he,card_bot] at hh
    omega
  have hh := full_point_four_selected_kernel_derived_knownSimple hb u hfull p hnon
  have hm := full_point_four_selected_moving_line_knownSimple hb u hfull p hnon
  refine ⟨hh.1,hh.2,?_,hder.2.2,hm.1,hm.2,?_⟩
  · rw [←hh.1]
    exact commutator_mono inf_le_right inf_le_right
  · rw [hh.1]
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
    obtain ⟨_,x,hx,q,_,_,_⟩ := selected_span_conjugate_critical_path (h := h) (by omega) p hnon
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    have hzP : Z d.radical (act d.radical x (p.walk.getVert 2)) ≤ P := by
      rw [Z_act]
      exact ((map_mono (Z_le_localZSpan d.radical _ _)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical _ _
          ((stabilizer d.radical (alpha d.radical)).inv_mem hx))))
    intro hcentral
    exact critical_commutator_not_central s hc q
      ((commutator_mono (Z_le_localZSpan d.radical _ _) hzP).trans hcentral)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
