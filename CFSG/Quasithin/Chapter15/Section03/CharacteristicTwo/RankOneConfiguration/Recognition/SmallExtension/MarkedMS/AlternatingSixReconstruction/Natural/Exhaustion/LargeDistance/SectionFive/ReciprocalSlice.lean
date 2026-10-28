module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ForwardSlice

/-!
# Reciprocal slices and the selected critical commutator

The starting cover of any critical path is outside the Baumann subgroup
at its second vertex. Otherwise the full seed lies in that slice; the
component and incident edge kernel then normalize its product with the
second vertex's omega-center. This contradicts source (2.2)(iv)'s forward
nonnormality. The conclusion keeps the full seed and both cover orders.

A nonabelian selected span supplies a reciprocal critical path through the
same first edge and original start. Applying the preceding result to both
paths proves that both reciprocal slices have index at least two. With
the original small-image and forward-slice bounds, the known derived-line
calculation identifies the reciprocal critical commutator with the entire
selected derived subgroup and original forward line. Projection of its
movement to the natural quotient, together with the symplectic pairing,
forces both reciprocal full seed images to have order two. The same line
is central at the prescribed midpoint and noncentral at both endpoints.
No complement to the order-32 cover's central kernel is chosen.

These are actual-path applications toward MS93 (5.8)--(5.12), using the
forward nonnormality of (2.2)(iv), printed pp.856--857, the small critical
module calculation of (3.3), and the selected spans on pp.920--927.
The nonabelian span and upper slice bound remain explicit source premises;
the constructed endpoint line is not an identification of the intermediate
R4 or R6 in (5.11). Source-selected backward shifts, exact-four radius
exclusion, intermediate noncentrality, both terminal contradictions and
largeDistance_knownSimple remain with
qt-e-ms-small-a6-exhaustion-large-distance. The independent whole-core
reconstruction remains with qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include h in
private theorem core_residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

private theorem normalizes_join_of_displacement {G : Type*} [Group G]
    (N H K : Subgroup G) (hn : K≤normalizer (N:Set G))
    (hcomm : ⁅K,H⁆≤N) : K≤normalizer ((N⊔H:Subgroup G):Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (N⊔H).map (MulAut.conj k).toMonoidHom≤N⊔H := by
    rw [Subgroup.map_sup]
    refine sup_le ((mem_normalizer_iff_map_conj_eq.mp (hn hk)).le.trans le_sup_left) ?_
    rintro _ ⟨y,hy,rfl⟩
    have hh := (N⊔H).mul_mem
      (mem_sup_left (hcomm (commutator_mem_commutator hk hy))) (mem_sup_right hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)

include s in
private theorem cover_small_commutator_image (A : Subgroup d.overgroup)
    (hcard : Nat.card (⁅replacementMoved d,A⁆ : Subgroup d.overgroup) ≤ 2) :
    Nat.card (A.map s.projection) ≤ 2 := by
  let := replacementMoved_normal h d
  let : IsElementaryAbelian 2 (⁅replacementMoved d,A⁆ : Subgroup d.overgroup) :=
    IsElementaryAbelian.of_le (commutator_le_left (replacementMoved d) A)
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  let D := subspaceCommutator (coverAction s) ⊤ (A.map s.projection)
  have hDcard : Nat.card D ≤ 2 := by
    have he := Nat.card_congr (NormalElementaryQuotient.movedEquiv
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) A).toEquiv
    change Nat.card (⁅replacementMoved d,A⁆ : Subgroup d.overgroup) = Nat.card D at he
    rwa [←he]
  have hDdim : Module.finrank (ZMod 2) D ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hDcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hDcard
  have hm : D.map π = subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
      (A.map s.projection) := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id (Equiv.Perm (Fin 6))) π
      (fun g v => (coverMap_equivariant s g v).symm) (A.map s.projection) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (coverMap_surjective
      (h := h) (e := e) (hz := hz) (hn := hn) (d := d)),Subgroup.map_id] at hh
    exact hh.symm
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 := by
    rw [←Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.moved_finrank_eq_fixedCodim,←hm]
    exact (Submodule.finrank_map_le π D).trans hDdim
  by_cases he : A.map s.projection = ⊥
  · rw [he,card_bot]; decide
  · obtain ⟨t,_,ht,he⟩ :=
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
        (A.map s.projection) he hnat
    rw [he,Nat.card_zpowers,ht.orderOf]

include s in
/-- A critical commutator of order at most two forces both full seed
images to have order two. The proof projects movement to the natural
quotient; it does not identify the full cover with that quotient. -/
theorem critical_indices_two_of_commutator_card (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hcard : Nat.card (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2) :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a' p.end_color
  have hA : Z d.radical a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  let A := (Z d.radical a).comap i
  have hmA : A.map i = Z d.radical a := map_comap_eq_self hA
  let := finite_Z d.radical a
  let : Finite (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a))) (inclusion_injective _)
  have hcomm : ⁅U d.radical a',Z d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm (Z d.radical a)]
    exact commutator_mono (DistanceEight.U_le_Z d.radical a') le_rfl
  have hsmall : Nat.card (⁅replacementMoved d,A⁆ : Subgroup d.overgroup) ≤ 2 := by
    rw [←card_map_of_injective hi,map_commutator,hiU,hmA]
    exact (card_le_of_le hcomm).trans hcard
  have hidx := cover_small_commutator_image s A hsmall
  rw [←relIndex_ker,s.projection_kernel,←relIndex_map_map_of_injective _ _ hi,hiQ,hmA] at hidx
  exact small_critical_indices s hc p (by omega)

include s in
/-- The starting moved cover escapes the Baumann subgroup at the second
vertex of every actual critical path. This is the forward nonnormality
argument of MS93 (2.2)(iv), with the original central cover retained. -/
theorem critical_start_not_le_second_slice (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ¬ U d.radical a ≤ B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hpos : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a p.start_color) := by
    rw [(replacementGeometry h d).distance_constant a p.start_color]
    exact replacementDistance_pos h d
  have hac : (cosetGraph d.radical).dist a c = 2 := p.dist_start (by omega)
  have hpath : (cosetGraph d.radical).dist c a' + 2 = (cosetGraph d.radical).dist a a' := by
    rw [p.dist_end,←p.shortest]
    omega
  have hn := (critical_nonnormal_forward d.radical (replacementGeometry h d)
    (edgeCentralizerCondition s hc) a p.start_color hpos a' p.critical c hac hpath).2
  intro hU
  have hZB : Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.start_color hat]
    exact sup_le hU ((adjacent_Z_le d.radical hcol hct).trans
      (Escape.EdgeTransfer.Z_le_B hb c hcol))
  have hZX : Z d.radical c ≤ X d.radical c :=
    Z_le_X_of_positive d.radical c hcol ((replacementGeometry h d).exists_critical c hcol)
      (by rw [(replacementGeometry h d).distance_constant c hcol]; exact replacementDistance_pos h d)
  apply hn
  apply normal_subgroupOf_of_le_normalizer
  rw [←core_residual_edge_generation (h := h) hcol hct,sup_comm (Z d.radical a) (X d.radical c)]
  apply sup_le
  · apply normalizes_join_of_displacement
    · exact (Ltilde_le_stabilizer c).trans (X_normalized d.radical c)
    · apply commutator_le.mpr
      intro l hl z hz
      exact hZX (((mem_B_iff d.radical c _
        ((replacementGeometry h d).V_local c hcol (by
          rw [(replacementGeometry h d).distance_constant c hcol]; exact hb)) z).mp (hZB hz)).2 l hl)
  · have htG : Q d.radical t ≤ stabilizer d.radical a :=
      fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
    have htC : Q d.radical t ≤ stabilizer d.radical c :=
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
    exact (le_inf (htC.trans (X_normalized d.radical c))
      (htG.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

include s in
/-- The reciprocal slice on the literal critical path has index at least
two, without a backward-escape or natural-subgroup hypothesis. -/
theorem critical_start_slice_index_two_le (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 ≤ (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a) := by
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  have hpos : 0 < (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a) ≠ 1 :=
    fun he => critical_start_not_le_second_slice s hc hb p (relIndex_eq_one.mp he)
  omega

/-- The nonabelian orbit-span construction produces a literal reciprocal
critical path through the same first edge. Both forward slices are eligible;
no separate eligibility premise remains. -/
theorem selected_span_reciprocal_paths_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    replacementDistance h d = 4 ∧
      2 ≤ (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      2 ≤ (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (alpha d.radical)) ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
          (p.walk.getVert 2) (act d.radical x (p.walk.getVert 2)),
          q.walk.getVert 1 = p.walk.getVert 1 ∧
          q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = act d.radical x (p.walk.getVert 1) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨hfour,x,hx,q,hq1,hq2,hq3⟩ := selected_span_conjugate_critical_path (h := h) hb p hnonabelian
  have hforward := critical_start_slice_index_two_le s hc hb q
  rw [hq2] at hforward
  exact ⟨hfour,hforward,critical_start_slice_index_two_le s hc hb p,x,hx,q,hq1,hq2,hq3⟩

/-- On the constructed reciprocal path, the critical commutator is exactly
the original selected span's derived subgroup and forward line. Both full
critical images have order two, and the line is central at the prescribed
midpoint but noncentral at both endpoints. All three intermediate vertices
retain the original first edge and the same conjugator. -/
theorem selected_span_reciprocal_critical_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    let c := p.walk.getVert 2
    let P := localZSpan d.radical c (alpha d.radical)
    let H := ⁅U d.radical c,Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆
    replacementDistance h d = 4 ∧
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) = 2 ∧
      2 ≤ (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (alpha d.radical)) ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical x c),
          q.walk.getVert 1 = p.walk.getVert 1 ∧
          q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = act d.radical x (p.walk.getVert 1) ∧
          (Q d.radical (act d.radical x c)).relIndex (Z d.radical c) = 2 ∧
          (Q d.radical c).relIndex (Z d.radical (act d.radical x c)) = 2 ∧
          ⁅Z d.radical c,Z d.radical (act d.radical x c)⁆ = ⁅P,P⁆ ∧
          ⁅P,P⁆ = H ∧ Nat.card H = 2 ∧
          H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
          ¬ H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) ∧
          ¬ H ≤ centralizer (stabilizer d.radical (act d.radical x c) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  obtain ⟨hfour,hlo,hopp,x,hx,q,hq1,hq2,hq3⟩ :=
    selected_span_reciprocal_paths_knownSimple (e := e) (hz := hz) (hn := hn) hb p hnonabelian
  have hderived := small_selected_span_derived_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hslice hnonabelian
  have hZP : Z d.radical c ≤ P := Z_le_localZSpan d.radical _ _
  have hxP : Z d.radical (act d.radical x c) ≤ P := by
    rw [Z_act]
    exact (map_mono hZP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical c (alpha d.radical)
        ((stabilizer d.radical (alpha d.radical)).inv_mem hx)))
  let D := ⁅Z d.radical c,Z d.radical (act d.radical x c)⁆
  have hDP : D ≤ ⁅P,P⁆ := commutator_mono hZP hxP
  let := finite_stabilizer d.radical (alpha d.radical)
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,p.dist_start (by have hl : p.walk.length = replacementDistance h d := p.length_eq_b; omega)])).trans
      ((replacementGeometry h d).V_local _ rfl hb)
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup P P).trans (sup_le hPG hPG))) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDP) (inclusion_injective _)
  have hDcard : Nat.card D ≤ 2 := (card_le_of_le hDP).trans_eq hderived.2.1
  have hDpos := (one_lt_card_iff_ne_bot D).mpr (critical_Z_commutator_ne_bot s hc q)
  have hDeq : D = ⁅P,P⁆ := eq_of_le_of_card_ge hDP (by
    have hh : Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := hderived.2.1
    omega)
  have hindices := critical_indices_two_of_commutator_card s hc q hDcard
  have hnonStart := critical_commutator_not_central s hc q
  let qr : CriticalPath d.radical (replacementGeometry h d) (act d.radical x c) c :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc q⟩
  have hnonEnd := critical_commutator_not_central s hc qr
  rw [commutator_comm (Z d.radical (act d.radical x c))] at hnonEnd
  change ¬ D ≤ _ at hnonStart hnonEnd
  rw [hDeq,hderived.1] at hnonStart hnonEnd
  refine ⟨hfour,by omega,hopp,x,hx,q,hq1,hq2,hq3,hindices.1,hindices.2,
    hDeq,hderived.1,?_,?_,hnonStart,hnonEnd⟩
  · rw [←hderived.1]
    exact hderived.2.1
  · rw [←hderived.1]
    exact hderived.2.2


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
