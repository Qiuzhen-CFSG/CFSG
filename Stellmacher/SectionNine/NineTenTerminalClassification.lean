module

public import Stellmacher.SectionNine.NineTenPredecessorWreathClassification
public import Stellmacher.SectionNine.NineTenPredecessorNoncommutation
public import Stellmacher.SectionNine.NineTenReversedSuppliedPath
public import Stellmacher.SectionNine.NineTenExtractedPredecessor
public import Stellmacher.SectionNine.NineEightNeighborhood
public import Stellmacher.SectionNine.NineTenPreterminalIntersectionContainment
public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration

/-!
# The terminal wreath classification for the retained two-extraction packet

At critical distance at least five, retain both actual geometric extractions,
their prescribed actor and residual conjugator bounds. The terminal module has
order thirty-two, its core quotient is the SL₂(2) wreath C₂ model, and its
intersection with the preterminal module has order eight.

The actual reversed critical path has a transvection in the original
preterminal module. Mutual normalization puts its displacement in the
predecessor/preterminal intersection, which the original (9.4) places in the
first module. The supplied-path (9.5)--(9.7) classification therefore applies
at the predecessor. Cubic two-arc transitivity transports the predecessor,
initial and first vertices simultaneously to the terminal, penultimate and
preterminal vertices; one conjugation preserves all three conclusions.

This is Stellmacher (9.10)(6), printed p.58. The output concerns the original
path and both original extraction packets; neither a coatom nor a selected
factor is transferred from an unrelated reorientation. The normalizer index
and distance-five exclusions are subsequent, separate steps.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem terminal_classification_of_predecessor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hcard : Nat.card (VAt ctx.Γ previous) = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ previous) (QAt ctx.Γ previous) SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = 2^3) :
    let preterminal := ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5 ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a') (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
      Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ preterminal : Subgroup G) = 2^3 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨alignment,halign,_⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment,halign⟩
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreAdj := Γ.adjacent_symm (nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  have hdistinct : cp.a' ≠ preterminal :=
    (nine_five_previous_ne_terminal ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩).symm
  have hpenModel := (lemma_nine_three_ambient ctx hshort penultimate hpenOrbit).1
  obtain ⟨mover,hmovePrevious,_,hmoveFirst⟩ := nine_seven_two_arc_transport ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mp hprevious) cp.firstStep_adj hne
    hterminalAdj hpreAdj hdistinct hpenOrbit hpenModel
  change Γ.act mover previous = cp.a' at hmovePrevious
  let equiv := MulAut.conj mover⁻¹
  have hVprevious : (VAt Γ previous).map equiv.toMonoidHom = VAt Γ cp.a' := by
    rw [← v_act, hmovePrevious]
  have hVfirst : (VAt Γ cp.firstStep).map equiv.toMonoidHom = VAt Γ preterminal := by
    rw [← v_act, hmoveFirst]
  have hGprevious : (GAt Γ previous).map equiv.toMonoidHom = GAt Γ cp.a' := by
    change conjugateBy (stabilizer Γ previous) mover⁻¹ = _
    rw [← stabilizer_act,hmovePrevious]
  have hQprevious : (QAt Γ previous).map equiv.toMonoidHom = QAt Γ cp.a' := by
    rw [← q_act,hmovePrevious]
  refine ⟨?_,?_,?_⟩
  · change Nat.card (VAt Γ cp.a')=2^5
    rw [← hVprevious,Subgroup.card_map_of_injective equiv.injective]
    exact hcard
  · change QuotientIsModel (GAt Γ cp.a') (QAt Γ cp.a') SL2TwoWreathC2
    rw [← hGprevious,← hQprevious]
    obtain ⟨projection,hsurj,hker⟩ := hmodel
    let e := (GAt Γ previous).equivMapOfInjective equiv.toMonoidHom equiv.injective
    refine ⟨projection.comp e.symm.toMonoidHom, hsurj.comp e.symm.surjective, ?_⟩
    ext x
    change e.symm x ∈ projection.ker ↔ (x:G) ∈ (QAt Γ previous).map equiv.toMonoidHom
    rw [hker, Subgroup.mem_map_equiv]
    change (e.symm x:G) ∈ QAt Γ previous ↔ equiv.symm (x:G) ∈ QAt Γ previous
    have heq : (e.symm x:G) = equiv.symm (x:G) := by
      apply equiv.injective
      exact (congrArg Subtype.val (e.apply_symm_apply x)).trans
        (equiv.apply_symm_apply (x:G)).symm
    rw [heq]
  · change Nat.card (VAt Γ cp.a' ⊓ VAt Γ preterminal : Subgroup G)=2^3
    rw [← hVprevious,← hVfirst,← Subgroup.map_inf _ _ _ equiv.injective,
      Subgroup.card_map_of_injective equiv.injective]
    exact hinter



public theorem nine_ten_terminal_wreath_classification
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor)
    (hfirstActors : ∀ b : G, b ∈ VAt ctx.Γ ctx.criticalPath.firstStep → b ∉ firstA0 →
      twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5 ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
        (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
      Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3 := by
  let cp := ctx.criticalPath
  have hlength : 4 < cp.length := hb
  let third := cp.path ⟨3, by omega⟩
  have hthird : IsCriticalPathOffset ctx.Γ cp 3 third :=
    ⟨⟨3, by omega⟩, rfl, rfl⟩
  have hnoncomm := nine_ten_predecessor_noncommutation ctx hb hterminalNot hfirstNot
    neighbor second actor E A0 data hsecond hactorNeighbor hactorComm hnew hneighbor
      hcenters firstActor firstE firstA0 firstData hfirstNew hfirstActors
  obtain ⟨hcritical, hcenterComm, path, hstart, hend, hpathFirst, hpathBack, hadj⟩ :=
    nine_ten_reversed_supplied_path ctx hb neighbor second actor E A0 data
      hsecond hnew hneighbor hcenters hnoncomm
  let penultimate := cp.path ⟨cp.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let predecessor := ctx.Γ.act data.x⁻¹ third
  obtain ⟨hpreG, newActor, hnewActor, hnewNot, hnewCard, hnewIndex⟩ :=
    nine_eight_transvection_of_supplied_critical_path ctx (by omega)
      penultimate predecessor hcritical hcenterComm path hstart hend hadj
  have hnewActor' : newActor ∈ VAt ctx.Γ
      (cp.path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
    simpa [hpathFirst] using hnewActor
  have hpreG' : VAt ctx.Γ
      (cp.path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ GAt ctx.Γ predecessor := by
    simpa [hpathFirst] using hpreG
  have hpredAdj : ctx.Γ.adjacent cp.a predecessor :=
    (nine_ten_extracted_predecessor_alternative ctx.Γ cp (by omega)
      second actor E A0 data hsecond hnew).1
  have hpredW : VAt ctx.Γ predecessor ≤ GeneratedNeighborhoodV ctx.Γ cp.a :=
    nine_eight_v_le_generated_neighborhood ctx.Γ
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hpredAdj)
  have hpreW : GeneratedNeighborhoodV ctx.Γ cp.a ≤
      GAt ctx.Γ (cp.path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) :=
    nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlength cp.a
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (ctx.Γ.adjacent_symm cp.firstStep_adj))
  have hpredPreG : VAt ctx.Γ predecessor ≤
      GAt ctx.Γ (cp.path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := hpredW.trans hpreW
  have hzG : Subgroup.zpowers newActor ≤ GAt ctx.Γ predecessor :=
    (Subgroup.zpowers_le.mpr hnewActor').trans hpreG'
  have hRpred : ⁅VAt ctx.Γ predecessor, Subgroup.zpowers newActor⁆ ≤
      VAt ctx.Γ predecessor := by
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hzG.trans (stabilizer_le_normalizer_v ctx.Γ predecessor))
  have hRpre : ⁅VAt ctx.Γ predecessor, Subgroup.zpowers newActor⁆ ≤
      VAt ctx.Γ (cp.path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hnewActor')).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hpredPreG.trans (stabilizer_le_normalizer_v ctx.Γ
          (cp.path ⟨cp.length - 2,
            Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))))
  have hI := nine_ten_preterminal_intersection_le_first ctx hb
    hterminalNot neighbor second actor E A0 data hactorNeighbor hactorComm hneighbor
      firstActor firstE firstA0 firstData hfirstNew
  have hcontain : ⁅VAt ctx.Γ predecessor, Subgroup.zpowers newActor⁆ ≤
      VAt ctx.Γ cp.firstStep := (le_inf hRpred hRpre).trans hI
  have hcontainPath : ⁅VAt ctx.Γ predecessor, Subgroup.zpowers newActor⁆ ≤
      VAt ctx.Γ (path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
    change path ⟨cp.length - 2, _⟩ = cp.firstStep at hpathBack
    rw [hpathBack]
    exact hcontain
  obtain ⟨hcard, hmodel, hinter⟩ := nine_ten_predecessor_wreath_classification ctx (by omega)
    penultimate predecessor hcritical hcenterComm path hstart hend hadj newActor
      ⟨hnewActor, hnewNot⟩ hnewIndex hcontainPath
  have hinter' : Nat.card (VAt ctx.Γ predecessor ⊓ VAt ctx.Γ cp.firstStep : Subgroup G) = 2^3 := by
    simpa [hpathBack] using hinter
  have hpredNe : predecessor ≠ cp.firstStep := by
    intro heq
    apply hcritical.2
    change ZAt ctx.Γ penultimate ≤ QAt ctx.Γ predecessor
    rw [heq]
    apply critical_minimality ctx.Γ cp
    have hdist := path_distance_le ctx.Γ cp 1 (cp.length - 1) (by omega) (Nat.sub_le _ _)
    rw [cp.path_first] at hdist
    rw [ctx.Γ.distance_symm]
    exact hdist.trans_lt (by omega)
  exact terminal_classification_of_predecessor ctx (by omega) predecessor
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hpredAdj) hpredNe hcard hmodel hinter'

end Stellmacher.SectionNine
