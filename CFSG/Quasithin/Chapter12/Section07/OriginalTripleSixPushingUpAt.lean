module

public import CFSG.Quasithin.Chapter12.Section07.OriginalChosenPointLocal
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCoreJoin
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCommutator
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointSectionCentralizer
public import CFSG.Quasithin.ChapterC.Section02.SourceHypotheses

/-!
# The genuine C.2.8 configuration at the original triple-six point

The actual original chosen module supplies every local field. Its full
commutator with the point residual, normal C-component structure, and exact
two-core of LtQ are already proved on the same subgroups. The pointed
commutant puts the two-section centralizer in C_G(U). The original Q is
Sylow in that full module centralizer, so restriction supplies the precise
Sylow required by C.2.8 without changing the point.

This is the source application of12.2.12(2) in the proof of12.7.5,
Aschbacher--Smith, printed pp.798,840. No C.2.8 field, selected larger
component, ambient recognition result, or local model is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Every original even-orbit vector gives the complete pushing-up
configuration at its literal ambient centralizer. -/
theorem original_tripleSix_pushingUp_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let H := centralizer ({(t : G)} : Set G)
    let Mt := normalizer (K : Set G) ⊓ H
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H Mt Lt Q U := by
  let H := centralizer ({(t : G)} : Set G)
  let M := normalizer (K : Set G)
  let Mt := M ⊓ H
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
  have hTU := ((structural K h).2.2 U D).1
  obtain ⟨hsq,hne,hfit,hQ,hnorm,hcentral,hnU⟩ :=
    original_chosen_point_pushingUp_local h.toHypothesis1221 D hTU t ht
  have hQM : Q ≤ Mt := by simpa only [Mt,M,H,inf_comm] using hQ
  have hfitM : generalizedFitting Mt = pCore 2 Mt := by
    change generalizedFitting (M ⊓ H : Subgroup G) = pCore 2 (M ⊓ H : Subgroup G)
    rw [inf_comm]
    exact hfit
  have hcontrol : (Q.subgroupOf H).characteristicNormalizerClosure ≤ Mt.subgroupOf H := by
    simpa only [Mt,M,H,inf_comm] using hnorm
  have hnormalizer : H ⊓ normalizer (U : Set G) ≤ Mt := by
    simpa only [Mt,M,H,inf_comm] using hnU
  obtain ⟨hn,hcomponent,hquot,hspan⟩ := tripleSixPointResidual_component D a t ht heven
  have hLM : Lt ≤ Mt :=
    (map_subtype_le _).trans (inf_le_inf K.le_normalizer le_rfl)
  obtain ⟨hcomm,hUL⟩ := tripleSixPointCentralizerResidual_commutator D a t ht heven
  have hcore := tripleSixPointResidual_core_join D a t ht heven
  let Y := ChapterA.Section04.twoSectionCentralizer Lt Mt
  have hQY : Q ≤ Y := tripleSixPointResidual_core_le_sectionCentralizer D a t ht heven
  have hYC : Y ≤ centralizer (U : Set G) :=
    tripleSixPoint_twoSectionCentralizer_le h structural D a t ht heven
  obtain ⟨P,hP⟩ := original_chosen_module_centralizer_sylow h.toHypothesis1221 D hTU
  change (P : Subgroup (centralizer (U : Set G))).map
    (centralizer (U : Set G)).subtype = Q at hP
  have hPY : (P : Subgroup (centralizer (U : Set G))) ≤ (inclusion hYC).range := by
    intro c hc
    have hcQ : (c : G) ∈ Q := hP ▸ mem_map_of_mem _ hc
    exact ⟨⟨c,hQY hcQ⟩,rfl⟩
  let S : Sylow 2 Y := P.comapOfInjective (inclusion hYC) (inclusion_injective hYC) hPY
  have hS : (S : Subgroup Y).map Y.subtype = Q := by
    ext g
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hP ▸ mem_map_of_mem (centralizer (U : Set G)).subtype hy
    · intro hg
      obtain ⟨c,hc,rfl⟩ := hP.symm ▸ hg
      exact ⟨⟨c,hQY (hP ▸ mem_map_of_mem _ hc)⟩,hc,rfl⟩
  refine ⟨hsq,isPGroup_pCoreIn 2 _,hQM,inf_le_right,hfitM,hne,hLM,hcomponent,
    ?_,hcontrol,D.ne_bot,D.elementary,?_,?_,?_,hnormalizer⟩
  · rw [hspan]
    exact ⟨S,hS⟩
  · rw [hspan]
    exact hUL
  · rw [hspan]
    exact hcomm
  · rw [hspan,hcore]
    exact hcentral

end CFSG.Quasithin.Chapter12.Section07
