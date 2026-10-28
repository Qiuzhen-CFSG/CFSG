module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicRadical
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSingleFactorSource

/-!
# The order-four pairing restriction on the original minimal witness

Apply the radical-kernel argument after the established full-action and
singleton exclusions. Minimality identifies the normal five-core lift
with the same original local I. All calculations keep its original
quotient action. The selected endpoint, its actor and canonical factor remain the ones
from the simultaneous-cubic construction.

The resulting necessary condition retains the normal two-perfect lift,
its full two-core quotient kernel, generation of I, and escape from M.
Both original pairing quotients have order four, and a fixed-witness
corollary allows subsequent arguments to keep their existing coordinates.
The ambient exclusion of this configuration, five-core vanishing and
the later reductions through 14.7.52 remain to be proved.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045,
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- On the original minimal five-core obstruction, the remaining cubic
branch forces the full two-core pairing quotient to have order four.
The normal two-perfect lift, its full quotient kernel and its escape from
M are preserved; no source-recognition datum or radical hypothesis is used. -/
theorem local_minimal_five_radical_reduction
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = pCore 5 (HStar I) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* pCore 5 (HStar I)) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧ ((F.Li L 1).subgroupOf I).Normal ∧
      IsElementaryAbelian 2 (F.UH I) ∧
      ⁅Y.map I.subtype,F.UH I⁆ ≤ F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G) ∧
      V ⊔ (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)) = F.UH I ∧
      V ⊓ (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)) = F.Vi 1 ∧
      (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)).relIndex (F.UH I) = 4 ∧
      (centralizer (F.UH I : Set G)).relIndex (I.pCoreIn 2) = 4 := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,houtc,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,
      htwo,hcentral,hcentralOpp⟩ :=
    local_minimal_five_simultaneous_cubic h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  obtain ⟨I',X,Y,hI'I,hI',_,hXn,hXp,hcore,hcard,hminX,hYn,hYp,hYle,hYm,hYk,he,
      hout,hgen,hs,hn,hpoint,hm,_⟩ :=
    local_minimal_five_point_normal h hab structural previous I hI hneI
  have hXne : X ≠ ⊥ := by
    intro hz
    rcases hcard with hc | hc <;> rw [hz,card_bot] at hc <;> omega
  have heq : I' = I := by
    by_contra hne'
    exact hXne (hcore.trans (hmin I' hI' (lt_of_le_of_ne hI'I hne')))
  subst I'
  have hb : 3 ≤ hf.b := (local_f9_critical_bounds h hab structural previous I hI).1
  have hBI : c.endpoint.conjugate (F.UH I) ≤ I :=
    (map_mono (conjugateSpanBy_mono hf.plus_le le_rfl)).trans (c.endpoint.large_le hb)
  have hcomm : ⁅I.pCoreIn 2,F.UH I⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact hf.commutator_UH_QH_le_point
  have hZ : F.Vi 1 ≤ centralizer (I : Set G) := le_centralizer_iff.mp hf.H_centralizes
  have hmove := local_minimal_five_lift_radical a hcomm hZ X hcore hminX Y hYm
    (c.endpoint.conjugate (F.UH I)) hBI hcentral f i hAi hAc
  have hsup := local_span_eq_seed_sup_radical h I Y hgen hmove
  have hinter := local_pairing_radical_seed_intersection h I (F.Li_one_le_of_mem_Hz hI) hn hZ
  have hindices := local_cubic_pairing_index_four h I (F.Li_one_le_of_mem_Hz hI) hn hf hsup
  refine ⟨I,Y,hIJ,hI,hneI,hmin,hYn,hYp,hYm.trans hcore,hYk,?_,hout,hgen,hs,hn,hU,
    hmove,hsup,hinter,hindices⟩
  exact ⟨he.some.trans (MulEquiv.subgroupCongr hcore)⟩

/-- The numerical restriction holds on any fixed original minimal witness,
so later arguments can reuse its own action and quotient coordinates. -/
theorem local_minimal_five_pairing_index
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar I) ≠ ⊥)
    (hmin : ∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
      pCore 5 (HStar E) = ⊥) :
    (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)).relIndex (F.UH I) = 4 ∧
      (centralizer (F.UH I : Set G)).relIndex (I.pCoreIn 2) = 4 := by
  obtain ⟨I',Y,hI'I,hI',hne',_,_,_,_,_,_,_,_,_,_,_,_,_,_,hindices⟩ :=
    local_minimal_five_radical_reduction h hab structural previous faithful I hI hne
  have he : I' = I := by
    by_contra hh
    exact hne' (hmin I' hI' (lt_of_le_of_ne hI'I hh))
  exact he ▸ hindices

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
