module
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Alignment
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Configurations
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CoreDisplacement

/-!
# The original section Sylow at a reselected involution centralizer

Choose an actual section-centralizer Sylow containing the pushing-up radical.
Its intersection with the outside overgroup, and hence with the full
involution centralizer, is exactly that radical. Sylow conjugacy marks it
as the core of a conjugate of the original LT, recording the conjugator
inside the original section centralizer and the original module inclusion.

The Chapter 12 Hermitian consumer constructs the reselected overgroup.
The proof-only import reuses the generic Sylow intersection theorem while
keeping the homonymous Mathieu and rank-one chapter exports separate.
No Mathieu model assumption is used.
Source: Aschbacher--Smith 4.1.4 and 4.2.13, printed pp.607,611--612,
as used in 8.2.7, p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

include D in
/-- Actual Sylow placement, original Sylow alignment and the full
involution-centralizer kernel for a literal reselected source witness. -/
theorem sourceOrbit_hermitian_involution_section_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (r : G) (hRr : J.pCoreIn 2 ≤ centralizer ({r} : Set G))
    (hCH : centralizer ({r} : Set G) ≤ H) :
    ∃ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
      let Pg := (P : Subgroup _).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
      J.pCoreIn 2 ≤ Pg ∧ Pg ⊓ H = J.pCoreIn 2 ∧
        Pg ⊓ centralizer ({r} : Set G) = J.pCoreIn 2 ∧
        ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
          ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom = Pg ∧
          (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2 = Pg ∧
          V.map (MulAut.conj (c : G)).toMonoidHom ≤ Chapter4.Section02.Unitary.fullModule L Pg := by
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have huniq : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  have hyp := source_hypothesis411 h huniq
  let C := sectionCentralizerIn (normalizer (L : Set G)) L
  let Mminus := coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)
  have hs : Mminus ∈ sigma (normalizer (L : Set G)) L := by
    refine ⟨sup_le (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
      inf_le_left,sup_le ?_ le_sup_right⟩
    intro l hl
    obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
    exact Mminus.mul_mem (hw.1.1.1.1 hj)
      ((show C ≤ Mminus from le_sup_right) (componentCore_le_sectionCentralizer L.le_normalizer hq))
  have hRC := core_le_sectionCentralizer_of_eta hyp.plus_le hyp.plus_normal hyp.plus_perfect hs.1 hw.1.1.1
  obtain ⟨P,hRP⟩ := ((isPGroup_pCoreIn 2 J).comap_subtype :
    IsPGroup 2 ((J.pCoreIn 2).subgroupOf C)).exists_le_sylow
  have hRPg : J.pCoreIn 2 ≤ (P : Subgroup C).map C.subtype := by
    intro x hx
    exact ⟨⟨x,hRC hx⟩,hRP hx,rfl⟩
  obtain ⟨c,hc,hVc⟩ := Chapter4.Section02.Unitary.exists_fullModule_comparison h D huniq P
  refine ⟨P,hRPg,D.sourceOrbit_pushingUp_sectionSylow_intersection h hw P hRPg,
    D.sourceOrbit_pushingUp_sectionSylow_centralizer h hw r hRr hCH P hRPg,c,hc,?_,hVc⟩
  exact (aligned_sylow_core hyp.plus_perfect D.sylow_normalizes_component c).1.trans hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
