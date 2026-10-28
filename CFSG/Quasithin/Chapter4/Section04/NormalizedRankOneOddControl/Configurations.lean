module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SectionKernel
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ClosureSylow
public import Theory.GroupTheory.PCoreCoverEquiv
public import CFSG.Quasithin.Chapter4.Section04.OddActorLargeComponent
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Models
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The two actual configurations in the normalized odd-local argument

Failure of uniqueness for the fixed residual constructs a maximal pushing-up
pair, its full module and the inclusion-induced isomorphism of two-core
quotients. The chosen module is only embedded in a section-centralizer
conjugate of the full module; no equality of those modules is imposed.

If uniqueness holds and the odd normalizer escapes, generalized-Fitting
detection constructs an outside component moved by the unchanged module.
The complete earlier A/B theorems identify its actual central quotient.
These are reductions for 4.4.3, not exclusions of either configuration.
Source: Aschbacher--Smith, 4.2.12 and 4.4.5--10, pp.610,620--621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G]

/-- The literal maximal pushing-up pair, including the full two-core quotient
and its representative formula. This definition records an output configuration. -/
@[expose] def PushingUpCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G,
    J ∈ muStar (normalizer (L : Set G)) L
      (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
    PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
    H ⊓ normalizer (L : Set G) < H ∧ V ≤ J.pCoreIn 2 ∧
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let MH := H ⊓ normalizer (L : Set G)
    let X := ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy LH MH) H
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H MH LH (J.pCoreIn 2) W ∧
    (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
    (LH.subgroupOf MH).Normal ∧
    V = ⁅V,LH⁆ ∧ V ≤ LH ∧
    (∃ e : (LH ⧸ pCore 2 LH) ≃* (L ⧸ pCore 2 L),
      ∀ i : LH, e (QuotientGroup.mk' (pCore 2 LH) i) =
        QuotientGroup.mk' (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_left) i)) ∧
    pPrimeCore 2 H = ⊥ ∧ IsPRadical 2 ((J.pCoreIn 2).subgroupOf H) ∧
    ChapterC.IsSylowInNormalClosure (J.pCoreIn 2) MH ∧
    generalizedFitting X = pCore 2 X ∧
    (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = J.pCoreIn 2) ∧
    Nat.card V ≤ Nat.card W ∧
    ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W

/-- The actual 4.4.5 residual produces the complete C.2.8 configuration. -/
theorem pushingUp_case_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    PushingUpCase L V A := by
  obtain ⟨hc,_,hVF,hne⟩ := chosen_oddActorResidual_cover h D A hAN hcomm hodd hAV
  have hFL : oddActorResidual L A ≤ L := (oddActorResidual_le L A).trans inf_le_left
  have hFN := hFL.trans L.le_normalizer
  obtain ⟨J,H,P,hJ,hpush,hH,hJH,_,hstrict,_,hC,c,_,hVW⟩ :=
    Chapter4.Section02.Unitary.exists_source_C28_of_not_unique h D hM hFN hc.subset hne hnot
  have hVJ : V ≤ J.pCoreIn 2 := hVF.trans hpush.1
  have hr := chosen_intersection_twoResidual_eq_solvableResidual h hJ.1.1.2.2.1 hJH
  have hd := chosen_oddActorResidual_counterexample_residual h D hJ.1.1.2.2.1 hJH hVJ
  rw [hr] at hd
  obtain ⟨e,he⟩ := exists_pCoreQuotientEquiv_of_cover
    ((map_subtype_le _).trans inf_le_left) hd.1.subset
  have hsize := card_le_of_le hVW
  rw [card_map_of_injective (MulAut.conj (c : G)).injective] at hsize
  exact ⟨J,H,_,hJ,hpush,hH,hJH,hstrict,hVJ,hC,hd.1,hd.2.2.1,hd.2.2.2.1,
    hd.2.2.2.2,⟨e,he⟩,hC.oddCore_eq_bot,hC.isRadical,hC.sylow_in_normalClosure,
    hC.section_fitting_eq_core,hC.section_sylow_in_H,hsize,c,hVW⟩

/-- The selected component in the uniqueness branch, retaining its ambient
embedding and the original fixed residual and module actions. -/
@[expose] def ComponentCase (L V A : Subgroup G) : Prop :=
  UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
  ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G)))

/-- The alternative branch selects a moved component without a fixed module order. -/
theorem component_of_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hcard : 8 < Nat.card V)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  obtain ⟨K,hK,hm,houtK,hcore,hqt,_⟩ :=
    chosen_oddNormalizer_exists_moved_component_of_large_module h D hcard A hne hAN
      hcomm hodd hAV (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2
  obtain ⟨_,hFK,hVK⟩ := chosen_oddNormalizer_component_normalization
    h D A hAN hcomm hodd hAV K hK
  let : IsQuasisimple K := hK.2
  have hkg : IsKGroup KnownSimple.IsKnownSimple K :=
    ((oddNormalizer_properQTK h.simpleQTKE A hne).2.2).subgroup K
  exact ⟨K,hK,hK.commutator_eq_self_of_normalizes hVK hm,houtK,hcore,
    ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
      hqt hkg,hFK,hVK⟩

/-- An escaping abelian odd normalizer produces one of the two literal source
configurations, with no assumed residual uniqueness or component classification. -/
theorem outside_case {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hcard : 8 < Nat.card V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    PushingUpCase L V A ∨ ComponentCase L V A := by
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · exact Or.inr ⟨hu,component_of_unique h D hcard A hne hAN hcomm hodd hAV hu hout⟩
  · exact Or.inl (pushingUp_case_of_not_unique h D hM A hAN hcomm hodd hAV hu)

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
