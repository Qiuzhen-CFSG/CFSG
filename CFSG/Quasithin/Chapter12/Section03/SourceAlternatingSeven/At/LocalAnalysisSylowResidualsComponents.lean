module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponents
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsComponentsSetup

/-!
# LocalAnalysisSylowResidualsComponents at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsComponents`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode ChapterA.Section04

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

lemma coset_containing_component_quasisimple_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) :
    ∃ K : Subgroup (centralizer ({c * (P.six : G)} : Set G)),
      K.IsCComponent ∧ K.Normal ∧
      P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G)) ≤ K ∧
      generalizedFitting K = pCore 2 K ∧ IsQuasisimple (K ⧸ pCore 2 K) := by
  obtain ⟨K,hK,hn,hBK,hf⟩ := P.coset_containing_component_at structural M e6 hc
  refine ⟨K,hK,hn,hBK,hf,?_⟩
  apply ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank
    (S.hypothesis.simpleQTKE.twoLocal_sqtk (P.coset_isTwoLocal hc)) hK
  have hr := P.six_three_rank e6
  have he := primeRank_equiv 3 (subgroupOfEquivOfLe (P.sixGroup_le_coset_centralizer hc))
  exact (he ▸ hr).trans
    (_root_.primeRank_le_of_injective 3 (inclusion hBK) (inclusion_injective hBK))

theorem coset_components_or_C27_enlargement_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    P.CosetComponents ∨ ∃ c ∈ P.fixed, ∃ K : Subgroup G,
      P.sixGroup < K ∧
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple
        (centralizer ({c * (P.six : G)} : Set G))
        ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K ∧
      centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G) ∧
      (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent := by
  classical
  by_cases hC : P.CosetComponents
  · exact Or.inl hC
  right
  have hbad : ∃ c ∈ P.fixed,
      ¬ (centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (P.sixGroup : Set G) ∧
        (P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G))).IsCComponent) := by
    by_contra! h
    exact hC ⟨fun c hc => (h c hc).1, fun c hc => (h c hc).2⟩
  obtain ⟨c,hc,hbad⟩ := hbad
  let H := centralizer ({c * (P.six : G)} : Set G)
  obtain ⟨K,hK,hn,hBK,hf,hq⟩ := P.coset_containing_component_quasisimple_at structural M e6 hc
  let A := K.map H.subtype
  have hAH : A ≤ H := map_subtype_le _
  have hKA : A.subgroupOf H = K := comap_map_eq_self_of_injective H.subtype_injective K
  have hAc : (A.subgroupOf H).IsCComponent := hKA.symm ▸ hK
  have hAn : H ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAH).mp (hKA.symm ▸ hn)
  have hBA : P.sixGroup ≤ A := by
    intro x hx
    exact ⟨⟨x, P.sixGroup_le_coset_centralizer hc hx⟩, hBK hx, rfl⟩
  have hne : A ≠ P.sixGroup := by
    intro he
    exact hbad (he ▸ ⟨hAn,hAc⟩)
  have hout : ¬ A ≤ normalizer (L : Set G) := fun hh =>
    hne (P.coset_container_eq_of_le_local e6 hc hK hBK hh)
  have hAf : generalizedFitting A = pCore 2 A := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2
      (K.equivMapOfInjective H.subtype H.subtype_injective)).mp
    rw [← hf]
    exact centralizer_generalizedFitting_le K
  have hAq : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := hq
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _
      (K.equivMapOfInjective H.subtype H.subtype_injective) (pCore_map_iso 2 _))
  refine ⟨c,hc,A,lt_of_le_of_ne hBA (Ne.symm hne),
    ⟨P.coset_pushingUp_setup_at structural M hc,⟨hAH,hAc⟩,hAq,hAf,
      fun hh => hout (hh.trans inf_le_right),(P.coset_core_le hc).trans hAn⟩,hAn,?_⟩
  have hBN : P.sixGroup ≤ normalizer (L : Set G) ⊓ A :=
    le_inf ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer)) hBA
  exact (P.coset_local_component e6 hc).subgroupOf_of_le hBN
    (le_inf (inf_le_right.trans hAH) inf_le_left)

theorem six_residuals_or_C27_enlargement_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    (∀ c ∈ P.fixed, pointThreeResidual (c * (P.six : G)) = P.sixGroup) ∨
      ∃ c ∈ P.fixed, ∃ K : Subgroup G,
        P.sixGroup < K ∧
        Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
          KnownSimple.IsKnownSimple
          (centralizer ({c * (P.six : G)} : Set G))
          ((L ⊔ (T : Subgroup G)).pCoreIn 2)
          (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K ∧
        centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G) ∧
        (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent := by
  rcases P.coset_components_or_C27_enlargement_at structural M e6 with h | h
  · exact Or.inl (fun _ hc => P.six_residual_of_coset_components h e6 hc)
  · exact Or.inr h

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

