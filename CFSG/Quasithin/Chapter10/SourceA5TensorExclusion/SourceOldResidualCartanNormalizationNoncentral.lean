module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationCatalogue
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationOddCore
public import Theory.GroupTheory.CComponent.FittingCentralizer

/-!
# The remaining noncentral odd-core Cartan configuration

The complete quasisimple catalogue leaves a proper normal containing component
J whose two-core quotient is nonquasisimple. Its literal image I in
N_G(tensorLine)/O₂(N_G(tensorLine)) therefore has noncentral Fitting subgroup:
a C-component with central Fitting subgroup has central solvable radical and
is quasisimple.

This discharges the noncentral-Fitting premise in the earlier invariant-core
construction. The original nonzero-core inputs now give Cartan normalization
or the exact remaining J, R=O_{2,2′,2}(J)=Rad(J), and the A-invariant residual
N_J(T∩R)^∞ containing the old residual. The marked involution-centralizer
cover and subsequent rank-one normalization remain the next source steps.
Source: Aschbacher–Smith, Proposition 9.3.1, printed pp.732–733.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ChapterA.Section03
open Theory.GroupTheory.LocalSolvableCoreNormalizer

private theorem quasisimple_of_central_fitting
    {X : Type*} [Group X] [Finite X] {C : Subgroup X}
    (hC : C.IsCComponent) (hf : fittingSubgroup C ≤ center C) : IsQuasisimple C := by
  have hr : solvableRadical C = center C := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center C) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hC.perfect
  let := hC.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem cartan_container_fitting_noncentral
    (J : Subgroup G) (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnq : ¬ IsQuasisimple (J ⧸ pCore 2 J)) :
    let N := normalizer (m.tensorLine : Set G)
    let I := (J.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
    ¬ fittingSubgroup I ≤ center I := by
  intro N I hf
  let j : J.subgroupOf N ≃* J := subgroupOfEquivOfLe hJU
  let d : I ≃* (J ⧸ pCore 2 J) := (cComponentTwoCoreQuotientEquiv hJ).symm.trans
    (QuotientGroup.congr _ _ j (pCore_map_iso 2 j))
  let := (pCore_isPGroup (p := 2) (G := N)).isNilpotent
  let := quasisimple_of_central_fitting (hJ.map_quotient (pCore 2 N)) hf
  exact hnq (IsQuasisimple.of_mulEquiv d)

theorem nonzero_core_cartan_normalization_invariant_oddCore
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∨
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype < J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 ∧
      Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))) ∧
      ¬ IsQuasisimple (J ⧸ pCore 2 J) ∧
      (let N := normalizer (m.tensorLine : Set G)
       let I := (J.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
       ¬ fittingSubgroup I ≤ center I) ∧
      twoOddTwoCore J = solvableRadical J ∧
      (pResidual 2 H).map H.subtype ≤
        localNormalizerResidual J ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype) ∧
      A ≤ normalizer (localNormalizerResidual J
        ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype) : Set G) := by
  obtain hAK | ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hz3,hnq⟩ :=
    m.nonzero_core_cartan_normalization_nonquasisimple hH hlarge
      A B hAB hA9 hAe hB3 hBK hBC hcore
  · exact .inl hAK
  have hn := m.cartan_container_fitting_noncentral J hJU hJ hnq
  obtain ⟨hR,hKK,hAK⟩ := m.cartan_invariant_oddCore_normalizer_residual
    hH hlarge A B J hAB hA9 hAe hBK hAJB hJU hJ hnJ hKJ.le hn
  exact .inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hz3,hnq,hn,hR,hKK,hAK⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
