module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawClassifier
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawLinearTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawAlternatingFive

/-!
# The same original quintic component after both rank-one exclusions

The controlled Borel and the actual Thompson-normalizer residual exclude
respectively the natural rank-one and exceptional alternating-five blocks.
The outside component is selected only once. Its original marking, residual
intersection and movement remain attached to the surviving ordinary or star
branch. No whole-M generation or residual-normalization premise is added.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The actual original quintic component has neither rank-one block.
All retained ordinary or star data refer to the same selected component. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_no_rank_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 4 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let MZ := G1 ⊓ Mc
      let Q1 := MZ.pCoreIn 2
      let S := (T : Subgroup G) ⊓ G1
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let W := ⁅V,R⁆
      let Y := (pResidual 2 MZ).map MZ.subtype
      letI := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
      ∃ L : Subgroup G,
        Z1 ≤ thompsonFixed T V ∧ Nat.card Z1 = 4 ∧
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 ∧
        MZ = centralizer (thompsonFixed T V : Set G) ∧
        pPrimeCore 2 G1 = ⊥ ∧ Chapter1.IsSylowIn 2 S G1 ∧
        (S.subgroupOf (T : Subgroup G)).Normal ∧
        (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
          (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
            (M ⊓ centralizer (V : Set G)).subtype ∧
        centralInvolutions T ⊓ V ≤ Z1 ⊔ W ∧
        Q1 ≠ ⊥ ∧ Q1.characteristicNormalizerClosure ≤ Mc ∧
        G1 ⊓ normalizer (Q1 : Set G) = MZ ∧
        (T : Subgroup G) ≤ normalizer (MZ : Set G) ∧
        (T : Subgroup G) ≤ normalizer (Q1 : Set G) ∧
        normalizer (Y : Set G) ≤ Mc ∧ Y ≤ centralizer (centralInvolutions T : Set G) ∧
        (∃ P : Sylow 2 G1, (P : Subgroup G1).map G1.subtype = S ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z) ∧
        L ∈ Chapter1.cComponentsIn G1 ∧ ¬ L ≤ MZ ∧
        IsQuasisimple (L ⧸ pCore 2 L) ∧ L ∈ Chapter1.L G S ∧
        Chapter1.IsSylowIn 2 (S ⊓ L) L ∧ ¬ L ≤ M ∧
        R ⊔ W ≤ normalizer (L : Set G) ∧ ⁅L,W⁆ ≠ ⊥ ∧
        (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
          centralizer (V : Set G) ∧
        S ⊓ centralizer (((primeToResidual 3 (M ⊓ L : Subgroup G)).map
          (M ⊓ L).subtype) : Set G) ≠ S ⊓ centralizer (L : Set G) ∧
        (¬ ∃ n : ℕ, IsL2EvenBlock L n) ∧ ¬ IsAlternatingBlock L 5 ∧
        ((IsComponent G1 (L.subgroupOf G1) ∧
          center L = pCore 2 L ∧ IsPGroup 2 (center L) ∧
          centralInvolutions T ≤ normalizer (L : Set G) ∧
          centralInvolutions T ⊓ centralizer (L : Set G) = ⊥ ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 →
            ⁅L,zpowers z⁆ = L ∧ ∃ α : MulAut L,
              (∀ x : L, (α x : G) = z*x*z⁻¹) ∧ ModelAction115 L α) ∨
          (generalizedFitting L = pCore 2 L ∧
            (∃ hi : Input KnownSimple.IsKnownSimple G1 Q1 MZ L,
                StarModels.Model (starImage L Q1 L) ∧
                  (coreToStar hi.normalizes).ker ≤ center (L ⧸ pCore 2 L) ∧
                  (Nat.card (center (L ⧸ pCore 2 L)) = 1 ∨
                    Nat.card (center (L ⧸ pCore 2 L)) = 3)))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,
    hres,hneq,hcases⟩ := h.decomposable_five_partner_four_raw_classifier
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hZne : thompsonPlane T V (c.ambientFactor d s.first).space ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hZcard
    norm_num at hZcard
  have hnot2 := h.raw_component_not_linear_two hG T hM hJ hu
    hZ hZne hSylG hLc hloc hquasi hout houtM hcontrol hresN hI hmove
  have hnot5 := h.raw_component_not_alternating_five hG T hM hJ hu
    hZ ⟨hLc.1,hloc⟩ hquasi hout houtM hSylG hnL hmove
  refine ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,
    hres,hneq,hnot2,hnot5,?_⟩
  rcases hcases with hordinary | ⟨hfit,hrank | hstar⟩
  · exact Or.inl hordinary
  · exact (hrank.elim hnot2 hnot5).elim
  · exact Or.inr ⟨hfit,hstar⟩

end CFSG.Quasithin.Chapter15.Section01
