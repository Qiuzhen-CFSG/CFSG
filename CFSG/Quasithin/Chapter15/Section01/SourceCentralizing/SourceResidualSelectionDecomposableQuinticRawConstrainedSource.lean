module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNoRankOne
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryExclusion

/-!
# The original order-four partner produces a constrained component

All ordinary models are excluded on the same component selected from the
original full quintic source. Its original local controls, movement, both
rank-one block exclusions and the actual C.2.7 star map remain attached.
No marked generation or global residual-normalization premise is introduced.
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

/-- One literal original source component is constrained, with its full
local geometry and exact star quotient kernel retained. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_constrained
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
        generalizedFitting L = pCore 2 L ∧
            (∃ hi : Input KnownSimple.IsKnownSimple G1 Q1 MZ L,
                StarModels.Model (starImage L Q1 L) ∧
                  (coreToStar hi.normalizes).ker ≤ center (L ⧸ pCore 2 L) ∧
                  (Nat.card (center (L ⧸ pCore 2 L)) = 1 ∨
                    Nat.card (center (L ⧸ pCore 2 L)) = 3)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,
    hres,hneq,hnot2,hnot5,hcases⟩ := h.decomposable_five_partner_four_raw_no_rank_one
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hconstrained : generalizedFitting L = pCore 2 L ∧
      ∃ hi : Input KnownSimple.IsKnownSimple
        (centralizer (thompsonPlane T V (c.ambientFactor d s.first).space : Set G))
        ((centralizer (thompsonPlane T V (c.ambientFactor d s.first).space : Set G) ⊓ Mc).pCoreIn 2)
        (centralizer (thompsonPlane T V (c.ambientFactor d s.first).space : Set G) ⊓ Mc) L,
        StarModels.Model (starImage L
          ((centralizer (thompsonPlane T V (c.ambientFactor d s.first).space : Set G) ⊓ Mc).pCoreIn 2) L) ∧
          (coreToStar hi.normalizes).ker ≤ center (L ⧸ pCore 2 L) ∧
          (Nat.card (center (L ⧸ pCore 2 L)) = 1 ∨ Nat.card (center (L ⧸ pCore 2 L)) = 3) := by
    rcases hcases with ⟨hL,hcenter,_,hnZ,hfaith,hmodels⟩ | hc
    · apply False.elim
      apply h.decomposable_five_raw_not_ordinary hG T hempty hM hmany hJ hu hfull
        c d hd s π hp hs hdec hq hfive hLc.1 hL hcenter hquasi hSyl hnL hmove
        hnZ hfaith hSylG h115 hout houtM hcontrol hresN hn hI
      intro z hz hzne
      obtain ⟨α,_,hm⟩ := (hmodels z hz hzne).2
      exact ⟨α,hm⟩
    · exact hc
  exact ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,
    hres,hneq,hnot2,hnot5,hconstrained⟩

end CFSG.Quasithin.Chapter15.Section01
