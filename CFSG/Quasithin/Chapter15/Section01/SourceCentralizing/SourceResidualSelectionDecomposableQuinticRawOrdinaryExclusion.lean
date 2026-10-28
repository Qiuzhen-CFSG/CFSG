module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawLieClassifier
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryTits
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinarySuzuki
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBenderLinear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBenderUnitary

/-!
# Ordinary componenthood is impossible at the original quintic source

Every ordinary model is excluded on the same actual L. The Lie source sieve
and native marked Borel arguments handle Bender groups; the original quintic
actor and Tits Sylow geometry handle the final exceptional row. All hypotheses
are literal outputs of the original raw source, with no whole-M generation
or prior global residual-normalization premise.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ClassificationModels
open Chapter1.Section02.LocalModels Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The actual raw source controls exclude ordinary componenthood before
any global residual-normalization or marked-generation statement. -/
theorem PreparedChosenModule.decomposable_five_raw_not_ordinary
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
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let S := (T : Subgroup G) ⊓ G1
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L → IsQuasisimple (L ⧸ pCore 2 L) → Chapter1.IsSylowIn 2 (S ⊓ L) L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        centralInvolutions T ≤ normalizer (L : Set G) →
        centralInvolutions T ⊓ centralizer (L : Set G) = ⊥ →
        Chapter1.IsSylowIn 2 S G1 →
        (∃ P : Sylow 2 G1, (P : Subgroup G1).map G1.subtype = S ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z) →
        ¬ L ≤ G1 ⊓ Mc → ¬L ≤ M →
        ((G1 ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc →
        normalizer ((pResidual 2 (G1 ⊓ Mc : Subgroup G)).map (G1 ⊓ Mc).subtype : Set G) ≤ Mc →
        G1 ⊓ normalizer ((G1 ⊓ Mc).pCoreIn 2 : Set G) = G1 ⊓ Mc →
        (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
          (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
            (M ⊓ centralizer (V : Set G)).subtype →
        (∀ z ∈ centralInvolutions T, z ≠ 1 →
          ∃ α : MulAut L, ModelAction115 L α) → False := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hquasi hSyl
    hnL hmove hnZ hfaith hSylG h115 hout houtM hcontrol hbound hcoreN hI hmodels
  have hZ : Z1 ≤ thompsonFixed T V := inf_le_right
  have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by
    rw [show Nat.card Z1 = 4 from s.thompson_card s.first]
    decide)
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,hm⟩ := hmodels z hz hzne
  obtain ⟨_,_,hB | ⟨et⟩⟩ := h.decomposable_five_raw_ordinary_lie_restrictions
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
    hLG hLc hcenter hquasi hSyl hnL hmove hnZ hfaith hSylG h115 hout
    hcontrol hbound hcoreN hI hm
  · cases hB with
    | linear n hn model =>
      by_cases hlarge : 2<n
      · exact h.raw_ordinary_not_binary_linear_gt_two hG T hM hJ hu hZ hZne hLG hLc
          hSylG hSyl hcontrol hbound hI hmove hout hlarge model
      · exact h.decomposable_five_raw_not_binary_linear_small hG T hempty hM hmany hJ hfull
          c d hd s π hp hs hdec hq hfive hnL hmove n hn (by omega) model
    | unitary n hn model =>
      exact h.raw_ordinary_not_binary_unitary hG T hM hJ hu hZ hZne hLG hLc hcenter
        hSylG hSyl hcontrol hbound hI hmove hout hn model
    | suzuki m hm model =>
      exact h.raw_ordinary_not_suzuki hG T hM hJ hu hZ hZne hLG hLc hcenter
        hSylG hSyl hcontrol hbound hI hmove hout (by omega) (Classical.choice model)
  · exact (h.decomposable_five_raw_ordinary_not_tits hG T hempty hM hmany hJ hfull
      c d hd s π hp hs hdec hq hfive hLG hLc hSyl hnZ h115 hI houtM hmove).false (Classical.choice et)

end CFSG.Quasithin.Chapter15.Section01
