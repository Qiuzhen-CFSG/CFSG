module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryLieRemaining
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryLinearThree
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryLinearThreeCover
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinarySymplectic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryHigherG2
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryTriality
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryTrialityRee
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBinaryExceptional
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-!
# Only Bender and Tits rows remain on the same original ordinary component

The original controls exclude all linear-three, symplectic, G2, triality and
Ree rows, including the retained central covers. The same marked automorphism
is inner and the same L is simple. No M-generation or global residual premise
is introduced; the remaining Bender and Tits source duties stay explicit.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ClassificationModels
open Chapter1.Section02.LocalModels Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The same original ordinary component is simple and retains only the
Bender or Tits family; its actual marked action remains inner. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_lie_restrictions
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
        ¬ L ≤ G1 ⊓ Mc →
        ((G1 ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc →
        normalizer ((pResidual 2 (G1 ⊓ Mc : Subgroup G)).map (G1 ⊓ Mc).subtype : Set G) ≤ Mc →
        G1 ⊓ normalizer ((G1 ⊓ Mc).pCoreIn 2 : Set G) = G1 ⊓ Mc →
        (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
          (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
            (M ⊓ centralizer (V : Set G)).subtype →
        ∀ {α : MulAut L}, ModelAction115 L α →
          α ∈ (MulAut.conj (G := L)).range ∧ IsSimpleGroup L ∧
            (IsBenderModel L ∨ Nonempty (L ≃* Tits.ParrottGroup)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hquasi hSyl
    hnL hmove hnZ hfaith hSylG h115 hout hcontrol hbound hcoreN hI α hm
  have hZ : Z1 ≤ thompsonFixed T V := inf_le_right
  have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by
    rw [show Nat.card Z1 = 4 from s.thompson_card s.first]
    decide)
  have hsmall := h.decomposable_five_raw_ordinary_small_quotients
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
    hLG hLc hcenter hnL hmove
  have hnocover := h.raw_ordinary_not_linearThree_four_cover hG T hempty hM hJ hu
    hZ hZne hLG hLc hcenter hnZ hfaith hSylG hSyl hcontrol hbound hI hmove
  have hnolinear : ¬∃ n : ℕ, 1≤n ∧ ClassicalGroup.IsPSL L 3 (2^n) := by
    rintro ⟨n,hn,F,_,_,hF,⟨e⟩⟩
    by_cases hn1 : n=1
    · subst n
      let := Fintype.ofFinite F
      let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod,pow_one] using hF)
      let e2 : L ≃* PSL(3,ZMod 2) := e.trans (Atlas.fieldEquivPSL 3 k)
      have hz : center L = ⊥ := by
        apply (Subgroup.eq_bot_iff_forall _).mpr
        intro z hz
        have hh : e2 z ∈ center PSL(3,ZMod 2) := (centerCongr e2 ⟨z,hz⟩).property
        rw [Group.IsPerfect.center_quotient_center_eq_bot SL(3,ZMod 2),mem_bot] at hh
        exact e2.injective (hh.trans (map_one e2).symm)
      have hc : pCore 2 L = ⊥ := hcenter.symm.trans hz
      let ec := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e2
      exact hsmall.2.2.2 7 (by decide) (by decide)
        ⟨ec.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩
    · exact h.raw_ordinary_not_linearThree hG T hempty hM hJ hu hZ hZne hLG hLc
        hcenter hnZ hfaith hSylG hSyl hcontrol hbound hI hmove (by omega) hF e
  have hnog2 (n : ℕ) (hn : 1<n) := h.raw_ordinary_not_higherG2 hG T hempty hM hJ hu
    hZ hZne hLG hLc hcenter hSylG hSyl hout n hn
  obtain ⟨hinner,hrows⟩ := h.decomposable_five_raw_ordinary_lie_remaining
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
    hLG hLc hcenter hquasi hSyl hnL hmove hnZ hfaith hSylG h115 hout hm
  rcases hrows with ⟨hsimple,hrows⟩ | ⟨_,_,hlinear | hg⟩
  · let := hsimple
    let : IsQuasisimple (L.subgroupOf G1) := hLc.2
    let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
    have hcb : pCore 2 L = ⊥ := hcenter.symm.trans center_eq_bot_of_simple_perfect
    let eq : (L ⧸ pCore 2 L) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hcb).trans QuotientGroup.quotientBot
    obtain ⟨htrial,hderived⟩ := h.decomposable_five_raw_ordinary_binary_exceptions
      hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive hLG hLc hcenter hnL hmove
    refine ⟨hinner,hsimple,?_⟩
    rcases hrows with hb | hl | ⟨n,hn,F,_,_,hF,⟨e⟩⟩ | ⟨n,hn,hg⟩ | ⟨n,hn,ht⟩ | ⟨m,hm,hr⟩ | ⟨ed⟩ | htits
    · exact Or.inl hb
    · exact (hnolinear hl).elim
    · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact (h.raw_ordinary_not_symplectic hG T hM hJ hu hZ hZne hLG hLc hcenter hSylG hSyl
        hcontrol hbound hcoreN hout hI hmove (by omega) hF
        (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)).elim
    · exact (hnog2 n (by omega) (Or.inl hg)).elim
    · by_cases hn1 : n=1
      · subst n
        obtain ⟨et⟩ := (Triality.Standard.isTrialityGroupAt_two_iff L).mp (by simpa only [pow_one] using ht)
        exact (htrial ⟨eq.trans et⟩).elim
      · exact (h.raw_ordinary_not_higherTriality hG T hempty hM hJ hu hZ hZne
          hLG hLc hcenter hSylG hSyl hout n (by omega) ht).elim
    · exact (h.raw_ordinary_not_higherRee hG T hempty hM hJ hu hZ hZne
        hLG hLc hcenter hSylG hSyl hout m hm hr).elim
    · exact (hderived ⟨eq.trans (Classical.choice ed)⟩).elim
    · exact Or.inr htits
  · exact (hnocover hlinear).elim
  · exact (hnog2 2 (by decide) (Or.inr hg)).elim

end CFSG.Quasithin.Chapter15.Section01
