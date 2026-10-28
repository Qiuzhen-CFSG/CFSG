module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryRows
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinarySporadic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryMathieu
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBinaryLinear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryJankoFour

/-!
# Only characteristic-two Lie rows remain on the original raw component

The actual faithful sixteen, quintic pair, full-Sylow overgroup, and original
marked J₄ exclusion exhaust every sporadic row and the binary linear models.
The same original component and marked automorphism retain only the explicit
characteristic-two Lie families or the nontrivial central two-covers of
PSL₃(4) and G₂(4). No component replacement, whole-M generation or global
residual-normalization hypothesis is introduced.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ClassificationModels
open Chapter1.Section02.LocalModels Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The original characteristic-two family list after the actual binary
PSL₄(2)/PSL₅(2) and derived symplectic endpoint exclusions. -/
def RawOrdinaryLieRemaining (H : Type*) [Group H] : Prop :=
  IsBenderModel H ∨
  (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL H 3 (2^n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSp H 2 (2^n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ IsG2At H (2^n)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) H) ∨
  (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At H m) ∨
  Nonempty (H ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
  Nonempty (H ≃* Tits.ParrottGroup)

/-- The same actual marked automorphism is inner, and its original ordinary
component has only the remaining characteristic-two Lie or central-cover rows. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_lie_remaining
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
        ∀ {α : MulAut L}, ModelAction115 L α →
          α ∈ (MulAut.conj (G := L)).range ∧
          ((IsSimpleGroup L ∧ RawOrdinaryLieRemaining L) ∨
            (center L ≠ ⊥ ∧ center L = pCore 2 L ∧
              (ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨
                IsG2At (L ⧸ pCore 2 L) 4))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hquasi hSyl
    hnL hmove hnZ hfaith hSylG h115 hout α hm
  have hr := h.decomposable_five_raw_ordinary_rows
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
    hLG hLc hcenter hnL hmove hm
  refine ⟨hr.inner,?_⟩
  rcases hr with ⟨hsimple,hLie,_⟩ | ⟨hnc,hc,hmodel,_⟩ | ⟨name,hn3,⟨e⟩,_⟩
  · refine Or.inl ⟨hsimple,?_⟩
    rcases hLie with hB | h3 | hSp | hG2 | hTrial | hRee | hDerived | hTits | ⟨n,hn,h45⟩
    · exact Or.inl hB
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl hSp))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hG2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hTrial))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hRee)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hDerived))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hTits))))))
    · exact (h.decomposable_five_raw_not_binary_psl
        hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
        hLG hLc hcenter hquasi hSyl hnL hmove n hn h45).elim
  · exact Or.inr ⟨hnc,hc,hmodel⟩
  · exfalso
    obtain ⟨h12,hj2,hhs,hhe,hru⟩ := h.decomposable_five_raw_ordinary_sporadic_exclusions
      hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
      hLG hLc hcenter hSyl hnL hmove
    obtain ⟨h22,h23,h24⟩ := h.decomposable_five_raw_not_large_mathieu
      hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
      hLG hLc hcenter hquasi hSyl hnL hmove
    cases name with
    | m11 =>
        exact h.decomposable_five_raw_ordinary_not_mathieuEleven
          hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
          hLG hLc hcenter hnL hmove ⟨e⟩
    | m12 => exact h12 ⟨e⟩
    | m22 => exact h22 ⟨e⟩
    | m23 => exact h23 ⟨e⟩
    | m24 => exact h24 ⟨e⟩
    | j2 => exact hj2 ⟨e⟩
    | j3 => exact hn3 rfl
    | j4 =>
        have hZ : Z1 ≤ thompsonFixed T V := inf_le_right
        have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by
          rw [show Nat.card Z1 = 4 from s.thompson_card s.first]
          decide)
        exact (h.raw_ordinary_not_jankoFour hG T hempty hM hJ hu hZ hZne
          hLG hLc hcenter hnZ hfaith hSylG hSyl h115 hout).false e
    | hs => exact hhs ⟨e⟩
    | he => exact hhe ⟨e⟩
    | ru => exact hru ⟨e⟩

end CFSG.Quasithin.Chapter15.Section01
