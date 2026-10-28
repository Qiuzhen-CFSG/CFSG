module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianBinaryLinear
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.BinaryExtension
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.BinaryUpper
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleRadicalTwoExtension

/-!
# The remaining binary endpoints in the original normal-component sieve

For a T-invariant escaping component K, restriction of the two-core
identifies K/O₂(K) with its normal image in KT/O₂(KT). The binary Sp₄′
and G₂′ generation theorems apply to that actual image and Sylow supplement.
For the nonsplit triple cover of A₆, retain its central three-group:
the solvable-radical quotient identifies the simple A₆ image, and positive
E-generation lifts through the entire solvable kernel.

All three rows make KT have generation parameter one. Source 12.6.29
then contradicts K escaping M. This applies to the original abelian-branch
component and uses none of the contrary nonabelian branch's selections.

Source: Aschbacher--Smith 12.6.31, printed p.836, using E.1.14(1),(6),
printed p.214, and 12.6.29, printed p.835.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open ChapterE.ValuesEvenClassical.RankTwoUpper
open Chapter15.Section03.AbelianAmalgam.GenerationOne

private theorem a6_center_isEGenerated {X : Type*} [Group X] [Finite X]
    (C : Subgroup X) [C.Normal] [IsQuasisimple C] (P : Sylow 2 X)
    (hgen : C ⊔ (P : Subgroup X) = ⊤)
    (e : (C ⧸ center C) ≃* alternatingGroup (Fin 6)) : ChapterE.IsEGenerated 1 X := by
  have hr : solvableRadical C = center C := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center C) inferInstance inferInstance)
  let er : (C ⧸ solvableRadical C) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hr).trans e
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (C ⧸ solvableRadical C) := er.isSimpleGroup
  let : Group.IsPerfect (C ⧸ solvableRadical C) :=
    Group.IsPerfect.ofSurjective (f := er.symm.toMonoidHom) er.symm.surjective
  have ha := Group.IsPerfect.not_isMulCommutative (C ⧸ solvableRadical C)
  have hq := isPGroup_quotient_of_sup_eq_top C P P.isPGroup' hgen
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (solvableRadical X))
  let ef := (radicalTwoExtensionFittingEquiv C ha hq).trans er
  let : IsSimpleGroup (generalizedFitting (X ⧸ solvableRadical X)) := ef.isSimpleGroup
  let em := ef.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  exact ChapterE.IsEGenerated.of_solvableRadical_quotient (by decide)
    (SymplecticFour.isEGenerated_binary_extension (by simp : Nat.card (ZMod 2) = 2)
      em Q (radicalTwoExtension_fitting_sup_sylow C ha hq Q))

private theorem small_lie_normal_isEGenerated {X : Type*} [Group X] [Finite X]
    (C : Subgroup X) [C.Normal] [IsQuasisimple C] (P : Sylow 2 X)
    (hgen : C ⊔ (P : Subgroup X) = ⊤) (hcore : pCore 2 X = ⊥)
    (hm : Models.IsSp4DerivedAt C 2 ∨ Models.IsG2DerivedAt C 2 ∨
      Nonempty (C ≃* Models.A6Triple)) : ChapterE.IsEGenerated 1 X := by
  rcases hm with ⟨F,hF,hfin,hcard,⟨e⟩⟩ | ⟨F,hF,hfin,hcard,⟨e⟩⟩ | ⟨e⟩
  · let := hF
    let := hfin
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let ea := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hcard)
    let : IsSimpleGroup C := ea.isSimpleGroup
    have hf := generalizedFitting_eq_of_quasisimple_two_quotient C
      (isPGroup_quotient_of_sup_eq_top C P P.isPGroup' hgen) hcore
    let ef := (MulEquiv.subgroupCongr hf).trans e
    let : IsSimpleGroup (generalizedFitting X) := (MulEquiv.subgroupCongr hf).isSimpleGroup
    exact SymplecticFour.isEGenerated_binary_extension hcard ef P (by rwa [hf])
  · let := hF
    let := hfin
    exact ChapterE.ExceptionalValues.G2.isEGenerated_one_of_binary_socle hcard C P e hgen
  · obtain ⟨e⟩ := e
    exact a6_center_isEGenerated C P hgen
      ((centralQuotientEquiv e).trans Representation.Hexacode.even_quotient_center_equiv)

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)

include hz hTV hTz hbound hTI hns in
/-- The original escaping T-invariant C-component has none of the binary
Sp₄′, binary G₂′ or triple-A₆ intrinsic quotients. -/
theorem SourceHypothesis.original_escaping_smallLie_impossible
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) (hout : ¬ K ≤ M L)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) 2 ∨
      Models.IsG2DerivedAt (K ⧸ pCore 2 K) 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Models.A6Triple)) : False := by
  let J := K ⊔ (T : Subgroup G)
  let Ki := K.subgroupOf J
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let q := QuotientGroup.mk' (pCore 2 J)
  let C := Ki.map q
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let P := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 J))
  let eKi : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eC : C ≃* (K ⧸ pCore 2 K) := (coreQuotientEquivImage 2 Ki).symm.trans
    (QuotientGroup.congr _ _ eKi (pCore_map_iso 2 eKi))
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv eC.symm
  have hCP : C ⊔ (P : Subgroup (J ⧸ pCore 2 J)) = ⊤ := by
    change (K.subgroupOf J).map q ⊔ ((T : Subgroup G).subgroupOf J).map q = ⊤
    rw [←Subgroup.map_sup,←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hmC : Models.IsSp4DerivedAt C 2 ∨ Models.IsG2DerivedAt C 2 ∨
      Nonempty (C ≃* Models.A6Triple) := by
    rcases hm with hm | hm | hm
    · exact Or.inl (hm.of_mulEquiv eC)
    · exact Or.inr (Or.inl (hm.of_mulEquiv eC))
    · exact Or.inr (Or.inr (hm.map (eC.trans ·)))
  have hg : ChapterE.IsEGenerated 1 J :=
    ChapterE.IsEGenerated.of_normal_two_subgroup (pCore 2 J) pCore_isPGroup
      (small_lie_normal_isEGenerated C P hCP (pCore_quotient_pCore_eq_bot 2) hmC)
  have hdV : 2 ∣ Nat.card V := (IsElementaryAbelian.isPGroup 2 V).card_eq_or_dvd.resolve_left
    (fun h => S.chosen.ne_bot (Subgroup.card_eq_one.mp h))
  have hdJ : 2 ∣ Nat.card J := hdV.trans
    (card_dvd_of_le (S.chosen.le_sylow.trans (le_sup_right : (T : Subgroup G) ≤ J)))
  have hn := ChapterE.ExceptionalValues.generationParameter_eq_one_of_upper
    (fun ho => ho.not_two_dvd_nat hdJ) hg
  exact hout (le_sup_left.trans (S.original_generation_one_overgroup_le D hZ z hz hTV hTz
    hbound hTI hns (show (T : Subgroup G) ≤ J from le_sup_right) hn))

end CFSG.Quasithin.Chapter12.Section06
