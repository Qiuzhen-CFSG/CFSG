module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeDegree
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeMarking
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.SourceExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.DoubleExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications

/-!
# The original linear-three rows use only the small MS classification

The marked parabolic and full core quotient force the original field to
have order two, before any use of C.1.34. The same X and R then form a
small MS pair: their odd-index witness is the original NI construction,
and their product is supplied by the selected radical normalization.

The existing small classifier applies with the original field F and every
original Sylow overgroup S. Thus all five module alternatives give the
literal MSDescription consumed by the established linear-three exclusion.
No enlargement of the universal classification input is required. Its
producer remains qt-rank-two-ms93 and final discharge remains at Theorem E.
The earlier full-field conditional APIs remain available unchanged.

Source: Aschbacher--Smith C.1.31--34, pp.135--137, C.2.7(g), pp.145--147,
and original 15.2.23, pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u

variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The source geometry supplies an actual small MS pair on the original
X and R, without invoking any MS classification. -/
theorem normalized_component_smallMSPair_of_parabolic
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F) :
    SmallMSPair KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) := by
  have he := linearThree_degree_eq_one_of_star_parabolic d hI
    (normalized_component_input (hsource := hsource) hI hcore s) n F hn hF hp
  subst n
  obtain ⟨e, _⟩ := hp
  have hms := normalized_component_msPair_of_star_model d hI hcore s 1 F hn hF e
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [← Nat.card_eq_fintype_card, pow_one] using hF)).symm
  obtain ⟨eCore⟩ := hms.model
  have hb : LinearThreeMSPair KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2)
      1 (ZMod 2) :=
    ⟨by decide, by simp, ⟨eCore.trans (Atlas.fieldEquivSL 3 f)⟩,
      hms.sqtk, hms.fitting, hms.component, hms.radical, hms.characteristic⟩
  exact linearThree_smallMSPair_of_odd_index hb
    (normalized_component_ms_oddIndex d hI hcore s) s.radical_normalizes

/-- Apply the existing small C.1.34 classifier to the original field and
markings, after deriving its small-pair premise from the source geometry. -/
theorem normalized_component_msDescription_of_small_classification
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F) :
    MSDescription KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) n F := by
  have hpar := hp
  obtain ⟨e, _⟩ := hp
  have hms := normalized_component_msPair_of_star_model d hI hcore s n F hn hF e
  have hsmall := normalized_component_smallMSPair_of_parabolic d hI hcore s n F hn hF hpar
  exact ⟨hms, hC134.linearThree G X ((M ⊓ I).pCoreIn 2)
    hsmall n hn F hF hms.model⟩

/-- The marked linear-three row includes the actual full MS description. -/
theorem normalized_component_linearThree_of_small_classification
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F) :
    LinearAlternative X ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  exact .linearThree n F hn hF hp
    (normalized_component_msDescription_of_small_classification d hC134 hI hcore s n F hn hF hp)

/-- Apply the source exclusion on the same marking; no whole-core or
local MS callback remains, only the existing small C.1.34 theorem. -/
theorem normalized_component_linearThree_false_of_small_classification
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F)
    (hout : n = 1 → ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hc : ChosenGeometry.StructuralAlternatives T H Mc)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ planeSylow T ZS)
    (hYY : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤ Y ⊓ Y.map (MulAut.conj t).toMonoidHom) :
    False := by
  exact LinearThree.not_linearThree_ms d
    (normalized_component_input (hsource := hsource) hI hcore s) hn hF hp
    hI hfit hout f hker hKcI hc t ht htS hYY
    (normalized_component_msDescription_of_small_classification d hC134 hI hcore s n F hn hF hp)

/-- The original natural B.5.1 row satisfies every clause of
C.2.7(g), with only the existing small C.1.34 theorem still explicit. -/
theorem normalized_component_naturalThree_alternative_of_small_classification
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (F : BinaryField)
    (a : ActionEquiv (s.action.comp
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))).subtype)
        (linearNatural F 3))
    (hext : (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))) = ⊤ ∨
      (∀ T : Sylow 2 (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))),
        (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
          (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))) ⊔
          (T : Subgroup _) = ⊤) ∧ OuterNaturalAction s.action) :
    LinearAlternative X ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  obtain ⟨_,hp⟩ | ⟨_,hp⟩ := normalized_component_naturalThree_parabolic (hsource := hsource) hI hcore selection hno hCJ s F a hext
  · exact normalized_component_linearThree_of_small_classification d hC134 hI hcore selection
      1 (ZMod 2) (by decide) (by simp) hp
  · exact normalized_component_linearThree_of_small_classification d hC134 hI hcore selection
      F.degree F.Carrier (Nat.succ_le_of_lt F.degree_pos) F.card_eq hp

/-- The original doubled-natural B.5.1 row satisfies every clause of
C.2.7(g), with only the existing small C.1.34 theorem still explicit. -/
theorem normalized_component_doubleThree_alternative_of_small_classification
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (F : BinaryField)
    (ht : (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))) = ⊤)
    (a : ActionEquiv (s.space.toRepresentation.comp
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))).subtype)
        (repeated (linearNatural F 3) 2)) :
    LinearAlternative X ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  obtain ⟨_,hp⟩ | ⟨_,hp⟩ := normalized_component_doubleThree_parabolic (hsource := hsource) hI hcore selection hno hCJ s F ht a
  · exact normalized_component_linearThree_of_small_classification d hC134 hI hcore selection
      1 (ZMod 2) (by decide) (by simp) hp
  · exact normalized_component_linearThree_of_small_classification d hC134 hI hcore selection
      F.degree F.Carrier (Nat.succ_le_of_lt F.degree_pos) F.card_eq hp

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
