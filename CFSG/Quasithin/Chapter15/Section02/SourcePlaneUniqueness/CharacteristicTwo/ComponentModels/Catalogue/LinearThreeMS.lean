module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.CoreQuotient
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeMarking
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.SourceExclusion

/-!
# C.1.34 on the original marked linear-three rows

The full core-quotient recognition and original NI witness establish all
MS hypotheses. The universal C.1.34 implication is kept explicit, with all
five module alternatives and the original Sylow subgroup. Its producer
is qt-rank-two-ms93 and its final discharge remains at Theorem E; the
small-model-only EarlierMSClassifications interface does not supply this
all-field implication by itself.

Both natural and doubled-natural B.5.1 rows now yield the full marked
C.2.7(g) conclusion on the same X, R, and NI, conditional only on this
source classification. The final exclusion applies the previously proved
linear-three argument with its genuine earlier source premises. This does
not assert exhaustiveness of the remaining C.2.7 catalogue.

Source: Aschbacher--Smith C.1.34, printed pp.136--137; C.2.7(g), pp.145--147;
original 15.2.23, pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u

/-- The exact full-field C.1.34 implication needed here, with all five
alternatives. This is an explicit source premise, not a classification proof. -/
@[expose] def FullLinearThreeClassification (κ : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (K R : Subgroup J)
    (n : ℕ) (F : Type) [Field F] [Finite F],
    LinearThreeMSPair κ K R n F →
    ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (K ⊔ R) → R ≤ S →
      ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F), MSModuleAlternatives K R S n F e

variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Construct the actual full MS description from the marked parabolic,
discharging the entire core-quotient and MS-pair premises of C.1.34. -/
theorem normalized_component_msDescription_of_classification
    (hC134 : FullLinearThreeClassification.{u} KnownSimple.IsKnownSimple)
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F) :
    MSDescription KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) n F := by
  obtain ⟨e,_,_,_,_⟩ := hp
  have hms := normalized_component_msPair_of_star_model d hI hcore s n F hn hF e
  exact ⟨hms, hC134 G X ((M ⊓ I).pCoreIn 2) n F hms⟩

/-- The marked linear-three row includes the actual full MS description. -/
theorem normalized_component_linearThree_of_classification
    (hC134 : FullLinearThreeClassification.{u} KnownSimple.IsKnownSimple)
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
    (normalized_component_msDescription_of_classification d hC134 hI hcore s n F hn hF hp)

/-- Apply the source exclusion on the same marking; no whole-core or
local MS callback remains, only the universal earlier C.1.34 theorem. -/
theorem normalized_component_linearThree_false_of_classification
    (hC134 : FullLinearThreeClassification.{u} KnownSimple.IsKnownSimple)
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
    (normalized_component_msDescription_of_classification d hC134 hI hcore s n F hn hF hp)

/-- The original natural B.5.1 row satisfies every clause of
C.2.7(g), with only the full earlier C.1.34 theorem still explicit. -/
theorem normalized_component_naturalThree_alternative
    (hC134 : FullLinearThreeClassification.{u} KnownSimple.IsKnownSimple)
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
  · exact normalized_component_linearThree_of_classification d hC134 hI hcore selection
      1 (ZMod 2) (by decide) (by simp) hp
  · exact normalized_component_linearThree_of_classification d hC134 hI hcore selection
      F.degree F.Carrier (Nat.succ_le_of_lt F.degree_pos) F.card_eq hp

/-- The original doubled-natural B.5.1 row satisfies every clause of
C.2.7(g), with only the full earlier C.1.34 theorem still explicit. -/
theorem normalized_component_doubleThree_alternative
    (hC134 : FullLinearThreeClassification.{u} KnownSimple.IsKnownSimple)
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
  · exact normalized_component_linearThree_of_classification d hC134 hI hcore selection
      1 (ZMod 2) (by decide) (by simp) hp
  · exact normalized_component_linearThree_of_classification d hC134 hI hcore selection
      F.degree F.Carrier (Nat.succ_le_of_lt F.degree_pos) F.card_eq hp

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
