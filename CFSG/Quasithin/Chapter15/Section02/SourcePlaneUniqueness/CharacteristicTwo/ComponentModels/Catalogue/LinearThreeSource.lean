module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeSmallMS
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.SourceAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ComplementExclusion

/-!
# Excluding the original marked linear-three rows

The original Omega action constructs the NI action and its exact kernel.
Binary field recognition precedes the small C.1.34 application, which keeps
the original X, R, field and Sylow markings. The corrected small-action
argument then supplies the canonical-seed commutator contradiction. The
component's escape from Mc is derived from the genuine earlier Kc orbit.

Both natural and doubled-natural moved-section rows are excluded on this
same selected component. No component-escape, action-kernel, factor,
commutator or full-field classification callback is added. The original
earlier action, plane involution, Kc orbit and no-chi inputs retain their
source owners; the small MS classification is discharged by qt-rank-two-ms93
at the final Theorem E assembly.

Source: Aschbacher--Smith C.2.7(g), pp.145--147, and original 15.2.23,
pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding ChapterD ChapterD.UniqueFactor
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The literal marked linear-three row is impossible from the earlier
source inputs and the existing small MS classifier. All local premises of
the completed small-action contradiction are constructed here. -/
theorem normalized_component_linearThree_false_from_preceding
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (s : Normalized H M I X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) : False := by
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  have h := normalized_component_input (hsource := hsource) hI hcore s
  have hn1 := linearThree_degree_eq_one_of_star_parabolic d hI h n F hn hF hp
  subst n
  have hms := normalized_component_msDescription_of_small_classification
    d hC134 hI hcore s 1 F hn hF hp
  let b : LinearThree.Branch M I X 1 F := ⟨h,hn,hF,hp,hms⟩
  obtain ⟨e⟩ := ho.2.2.2.1
  exact SmallActionsSource.binary_component_false_from_preceding d horbit hI hfit
    e b (b.binary_not_le_partner d horbit hI) f hker


/-- Exclude the original natural-natural moved-section row using its proved
parabolic marking and the completed corrected small-action contradiction. -/
theorem normalized_component_naturalThree_false_from_preceding
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
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
          (T : Subgroup _) = ⊤) ∧ OuterNaturalAction s.action)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) : False := by
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  obtain ⟨_,hp⟩ | ⟨_,hp⟩ := normalized_component_naturalThree_parabolic
    (hsource := hsource) hI hcore selection hno hCJ s F a hext
  · exact normalized_component_linearThree_false_from_preceding d hC134 horbit hI hfit
      selection 1 (ZMod 2) (by decide) (by simp) hp hNI ha hi
  · exact normalized_component_linearThree_false_from_preceding d hC134 horbit hI hfit
      selection F.degree F.Carrier (Nat.succ_le_of_lt F.degree_pos) F.card_eq hp hNI ha hi


/-- Exclude the original double-natural moved-section row using its proved
parabolic marking and the completed corrected small-action contradiction. -/
theorem normalized_component_doubleThree_false_from_preceding
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
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
        (repeated (linearNatural F 3) 2))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) : False := by
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  obtain ⟨_,hp⟩ | ⟨_,hp⟩ := normalized_component_doubleThree_parabolic
    (hsource := hsource) hI hcore selection hno hCJ s F ht a
  · exact normalized_component_linearThree_false_from_preceding d hC134 horbit hI hfit
      selection 1 (ZMod 2) (by decide) (by simp) hp hNI ha hi
  · exact normalized_component_linearThree_false_from_preceding d hC134 horbit hI hfit
      selection F.degree F.Carrier (Nat.succ_le_of_lt F.degree_pos) F.card_eq hp hNI ha hi


end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
