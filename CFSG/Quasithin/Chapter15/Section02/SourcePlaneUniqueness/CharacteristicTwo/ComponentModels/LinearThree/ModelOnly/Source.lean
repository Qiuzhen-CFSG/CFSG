module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.ModelOnly.Complement
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeDegree
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeMarking
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.SourceAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ComplementExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.Escape

/-!
# The original linear-three source rows before MS classification

The source star parabolic yields the full component quotient and its
unclassified MS input pair. Binary field recognition is already proved
from these original data. The pair supplies escape from Mc through MS3;
no classified MS alternative is used. The model-only quotient action then
constructs the complementary cubic factor excluded by the canonical seed.

The final applications exclude the literal linear-three, natural and
doubled-natural rows with the original selected X, R = O2(M intersect I),
NI action, plane involution and Kc orbit. The earlier action, orbit and
plane premises remain explicit and retain their existing producers. No
full catalogue exhaustion or other branch is asserted. Existing Branch,
Catalogue/LinearThreeSource and shared assembly APIs are unchanged.

Source: Aschbacher--Smith C.2.7(g), p.145, and 15.2.23, printed p.1116.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Escape uses the original MS input hypotheses, without any classified
core alternative. The actual source constructs this pair before C.1.34. -/
theorem Branch.binary_not_le_partner_of_msPair
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F)
    (hms : LinearThreeMSPair KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) 1 F) :
    ¬ X ≤ Mc := by
  let A := X.subgroupOf I
  let a : A ≃* X := subgroupOfEquivOfLe b.input.component.1
  have hA : A.map I.subtype = X := map_subgroupOf_eq_of_le b.input.component.1
  obtain ⟨e⟩ := b.model
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [←Nat.card_eq_fintype_card,pow_one] using b.field_card)).symm
  let eA : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.PSL :=
    (((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e).trans
      (Atlas.fieldEquivSL 3 f)).trans Matrix.PSL3Two.equiv
  have hh := d.linearThree_ms_component_not_le_partner horbit hI
    b.input.component.2 eA (isPGroup_pCoreIn 2 (M ⊓ I)) (hA.symm ▸ hms)
  simpa only [map_subgroupOf_eq_of_le b.input.component.1] using hh

open SmallActionsSource ChapterD.UniqueFactor in
/-- The binary full-quotient model supplies the complementary cubic factor;
the canonical-seed normalizer argument excludes it on the original I and X. -/
theorem Branch.binary_false_from_preceding
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) : False := by
  have hST : smallActionS T ZS < (T : Subgroup G) := lt_of_le_of_ne inf_le_left (by
    intro he
    have hi := (d.escape_index hI).2
    change (smallActionS T ZS).relIndex (T : Subgroup G) = 2 at hi
    rw [he,relIndex_self] at hi
    omega)
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt hST
  obtain ⟨hLK,hperfect,hcard,hSL,hMI,hnot⟩ :=
    b.binary_factor_data_of_action d hI hout f hker
  have hKL := (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans hMI
  have hn := (normal_subgroupOf_iff_le_normalizer hLK).mpr hKL
  obtain ⟨p,he⟩ := residualPair_with_first d hI ⟨hLK,hn,hperfect,hcard⟩ hSL t ht htS
  have hpn : Mc ⊓ I ≤ normalizer (p.K₁ : Set G) := by rwa [he]
  have hK := orbit_eq_of_pair_factor_normalized d horbit hI hnot p hpn
  have hC := source_15_2_21_2_from_preceding d hK
  obtain ⟨E,hEK,hp,hc,hS,hKE,_,hcomm⟩ := b.binary_complementary_factor d hI hout
    (b.binary_normal_of_action d hI hout f hker)
  have hE : E ∈ normalCubicResiduals (smallActionK H) :=
    ⟨hEK,(normal_subgroupOf_iff_le_normalizer hEK).mpr hKE,hp,hc⟩
  exact canonical_seed_exclusion_any_factor d hI hfit e hC
    (b.binary_source_residual_quotient d hI hout f hker hC) hE hS
    (b.binary_commutator_of_action d hI hout f hker hC hS hp hcomm)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original 15.2.23 linear-three row is excluded before C.1.34: its
full quotient and genuine MS input pair follow from the actual star model.
The preceding action, orbit and plane-involution hypotheses stay explicit. -/
theorem normalized_component_linearThree_false_of_core_model
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
  have hpar := hp
  obtain ⟨estar,_⟩ := hp
  have hms := normalized_component_msPair_of_star_model d hI hcore s 1 F hn hF estar
  let b : LinearThree.ModelOnly.Branch M I X 1 F := ⟨h,hn,hF,hpar,hms.model⟩
  obtain ⟨e⟩ := ho.2.2.2.1
  exact b.binary_false_from_preceding d horbit hI hfit e
    (b.binary_not_le_partner_of_msPair d horbit hI hms) f hker

/-- Exclude the original natural-natural moved-section row using its proved
parabolic marking and the completed corrected small-action contradiction. -/
theorem normalized_component_naturalThree_false_of_core_model
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
  · exact normalized_component_linearThree_false_of_core_model d horbit hI hfit
      selection 1 (ZMod 2) (by decide) (by simp) hp hNI ha hi
  · exact normalized_component_linearThree_false_of_core_model d horbit hI hfit
      selection F.degree F.Carrier (Nat.succ_le_of_lt F.degree_pos) F.card_eq hp hNI ha hi


/-- Exclude the original double-natural moved-section row using its proved
parabolic marking and the completed corrected small-action contradiction. -/
theorem normalized_component_doubleThree_false_of_core_model
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
  · exact normalized_component_linearThree_false_of_core_model d horbit hI hfit
      selection 1 (ZMod 2) (by decide) (by simp) hp hNI ha hi
  · exact normalized_component_linearThree_false_of_core_model d horbit hI hfit
      selection F.degree F.Carrier (Nat.succ_le_of_lt F.degree_pos) F.card_eq hp hNI ha hi


end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
