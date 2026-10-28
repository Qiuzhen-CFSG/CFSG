module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.SevenFive
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.SevenGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.Alternating
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.OriginalSeven

/-!
# Full natural coordinates on the original seven-letter subgroup

The source symmetric action has degree five or seven.  The five-letter row
is excluded by the original radical marking.  In degree seven, splitting
of the odd permutation module removes its central factor and identifies
the entire original U with the natural permutation module.  The coordinates
intertwine the whole XR action and keep its literal alternating component.

Source: Aschbacher--Smith, proof of 15.2.23, printed pp.1116--1117,
refs/quasithin.pdf. The original U, QI and star markings are retained.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 ComponentCatalogue PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The literal symmetric action gives natural coordinates on all of original U. -/
theorem ResidualInput.normalized_symmetric_originalSeven_coordinates_of_eq
    (r : ResidualInput hsource H B)
    (heq : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
  offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
  (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
  ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
    (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hi : IsIrrPlus
  ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
    (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
  ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
    (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) s.space.toSubmodule)
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
  ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
    (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))))
  (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))
    (hr : quadraticRatio s.action = 1) :
    ∃ e : StarQuotient X ((M ⊓ I).pCoreIn 2) ≃* Equiv.Perm (Fin 7),
  ∃ A : U X ⁅V,B⁆ ≃* Multiplicative (BinaryPermutation.natural (Fin 7)),
    (starImage X ((M ⊓ I).pCoreIn 2) X).map e.toMonoidHom = alternatingGroup (Fin 7) ∧
    (X ⊔ (M ⊓ I).pCoreIn 2 ≤ normalizer (U X ⁅V,B⁆ : Set G)) ∧
    (∀ (j : (X ⊔ (M ⊓ I).pCoreIn 2 : Subgroup G)) (u v : U X ⁅V,B⁆),
      (v : G) = (j : G) * (u : G) * (j : G)⁻¹ →
      (A v).toAdd = BinaryPermutation.naturalRepresentation (Fin 7)
        (e (QuotientGroup.mk' (starKernel X ((M ⊓ I).pCoreIn 2)) j)) (A u).toAdd) := by
  rcases hn with rfl | rfl
  · exact (r.normalized_alternatingFive_false hI hcore selection hno
      ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv)).elim
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let Joff := offenderSubgroup (starRepresentation X R)
  let C := X.subgroupOf J
  let L := (starImage X R X).subgroupOf Joff
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  let eA := (subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv
  have hzC : Nat.card (center (X ⧸ pCore 2 X)) ≤ 3 := by
    rcases coreQuotient_center_card_from_source h with hz | hz <;> omega
  have hnX := alternating_component_normalized (hsource := hsource) hI selection.toSelected
    hzC (Or.inr rfl) (alternatingStarCoreCenterEquiv h (by decide) eA)
  have hout := r.alternating_component_not_le_partner_of_eq heq hI hcore selection
    (Or.inr rfl) (alternatingStarCoreCenterEquiv h (by decide) eA)
  have hU := r.original_U_eq_star_moved hI hfit selection.component.1 hnX hout h hCJ s hi
  have hUJ : U X ⁅V,B⁆ ≤ J :=
    (EqualityRow.Linear.U_le_intersection_radical r hI hfit selection.component.1).trans le_sup_right
  have hred := EqualityRow.Linear.U_reduced_in_component_radical r hI hfit
    selection.component.1 hnX hout h
  have hnU : J ≤ normalizer (U X ⁅V,B⁆ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hUJ).mp hred.1.normal
  let W := ⁅starV X R,C⁆
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left (starV X R) C)) (inclusion_injective _)
  have hs : s.space.toSubmodule = NormalElementaryQuotient.commutatorSpace (starV X R) C := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (starV X R)
      (QuotientGroup.mk' (starKernel X R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _),s.space_eq]
    change subspaceCommutator ((starRepresentation X R).comp Joff.subtype) ⊤ L = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  let m : Additive W ≃ₗ[ZMod 2] s.space.toSubmodule :=
    (NormalElementaryQuotient.commutatorSpaceEquiv (starV X R) C).trans
      (LinearEquiv.ofEq _ _ hs.symm)
  have hsplit := ChapterB.QuasisimpleSource.ExtensionConsequences.symmetricOdd_isCompl
    s hi (Or.inr rfl) a
  have hz : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact (disjoint_iff.mp hsplit.disjoint).le
      ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩
  let qE := s.central.toSubmodule.quotEquivOfEqBot hz
  let E := m.trans (qE.symm.trans a.action.linearEquiv)
  let jU : U X ⁅V,B⁆ ≃* W :=
    (subgroupOfEquivOfLe hUJ).symm.trans (MulEquiv.subgroupCongr hU)
  let A := jU.trans E.toAddEquiv.toMultiplicativeRight
  obtain ⟨e,he,ha⟩ := natural_permutation_star_coordinates h hCJ s (Or.inr rfl) a hr
  have htop : Joff = ⊤ := natural_permutation_offender_eq_top h hCJ s (Or.inr rfl) a hr
  refine ⟨e,A,?_,hnU,?_⟩
  · apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change e x ∈ alternatingGroup (Fin 7)
      rw [he ⟨x,hx⟩]
      exact (a.subgroupEquiv _).property
    · intro y hy
      let l := a.subgroupEquiv.symm ⟨y,hy⟩
      let x := subgroupOfEquivOfLe hCJ l
      refine ⟨x,x.property,?_⟩
      change e x = y
      rw [he x]
      change (a.subgroupEquiv ((subgroupOfEquivOfLe hCJ).symm
        (subgroupOfEquivOfLe hCJ (a.subgroupEquiv.symm ⟨y,hy⟩))) : Equiv.Perm (Fin 7)) = y
      rw [MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply]
  · intro j u v hv
    let b : Joff := ⟨QuotientGroup.mk' (starKernel X R) j,htop ▸ mem_top _⟩
    have hm : s.space.toRepresentation b (m (Additive.ofMul (jU u))) =
        m (Additive.ofMul (jU v)) := by
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change (((starRepresentation X R (QuotientGroup.mk' (starKernel X R) j)
        (Additive.ofMul ⟨_,_⟩)).toMul : J) : G) = (v : G)
      rw [starRepresentation_apply]
      exact hv.symm
    have hq : qE.symm (m (Additive.ofMul (jU v))) =
        s.central.quotientRepresentation b (qE.symm (m (Additive.ofMul (jU u)))) := by
      change Submodule.Quotient.mk (m (Additive.ofMul (jU v))) =
        Submodule.Quotient.mk (s.space.toRepresentation b (m (Additive.ofMul (jU u))))
      exact congrArg s.central.toSubmodule.mkQ hm.symm
    exact (congrArg a.action.linearEquiv hq).trans (ha b _)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
