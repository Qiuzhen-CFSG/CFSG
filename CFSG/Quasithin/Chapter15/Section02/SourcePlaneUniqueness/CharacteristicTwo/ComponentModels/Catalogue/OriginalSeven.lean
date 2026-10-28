module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingSeven
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedEmbedding

/-!
# Seven-letter coordinates on the original moved subgroup

The original U = [⟨ZS^X⟩,X] lies in the star moved subgroup. Its noncentrality
and the actual Irr⁺ conclusion force equality. In the remaining seven-letter
row, splitting of the odd permutation module removes the central factor,
giving natural coordinates on all of U rather than just a quotient section.
The coordinates intertwine conjugation by the whole XR, preserve the original
alternating component, and identify C_XR(U) with the literal star kernel.

The source consumer retains the same selected X and full B.5.1 conclusion.
The seven-letter exclusion, cubic symplectic branch, full KS placement and
final source contradiction remain to be established.

Source: Aschbacher--Smith original 15.2.23, printed pp.1116--1117;
C.2.7, pp.145--147, and B.5.1, pp.99--103.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The noncentral original U fills the actual Irr⁺ moved subgroup. -/
theorem original_U_eq_star_moved
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hi : IsIrrPlus ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) s.space.toSubmodule) :
    (U X ZS).subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2) =
      ⁅starV X ((M ⊓ I).pCoreIn 2), X.subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2)⁆ := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let C := X.subgroupOf J
  let B := offenderSubgroup (starRepresentation X R)
  let L := (starImage X R X).subgroupOf B
  let W := (U X ZS).subgroupOf J
  let A : Submodule (ZMod 2) (Additive (starV X R)) :=
    AddSubgroup.toZModSubmodule 2 (W.subgroupOf (starV X R)).toAddSubgroup
  let ρ := (starRepresentation X R).comp B.subtype
  have hW := original_U_le_star_moved d hI hfit hXI hn hout h
  have hs : s.space.toSubmodule = NormalElementaryQuotient.commutatorSpace (starV X R) C := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (starV X R)
      (QuotientGroup.mk' (starKernel X R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _), s.space_eq]
    change subspaceCommutator ρ ⊤ L = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  have hAS : A ≤ s.space.toSubmodule := by
    rw [hs]
    exact fun _ hu => hW hu
  have hstab : L ≤ subspaceStabilizer ρ A := by
    apply le_subspaceStabilizer
    intro l hl v hv
    obtain ⟨x,hx,he⟩ := hl
    have hlq : (l : StarQuotient X R) =
        QuotientGroup.mk' (starKernel X R) ⟨x,mem_sup_left hx⟩ := he.symm
    change ((starRepresentation X R l.val v).toMul : G) ∈ U X ZS
    rw [hlq,starRepresentation_apply]
    exact (mem_normalizer_iff.mp
      (U_normalized d hI hn (mem_sup_left hx)) _).mp hv
  have hnon : ¬ A ≤ fixedSpace ρ L := by
    intro hfix
    have hcentral : X ≤ centralizer (U X ZS : Set G) := by
      intro x hx u hu
      let uJ : J := ⟨u,(U_le_intersection_radical d hI hfit hXI hu |> mem_sup_right)⟩
      let v : Additive (starV X R) := Additive.ofMul
        ⟨uJ,commutator_le_left _ _ (hW hu)⟩
      let l : L := (subgroupOfEquivOfLe hCJ).symm (toStarImage X R ⟨x,hx⟩)
      have hh := congrArg (fun w : Additive (starV X R) => (w.toMul.val : G))
        (hfix (show v ∈ A from hu) l)
      change (((starRepresentation X R
        (QuotientGroup.mk' (starKernel X R) ⟨x,mem_sup_left hx⟩) v).toMul : J) : G) = u at hh
      rw [starRepresentation_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hred := U_reduced_in_component_radical d hI hfit hXI hn hout h
    exact hred.2.2 (by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
      intro x hx u hu
      exact Subtype.ext (hcentral hx u hu))
  have he : A = s.space.toSubmodule :=
    (hi.eq_or_le_fixedSpace ρ hstab hAS).resolve_right hnon
  apply le_antisymm hW
  intro w hw
  let v : Additive (starV X R) := Additive.ofMul ⟨w,commutator_le_left _ _ hw⟩
  have hv : v ∈ s.space.toSubmodule := by rw [hs]; exact hw
  exact (show v ∈ A from he ▸ hv)
include d in
/-- Natural permutation coordinates on the whole original U, with the same
star map, component marking and full XR conjugation action. -/
theorem normalized_natural_originalSeven_coordinates
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hc : RemainingNaturalActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) s) :
    ∃ e : StarQuotient X ((M ⊓ I).pCoreIn 2) ≃* Equiv.Perm (Fin 7),
      ∃ A : U X ZS ≃* Multiplicative (BinaryPermutation.natural (Fin 7)),
        (starImage X ((M ⊓ I).pCoreIn 2) X).map e.toMonoidHom = alternatingGroup (Fin 7) ∧
        (X ⊔ (M ⊓ I).pCoreIn 2 ≤ normalizer (U X ZS : Set G)) ∧
        (∀ (j : (X ⊔ (M ⊓ I).pCoreIn 2 : Subgroup G)) (u v : U X ZS),
          (v : G) = (j : G) * (u : G) * (j : G)⁻¹ →
          (A v).toAdd = BinaryPermutation.naturalRepresentation (Fin 7)
            (e (QuotientGroup.mk' (starKernel X ((M ⊓ I).pCoreIn 2)) j)) (A u).toAdd) := by
  cases hc with
  | irreducible hi hf hirr hr hext =>
    cases hr with
    | symmetric n hn a ho hr =>
      rcases hn with rfl | rfl
      · exact (normalized_alternatingFive_false d hI hcore selection hno
          ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv)).elim
      let R := (M ⊓ I).pCoreIn 2
      let J := X ⊔ R
      let B := offenderSubgroup (starRepresentation X R)
      let C := X.subgroupOf J
      let L := (starImage X R X).subgroupOf B
      let h := normalized_component_input (hsource := hsource) hI hcore selection
      let eA := (subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv
      have hzC : Nat.card (center (X ⧸ pCore 2 X)) ≤ 3 := by
        rcases coreQuotient_center_card_from_source h with hz | hz <;> omega
      have hnX := alternating_component_normalized (hsource := hsource) hI selection.toSelected
        hzC (Or.inr rfl) (alternatingStarCoreCenterEquiv h (by decide) eA)
      have hout := alternating_star_not_le_partner d horbit hI hcore selection (Or.inr rfl) eA
      have hU := original_U_eq_star_moved d hI hfit selection.component.1 hnX hout h hCJ s hi
      have hUJ : U X ZS ≤ J :=
        (U_le_intersection_radical d hI hfit selection.component.1).trans le_sup_right
      have hred := U_reduced_in_component_radical d hI hfit
        selection.component.1 hnX hout h
      have hnU : J ≤ normalizer (U X ZS : Set G) :=
        (normal_subgroupOf_iff_le_normalizer hUJ).mp hred.1.normal
      let W := ⁅starV X R,C⁆
      let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
        (inclusion (commutator_le_left (starV X R) C)) (inclusion_injective _)
      have hs : s.space.toSubmodule = NormalElementaryQuotient.commutatorSpace (starV X R) C := by
        rw [NormalElementaryQuotient.commutatorSpace_eq (starV X R)
          (QuotientGroup.mk' (starKernel X R)) (QuotientGroup.mk'_surjective _)
          (QuotientGroup.ker_mk' _),s.space_eq]
        change subspaceCommutator ((starRepresentation X R).comp B.subtype) ⊤ L = _
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
      let jU : U X ZS ≃* W :=
        (subgroupOfEquivOfLe hUJ).symm.trans (MulEquiv.subgroupCongr hU)
      let A := jU.trans E.toAddEquiv.toMultiplicativeRight
      obtain ⟨e,he,ha⟩ := natural_permutation_star_coordinates h hCJ s (Or.inr rfl) a hr
      have htop : B = ⊤ := natural_permutation_offender_eq_top h hCJ s (Or.inr rfl) a hr
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
        let b : B := ⟨QuotientGroup.mk' (starKernel X R) j,htop ▸ mem_top _⟩
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

variable {R : Subgroup G}

/-- Full symmetric coordinates on the original subgroup U, retaining the
literal star quotient, component marking and ambient conjugation action. -/
@[expose] def OriginalSevenCoordinates (X R ZS : Subgroup G) : Prop :=
  ∃ e : StarQuotient X R ≃* Equiv.Perm (Fin 7),
    ∃ A : U X ZS ≃* Multiplicative (BinaryPermutation.natural (Fin 7)),
      (starImage X R X).map e.toMonoidHom = alternatingGroup (Fin 7) ∧
      (X ⊔ R ≤ normalizer (U X ZS : Set G)) ∧
      (∀ (j : (X ⊔ R : Subgroup G)) (u v : U X ZS),
        (v : G) = (j : G) * (u : G) * (j : G)⁻¹ →
        (A v).toAdd = BinaryPermutation.naturalRepresentation (Fin 7)
          (e (QuotientGroup.mk' (starKernel X R) j)) (A u).toAdd)

omit d [Finite G] in
/-- The seven-letter model has order 64 on the original U itself. -/
theorem OriginalSevenCoordinates.card (h : OriginalSevenCoordinates X R ZS) :
    Nat.card (U X ZS) = 64 := by
  obtain ⟨e,A,hm,hn,ha⟩ := h
  rw [Nat.card_congr A.toEquiv,Nat.card_congr Multiplicative.toAdd,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)]
  decide

omit d [Finite G] in
/-- The kernel of the original star map is exactly the centralizer of the
whole original U, inside XR. -/
theorem OriginalSevenCoordinates.centralizer_eq_starKernel
    (h : OriginalSevenCoordinates X R ZS) :
    (centralizer (U X ZS : Set G)).subgroupOf (X ⊔ R) = starKernel X R := by
  obtain ⟨e,A,hm,hn,ha⟩ := h
  let q := QuotientGroup.mk' (starKernel X R)
  ext j
  constructor
  · intro hj
    have hact : BinaryPermutation.naturalRepresentation (Fin 7) (e (q j)) = 1 := by
      apply LinearMap.ext
      intro w
      let u := A.symm (Multiplicative.ofAdd w)
      have hc : (u : G) = (j : G) * (u : G) * (j : G)⁻¹ := by
        have hc' : (u : G) * (j : G) = (j : G) * (u : G) := hj u u.property
        rw [← hc', mul_inv_cancel_right]
      have hh := ha j u u hc
      have hu : (A u).toAdd = w := A.apply_symm_apply _
      rw [hu] at hh
      exact hh.symm
    have he : e (q j) = 1 := BinaryPermutation.naturalRepresentation_injective
      (Fin 7) (by decide) (by simpa only [map_one] using hact)
    have hq : q j = 1 := e.injective (by simpa only [map_one] using he)
    exact (QuotientGroup.eq_one_iff _).mp hq
  · intro hj u hu
    let uU : U X ZS := ⟨u,hu⟩
    let v : U X ZS := ⟨(j : G) * u * (j : G)⁻¹,
      le_normalizer_iff.mp hn j j.property u hu⟩
    have hh := ha j uU v rfl
    have hq : q j = 1 := (QuotientGroup.eq_one_iff _).mpr hj
    change (A v).toAdd = BinaryPermutation.naturalRepresentation (Fin 7)
      (e (q j)) (A uU).toAdd at hh
    rw [hq, map_one, map_one] at hh
    have hv : v = uU := A.injective (Multiplicative.toAdd.injective hh)
    have he := congrArg Subtype.val hv
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

include d in
/-- The original source retains the same component and full moved section.
In the seven-letter branch, the natural action is now on the original U,
with its full XR-action and literal star projection. -/
theorem exists_source_originalSeven_or_cubicSymplectic_component
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    ∃ X : Subgroup G, Normalized H M I X ∧
      let R := (M ⊓ I).pCoreIn 2
      let ρ := starRepresentation X R
      let J := offenderSubgroup ρ
      starImage X R X ≤ J ∧
        ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp J.subtype) ((starImage X R X).subgroupOf J),
          ((RemainingNaturalActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData ∧
            FullSevenPermutationCoordinates c.sectionData ∧ OriginalSevenCoordinates X R ZS ∧
            (centralizer (U X ZS : Set G)).subgroupOf (X ⊔ R) = starKernel X R) ∨
            (Nonempty (starImage X R X ≃* alternatingGroup (Fin 6)) ∧
              Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
              quadraticRatio c.sectionData.action = 2 / 3)) := by
  obtain ⟨X,selection,hCJ,c,hc⟩ := exists_source_seven_or_cubicSymplectic_component
    d hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  refine ⟨X,selection,hCJ,c,?_⟩
  rcases hc with ⟨hn,hcoords⟩ | hs
  · have hU : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ZS :=
      normalized_natural_originalSeven_coordinates d horbit
        hI hfit hcore selection hno hCJ c.sectionData hn
    exact .inl ⟨hn,hcoords,hU,hU.centralizer_eq_starKernel⟩
  · exact .inr hs

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
