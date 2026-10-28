module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherLinearMembership

/-! Both original linear-three parabolic residuals are nonshort local-family
members. Their native generation and proved marked-local placement force
field degree one in the actual natural and doubled-natural B.5 rows. -/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]

/-- An actual repeated-natural moved section or space of the original
normalizer action has field degree one. -/
theorem PreparedChosenModule.raw_linear_row_field_eq_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hfit : generalizedFitting K = pCore 2 K) (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (K : Set G)
    let H := K ⊔ R
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    ∀ hr : IsPReduced 2 W,
    letI := hr.elementary
    let C := centralizer (W : Set H)
    let qH := QuotientGroup.mk' C
    let I := (K.subgroupOf H).map qH
    let ρ := NormalElementaryQuotient.representation W qH
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ (J : Subgroup (H ⧸ C)) (_hIJ : I ≤ J)
      (s : MovedSection (ρ.comp J.subtype) (I.subgroupOf J))
      (F : BinaryField) (r : ℕ), 0 < r →
      (Nonempty (ActionEquiv (s.action.comp (I.subgroupOf J).subtype)
        (repeated (linearNatural F 3) r)) ∨
       Nonempty (ActionEquiv (s.space.toRepresentation.comp (I.subgroupOf J).subtype)
        (repeated (linearNatural F 3) r))) → F.degree = 1 := by
  intro S R H W hr
  let := hr.elementary
  intro C qH I ρ J hIJ s F r hrpos hm
  by_contra hn
  have hlarge : 1 < F.degree := by have := F.degree_pos; omega
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have houtM : ¬K ≤ M := by
    intro hKM
    exact hout (le_inf hK.1
      ((perfect_subgroup_centralizes_localModule hG T hempty hM hKM).trans
        (localModule_centralizer_le_partner T M hu)))
  obtain ⟨f,ec,hval,hproj,hf,hec,hcentral,_⟩ :=
    h.raw_component_normalizer_quotient hG T hM hJ hu hZ hZne hK hq hfit hout houtM
  obtain ⟨e,hker,hfam⟩ := h.raw_linear_residual_members hG T hZ hZne hK hq
    hr f ec hval hproj hf hec hcentral J hIJ s F r hrpos hlarge hm
  let q := e.toMonoidHom.comp f
  have hqs : Function.Surjective q := e.surjective.comp hf
  have hkq : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,hker]
    exact pCore_isPGroup
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hlarge
  have hR : IsPGroup 2 R := T.isPGroup'.to_le (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left))
  have hplace (P : Subgroup SL(3,F.Carrier))
      (hP : P ∈ ({pointParabolicSL F.Carrier,lineParabolicSL F.Carrier} : Set (Subgroup SL(3,F.Carrier)))) :
      let B := (P.comap q).map K.subtype
      (solvableResidual B).map B.subtype ≤ centralizer (Z1 : Set G) ⊓ Mc := by
    intro B
    let A := (solvableResidual B).map B.subtype
    have hA := hfam P hP
    let : Group.IsPerfect A := Chapter1.mem_L_isPerfect hA.2
    obtain ⟨hfitA,⟨er⟩⟩ := RawClassicalResidual.linear_data K q hqs hkq hfour P hP
    let : IsSimpleGroup SL(2,F.Carrier) :=
      Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple (by omega)
    let : IsSimpleGroup (A ⧸ pCore 2 A) := er.isSimpleGroup
    have hz : center (A ⧸ pCore 2 A) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (A ⧸ pCore 2 A)) inferInstance with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
    let hqa : IsQuasisimple (A ⧸ pCore 2 A) :=
      { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hnot : ¬ChapterC.IsShort A := by
      intro hs
      have hh := RawClassicalResidual.linear_nonshort K R inf_le_right hR W I f hval e hfour P hP
      exact hh (hs.of_mulEquiv
        ((solvableResidual B).equivMapOfInjective B.subtype B.subtype_injective).symm)
    exact h.raw_nonshort_slTwo_le_marked hG T hempty hM hJ hu hZ hZne hA hqa hfitA hnot F.Carrier er
  let : Group.IsNilpotent q.ker := hkq.isNilpotent
  have hgen := congrArg (Subgroup.map K.subtype)
    (Matrix.PSL3.LinearThree.preimage_residuals_generate q hqs F.card_eq hlarge)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hgen
  rw [map_embedded_solvableResidual_of_hom,map_embedded_solvableResidual_of_hom] at hgen
  apply hout
  rw [←hgen]
  exact sup_le (hplace _ (Or.inl rfl)) (hplace _ (Or.inr rfl))

/-- The genuine B.5 classifier on the original normalizer image, with both
linear-three rows restricted to the binary field. The same reduced-module
instance is used in the representation, classifier and row exclusions. -/
theorem PreparedChosenModule.raw_linear_source_rows_binary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hfit : generalizedFitting K = pCore 2 K) (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (K : Set G)
    let H := K ⊔ R
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    ∃ hr : IsPReduced 2 W,
    letI := hr.elementary
    let C := centralizer (W : Set H)
    let qH := QuotientGroup.mk' C
    let I := (K.subgroupOf H).map qH
    let ρ := NormalElementaryQuotient.representation W qH
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := offenderSubgroup ρ
    pCore 2 H = R.subgroupOf H ⊓ C ∧ I = generalizedFitting (H ⧸ C) ∧
      IsQuasisimple I ∧ IsFFModule ρ ∧
    ∃ (_hIJ : I ≤ J)
      (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp J.subtype) (I.subgroupOf J)),
      (∀ F : BinaryField,
        ActionEquiv (c.sectionData.action.comp (I.subgroupOf J).subtype)
          (linearNatural F 3) → F.degree = 1) ∧
      (∀ F : BinaryField,
        ActionEquiv (c.sectionData.space.toRepresentation.comp (I.subgroupOf J).subtype)
          (repeated (linearNatural F 3) 2) → F.degree = 1) := by
  intro S R H W
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have houtM : ¬K ≤ M := by
    intro hKM
    exact hout (le_inf hK.1
      ((perfect_subgroup_centralizes_localModule hG T hempty hM hKM).trans
        (localModule_centralizer_le_partner T M hu)))
  obtain ⟨hr,hcore,hf,hqi,hff,hIJ,⟨c⟩⟩ :=
    h.raw_component_normalizer_source hG T hM hJ hu hZ hZne hK hq hfit hout houtM
  let := hr.elementary
  refine ⟨hr,hcore,hf,hqi,hff,hIJ,c,?_,?_⟩
  · intro F e
    apply h.raw_linear_row_field_eq_one hG T hempty hM hJ hu hZ hZne hK hq hfit hout
      hr _ hIJ c.sectionData F 1 (by decide)
    apply Or.inl
    refine ⟨⟨e.groupEquiv,e.linearEquiv.trans
      (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 3 → F.Carrier)).symm,?_⟩⟩
    intro g v
    funext i
    exact e.intertwines g v
  · intro F e
    exact h.raw_linear_row_field_eq_one hG T hempty hM hJ hu hZ hZne hK hq hfit hout
      hr _ hIJ c.sectionData F 2 (by decide) (Or.inr ⟨e⟩)

end CFSG.Quasithin.Chapter15.Section01
