module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ComponentCentralizer
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.BinaryOffender.CentralImageMoved
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# The moved module of an alternating-five component in B.5

The full B.5.1 and adequate B.5.6 alternatives give an Irr⁺ moved module for
an ordinary component of order sixty. In product rows, a component lies
in one factor. The SL₃ rows are excluded by their simple groups and orders;
the remaining natural SL₂ and S₅ modules restrict irreducibly. Central-image
lifting preserves the literal moved space, including the hyperplane row.
The outer A₆–C₃ row has only its A₆ component and is excluded by order.

The actual consumer is the original A₅ action on the omega span in 12.3.8.
Source: Aschbacher–Smith B.5.1, B.5.6, pp.99–105, and 12.3.8, p.810.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V W : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The original quotient image of a containing space determines the moved layer. -/
theorem moved_irrPlus_of_quotient_image
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D)
    [Group.IsPerfect C] [Nontrivial C]
    (U : Subrepresentation ρ) (hm : subspaceCommutator ρ ⊤ C ≤ U.toSubmodule)
    (hi : IsIrreducible (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype))
    (hf : Function.Injective (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype)) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) := by
  let f : U.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule :=
    ((fixed ρ).toSubmodule.mkQ.comp U.toSubmodule.subtype).codRestrict _
      (fun v => ⟨v,v.property,rfl⟩)
  apply moved_irrPlus_of_central_image ρ ((fixed ρ).quotientImage U).toRepresentation
    C U hm f
  · rintro ⟨v,w,hw,rfl⟩
    exact ⟨⟨w,hw⟩,rfl⟩
  · intros; rfl
  · intro v hv c
    apply Subtype.ext
    have hz : (fixed ρ).toSubmodule.mkQ v = 0 := congrArg Subtype.val hv
    exact (Submodule.Quotient.mk_eq_zero _).mp hz c
  · exact hi
  · exact hf

private theorem component_top_of_simple [IsSimpleGroup D]
    {C : Subgroup D} (hC : IsComponent D C) : C = ⊤ :=
  (hC.1.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left hC.isCComponent.ne_bot

private theorem component_le_factor {A B C : Subgroup D}
    (h : InternalProduct A B) (hC : IsComponent D C) : C ≤ A ∨ C ≤ B := by
  let := h.swap.second_normal
  let := h.second_normal
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [h.sup_eq_top] at hc
  have hcc : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (C : Set D) ⊆ (⊤ : Subgroup D) from Set.subset_univ _)))
  let := hC.2
  rw [commutator_eq_self] at hcc
  exact (hC.isCComponent.ne_bot hcc).elim

private theorem linear_three_card_gt_60 (F : BinaryField) :
    60 < Nat.card SL(3,F.Carrier) := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
  have hb : 168 ≤ Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
      (Nat.card F.Carrier ^ 2 - 1) := by
    calc
      168 = 2^3 * (2^3-1) * (2^2-1) := by norm_num
      _ ≤ _ := by gcongr
  omega

private theorem linear_three_component_ne_60 (F : BinaryField) (ho : Odd F.degree)
    (e : D ≃* SL(3,F.Carrier)) {C : Subgroup D} (hC : IsComponent D C) :
    Nat.card C ≠ 60 := by
  let : IsSimpleGroup PSL(3,F.Carrier) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup D := (e.trans
    (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv F.card_eq ho)).isSimpleGroup
  rw [component_top_of_simple hC, Nat.card_congr Subgroup.topEquiv.toEquiv,
    Nat.card_congr e.toEquiv]
  exact ne_of_gt (linear_three_card_gt_60 F)

private theorem linear_two_component_top (F : BinaryField)
    (e : D ≃* SL(2,F.Carrier)) {C : Subgroup D} (hC : IsComponent D C)
    (hc : Nat.card C = 60) : C = ⊤ := by
  by_cases hd : F.degree = 1
  · let b := e.trans
      ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let : Finite D := Finite.of_equiv _ b.toEquiv.symm
    have h := card_subgroup_dvd_card C
    rw [hc,Nat.card_congr b.toEquiv] at h
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at h
  · have hl : 3 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have hd' : 2 ≤ F.degree := by have := F.degree_pos; omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
      norm_num at hp
      omega
    let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : IsSimpleGroup D := (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup
    exact component_top_of_simple hC

private def restrictAction {E : Type*} [Group E]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (e : ActionEquiv ρ σ) (C : Subgroup D) :
    ActionEquiv (ρ.comp C.subtype) (σ.comp (C.map e.groupEquiv.toMonoidHom).subtype) :=
  ⟨C.equivMapOfInjective e.groupEquiv.toMonoidHom e.groupEquiv.injective,
    e.linearEquiv,fun c v => e.intertwines c v⟩

private theorem linear_two_component_irreducible
    (σ : Representation (ZMod 2) D V) (F : BinaryField)
    (e : ActionEquiv σ (linearNatural F 2)) {C : Subgroup D}
    (hC : IsComponent D C) (hc : Nat.card C = 60) :
    IsIrreducible (σ.comp C.subtype) := by
  have he : C = ⊤ := linear_two_component_top F e.groupEquiv hC hc
  subst C
  apply (irreducible_comp_surjective_iff (⊤ : Subgroup D).subtype
    Subgroup.topEquiv.surjective σ).mpr
  exact ExtensionConsequences.irreducible_of_equiv e
    (ExtensionConsequences.linearNatural_irreducible F (by decide))

private theorem symmetric_five_component_irreducible
    (σ : Representation (ZMod 2) D V)
    (e : ActionEquiv σ (BinaryPermutation.naturalRepresentation (Fin 5)))
    {C : Subgroup D} (hC : IsComponent D C) :
    IsIrreducible (σ.comp C.subtype) := by
  let N := alternatingGroup (Fin 5)
  let : IsSimpleGroup N := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple N := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hN : IsComponent (Equiv.Perm (Fin 5)) N :=
    ⟨(inferInstance : N.Normal).isSubnormal,inferInstance⟩
  have hm := hC.map_equiv e.groupEquiv
  let := hm.2
  have heq : C.map e.groupEquiv.toMonoidHom = N := by
    apply hm.eq_of_le hN
    rw [←commutator_eq_self (H := C.map e.groupEquiv.toMonoidHom)]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  apply ExtensionConsequences.irreducible_of_equiv (restrictAction e C)
  rw [heq]
  exact BinaryPermutation.alternatingNatural_isIrreducible (by decide)

/-- A component of order sixty acts irreducibly on its prescribed B.5.6 factor image. -/
theorem SourceFactorCase.card60_component_irreducible
    {ρ : Representation (ZMod 2) D V} {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) {C : Subgroup A} (hC : IsComponent A C)
    (hc : Nat.card C = 60) :
    IsIrreducible ((((fixed ρ).quotientImage U).toRepresentation.comp A.subtype).comp C.subtype) := by
  cases h with
  | natural _ hn =>
    cases hn with
    | linearTwo F hn =>
      obtain ⟨e⟩ := hn
      exact linear_two_component_irreducible _ F e hC hc
    | symmetricFive hn =>
      obtain ⟨e⟩ := hn
      exact symmetric_five_component_irreducible _ e hC
    | linearThree F ho hn =>
      obtain ⟨e⟩ := hn
      exact (linear_three_component_ne_60 F ho e.groupEquiv hC hc).elim
  | doubleNatural F ho _ hn =>
    obtain ⟨e⟩ := hn
    exact (linear_three_component_ne_60 F ho e.groupEquiv hC hc).elim
  | exceptional _ hn =>
    exact (linear_three_component_ne_60 BinaryField.two (by decide) hn.natural.groupEquiv hC hc).elim


private theorem factor_component_moved {ρ : Representation (ZMod 2) D V}
    {A C : Subgroup D} {U : Subrepresentation ρ} (h : SourceFactorCase ρ A U)
    (hC : IsComponent D C) (hc : Nat.card C = 60) (hCA : C ≤ A) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) := by
  let := hC.2
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
  let e := subgroupOfEquivOfLe hCA
  let σ := ((fixed ρ).quotientImage U).toRepresentation
  have hi := h.card60_component_irreducible (hC.subgroupOf hCA)
    ((Nat.card_congr e.toEquiv).trans hc)
  have hm : subspaceCommutator ρ ⊤ A ≤ U.toSubmodule := by
    cases h with
    | natural he _ => exact he.ge
    | doubleNatural _ _ he _ => exact he.ge
    | exceptional he _ => exact he
  apply moved_irrPlus_of_quotient_image ρ C U
  · apply le_trans ?_ hm
    apply Submodule.span_mono
    rintro _ ⟨c,hc,v,hv,rfl⟩
    exact ⟨c,hCA hc,v,hv,rfl⟩
  · exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective
      (σ.comp C.subtype)).mp hi
  · intro a b hab
    have ha : (⟨a,hCA a.property⟩ : A) = ⟨b,hCA b.property⟩ := h.faithful hab
    exact Subtype.ext (congrArg (fun x : A => (x : D)) ha)

/-- The two-factor clause gives one Irr⁺ moved module for each A₅ component. -/
theorem SourceTwoFactorCase.card60_component_moved
    {ρ : Representation (ZMod 2) D V} (d : SourceTwoFactorCase ρ)
    {C : Subgroup D} (hC : IsComponent D C) (hc : Nat.card C = 60) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) := by
  rcases component_le_factor d.product hC with ha | hb
  · exact factor_component_moved d.firstCase hC hc ha
  · exact factor_component_moved d.secondCase hC hc hb

private theorem linear_natural_faithful (F : BinaryField) (n : ℕ)
    (σ : Representation (ZMod 2) D V) (e : ActionEquiv σ (linearNatural F n)) :
    Function.Injective σ := by
  intro a b hab
  apply e.groupEquiv.injective
  apply specialLinearNatural_injective n
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
  exact (e.intertwines a w).symm.trans
    ((congrArg e.linearEquiv (LinearMap.congr_fun hab w)).trans (e.intertwines b w))

/-- The SL₃ factor cannot contain A₅; the other hyperplane factor has one
natural reduced module. Its central kernel does not create another moved layer. -/
theorem HyperplaneCase.card60_component_moved
    {ρ : Representation (ZMod 2) D V} (d : HyperplaneCase ρ)
    {C : Subgroup D} (hC : IsComponent D C) (hc : Nat.card C = 60) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) := by
  rcases component_le_factor d.product hC with ha | hb
  · exact (linear_three_component_ne_60 BinaryField.two (by decide) d.firstEquiv
      (hC.subgroupOf ha) ((Nat.card_congr (subgroupOfEquivOfLe ha).toEquiv).trans hc)).elim
  cases d.secondCase with
  | linearThree r hr hn =>
    obtain ⟨e⟩ := hn
    exact (linear_three_component_ne_60 BinaryField.two (by decide) e.groupEquiv
      (hC.subgroupOf hb) ((Nat.card_congr (subgroupOfEquivOfLe hb).toEquiv).trans hc)).elim
  | linearTwo F hn =>
    obtain ⟨e⟩ := hn
    have heq := linear_two_component_top F e.groupEquiv (hC.subgroupOf hb)
      ((Nat.card_congr (subgroupOfEquivOfLe hb).toEquiv).trans hc)
    have hCB : C = d.second := by
      have hh := congrArg (map d.second.subtype) heq
      simpa only [map_subgroupOf_eq_of_le hb,← MonoidHom.range_eq_map,Subgroup.range_subtype] using hh
    subst C
    let := hC.2
    let : Nontrivial d.second := (nontrivial_iff_ne_bot _).mpr hC.isCComponent.ne_bot
    let U : Subrepresentation (ρ.comp d.second.subtype) :=
      ⟨d.secondSpace.toSubmodule,fun c v hv => d.secondSpace.apply_mem_toSubmodule c hv⟩
    let σ := reducedAction U.toRepresentation
    have hi : IsIrreducible σ := ExtensionConsequences.irreducible_of_equiv e
      (ExtensionConsequences.linearNatural_irreducible F (by decide))
    have hfaith : Function.Injective σ := linear_natural_faithful F 2 _ e
    have hm : subspaceCommutator (ρ.comp d.second.subtype) ⊤ (⊤ : Subgroup d.second) ≤
        U.toSubmodule := by
      rw [subspaceCommutator_comp_map,← MonoidHom.range_eq_map,Subgroup.range_subtype]
      exact d.secondSpace_eq.ge
    have ht := moved_irrPlus_of_central_image (ρ.comp d.second.subtype) σ
      (⊤ : Subgroup d.second) U hm (fixed U.toRepresentation).toSubmodule.mkQ
      (Submodule.mkQ_surjective _) (fun _ _ => rfl)
      (by
        intro v hv c
        exact (Submodule.Quotient.mk_eq_zero _).mp hv c.val)
      ((irreducible_comp_surjective_iff (⊤ : Subgroup d.second).subtype
        Subgroup.topEquiv.surjective σ).mpr hi)
      (hfaith.comp (⊤ : Subgroup d.second).subtype_injective)
    have ht' : IsIrrPlus (ρ.comp d.second.subtype) (d.second.subgroupOf d.second)
        (subspaceCommutator ρ ⊤ d.second) := by
      simpa only [subgroupOf_self,subspaceCommutator_comp_map,← MonoidHom.range_eq_map,Subgroup.range_subtype] using ht
    exact (IsIrrPlus.subgroupOf_iff ρ d.second d.second le_rfl _).mp ht'

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp
private theorem binary_higher_card_ne_60 {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card SL(d,ZMod 2) ≠ 60 := by
  rcases hd with rfl | rfl <;> rw [binary_card] <;> norm_num [Fin.prod_univ_succ]

/-- The full B.5.1 conclusion has only its Irr⁺ branch at component order sixty. -/
theorem ProjectiveLine.QuasisimpleSourceConclusion.card60_moved_irrPlus
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) (hc : Nat.card C = 60) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) := by
  cases c.clause_one with
  | irreducible hi _ _ _ _ => rwa [c.sectionData.space_eq] at hi
  | doubleThree F _ e _ _ =>
    exact (ne_of_gt (linear_three_card_gt_60 F)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne_60 hd ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne_60 hd ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim

/-- B.5.1 and every adequate B.5.6 branch give the literal moved Irr⁺ module
of an ordinary component of order sixty. -/
theorem AdequateAlternative.card60_component_moved [Finite D]
    {ρ : Representation (ZMod 2) D V} (h : AdequateAlternative ρ)
    {C : Subgroup D} (hC : IsComponent D C) (hc : Nat.card C = 60) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) := by
  let := hC.2
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
  let : Nontrivial D := Function.Injective.nontrivial C.subtype_injective
  cases h.of_nontrivial ρ with
  | quasisimple hq ha =>
    have he : generalizedFitting D = C := (hC.eq_of_le
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
      (component_le_generalizedFitting D C hC)).symm
    rw [he] at ha
    exact ha.card60_moved_irrPlus hc
  | symmetricThree d =>
    have hd := card_subgroup_dvd_card C
    rw [hc,Nat.card_congr d.equiv.toEquiv] at hd
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hd
  | twoFactors d => exact d.card60_component_moved hC hc
  | outerSixThree d =>
    let := d.first_normal
    let := d.quotient_first_solvable
    have he : C = d.first := hC.eq_of_le d.first_isComponent
      (le_of_isPerfect_of_solvable_quotient C d.first)
    rw [he,Nat.card_congr d.firstEquiv.toEquiv,nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
  | hyperplane d => exact d.card60_component_moved hC hc

end CFSG.Quasithin.ChapterB.SourceInduction
