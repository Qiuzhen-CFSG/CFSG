module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Residual
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# A component with cubic center selects the quasisimple source row

All actual components in the nonquasisimple adequate B.5.6 rows are centerless.
For an internal product a component lies in one factor; the factor models are
solvable S₃, S₅ with unique component A₅, or simple perfect binary linear groups.
In the outer A₆–C₃ configuration the quotient by the literal A₆ factor is
solvable, so every perfect component lies in that factor. Thus an actual
component with center of order three selects the quasisimple row, retaining
its complete source action conclusion.

Source: Aschbacher–Smith, B.5.6, printed p.105, with ordinary component calculus.
This is the center comparison used by the contained-component argument in
Chapter 15; no whole-space splitting is inferred in the outer source row.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource

private theorem center_eq_bot_of_equiv {E F : Type*} [Group E] [Group F]
    (e : E ≃* F) (hF : center F = ⊥) : center E = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have he : e x = 1 := hF.le ((centerCongr e) ⟨x,hx⟩).property
  exact e.injective (he.trans e.map_one.symm)

private theorem component_center_eq_bot_of_model {E : Type*} [Group E]
    (hm : Nonempty (E ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 5)) ∨
      (IsSimpleGroup E ∧ Group.IsPerfect E))
    {C : Subgroup E} (hC : IsComponent E C) : center C = ⊥ := by
  rcases hm with he | he | ⟨hs,hp⟩
  · obtain ⟨e⟩ := he
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable E := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    let := hC.2
    let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  · obtain ⟨e⟩ := he
    let N := alternatingGroup (Fin 5)
    let : IsSimpleGroup N := alternatingGroup.isSimpleGroup (by simp)
    let : IsQuasisimple N :=
      { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
        simple := ((QuotientGroup.quotientMulEquivOfEq
          (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hN : IsComponent (Equiv.Perm (Fin 5)) N :=
      ⟨(inferInstance : N.Normal).isSubnormal,inferInstance⟩
    have hc := hC.map_equiv e
    let := hc.2
    have heq : C.map e.toMonoidHom = N := by
      apply hc.eq_of_le hN
      rw [← commutator_eq_self (H := C.map e.toMonoidHom)]
      exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
    exact center_eq_bot_of_equiv
      ((C.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr heq))
      (alternatingGroup.center_eq_bot (by simp))
  · let := hs
    let := hp
    have he : C = ⊤ := (hC.1.eq_bot_or_top_of_isSimpleGroup hs).resolve_left
      hC.isCComponent.ne_bot
    have hz : center E = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center E) inferInstance).resolve_right
        (fun he => Group.IsPerfect.not_isMulCommutative E (center_eq_top_iff.mp he))
    exact center_eq_bot_of_equiv ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv) hz

private theorem component_le_factor {D : Type*} [Group D] {A B C : Subgroup D}
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

private theorem binary_linear_two_models (F : BinaryField)
    {E : Type*} [Group E] (e : E ≃* SL(2,F.Carrier)) :
    Nonempty (E ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 5)) ∨
      (IsSimpleGroup E ∧ Group.IsPerfect E) := by
  by_cases hd : F.degree = 1
  · exact Or.inl ⟨e.trans
      ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))⟩
  · have hl : 3 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have hd' : 2 ≤ F.degree := by have := F.degree_pos; omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
      norm_num at hp
      omega
    let : IsSimpleGroup PSL(2,F.Carrier) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : Group.IsPerfect SL(2,F.Carrier) :=
      GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hl
    exact Or.inr (Or.inr
      ⟨(e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup,
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩)

private theorem binary_three_models {E : Type*} [Group E]
    (e : E ≃* SL(3,ZMod 2)) :
    Nonempty (E ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 5)) ∨
      (IsSimpleGroup E ∧ Group.IsPerfect E) := by
  let : IsSimpleGroup PSL(3,ZMod 2) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
  exact Or.inr (Or.inr
    ⟨(e.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
      (n := 1) (by simp) (by decide))).isSimpleGroup,
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩)

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- Every actual component in the two-factor row has trivial center. -/
theorem SourceTwoFactorCase.component_center_eq_bot (d : SourceTwoFactorCase ρ)
    {C : Subgroup D} (hC : IsComponent D C) : center C = ⊥ := by
  rcases component_le_factor d.product hC with ha | hb
  · exact center_eq_bot_of_equiv (subgroupOfEquivOfLe ha).symm
      (component_center_eq_bot_of_model d.firstCase.group_models (hC.subgroupOf ha))
  · exact center_eq_bot_of_equiv (subgroupOfEquivOfLe hb).symm
      (component_center_eq_bot_of_model d.secondCase.group_models (hC.subgroupOf hb))

/-- Every actual component in the hyperplane row has trivial center. -/
theorem HyperplaneCase.component_center_eq_bot (d : HyperplaneCase ρ)
    {C : Subgroup D} (hC : IsComponent D C) : center C = ⊥ := by
  rcases component_le_factor d.product hC with ha | hb
  · exact center_eq_bot_of_equiv (subgroupOfEquivOfLe ha).symm
      (component_center_eq_bot_of_model (binary_three_models d.firstEquiv) (hC.subgroupOf ha))
  · apply center_eq_bot_of_equiv (subgroupOfEquivOfLe hb).symm
    apply component_center_eq_bot_of_model (hC := hC.subgroupOf hb)
    cases d.secondCase with
    | linearThree _ _ hn =>
      obtain ⟨e⟩ := hn
      exact binary_three_models e.groupEquiv
    | linearTwo F hn =>
      obtain ⟨e⟩ := hn
      exact binary_linear_two_models F e.groupEquiv

/-- The literal A₆ factor is the sole component in the adopted outer row. -/
theorem outerSixThree_component_center_eq_bot (d : OuterSixThreeShape D)
    {C : Subgroup D} (hC : IsComponent D C) : center C = ⊥ := by
  let := hC.2
  let := d.first_normal
  let := d.quotient_first_solvable
  have hle : C ≤ d.first := le_of_isPerfect_of_solvable_quotient C d.first
  have he : C = d.first := hC.eq_of_le d.first_isComponent hle
  exact center_eq_bot_of_equiv ((MulEquiv.subgroupCongr he).trans d.firstEquiv)
    (alternatingGroup.center_eq_bot (by simp))

/-- A component with cubic center selects the full quasisimple source conclusion.
The component is the original subgroup of the actor, not a replacement model. -/
theorem NontrivialAdequateAlternative.quasisimple_of_component_center_card_three
    (h : NontrivialAdequateAlternative ρ) {C : Subgroup D}
    (hC : IsComponent D C) (hc : Nat.card (center C) = 3) :
    IsQuasisimple (generalizedFitting D) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D)) := by
  have hn : center C ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  cases h with
  | quasisimple hq ha => exact ⟨hq,⟨ha⟩⟩
  | symmetricThree d =>
    exact (hn (component_center_eq_bot_of_model (Or.inl ⟨d.equiv⟩) hC)).elim
  | twoFactors d => exact (hn (d.component_center_eq_bot hC)).elim
  | outerSixThree d => exact (hn (outerSixThree_component_center_eq_bot d hC)).elim
  | hyperplane d => exact (hn (d.component_center_eq_bot hC)).elim

end CFSG.Quasithin.ChapterB.SourceInduction
