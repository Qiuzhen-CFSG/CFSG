module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Residual
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# C-components of the adequate FF actor

Every C-component of an actor in the adopted B.5.6 alternatives is
quasisimple. In the product rows, perfectness places it in the product of
the two solvable residuals, and component calculus identifies one of the
quasisimple factors. In the quasisimple generalized-Fitting row,
self-centralization and the component dichotomy force equality with F*.
The outer A₆–C₃ row has solvable quotient by its literal A₆ component;
the trivial and S₃ rows admit no C-component.

This is the extraction used on the actual offender subgroup in the
nonzero-core line argument of original 9.3.1. It requires no generation
of the actor by the selected component and a Sylow subgroup, and keeps
the corrected outer row without a fixed-space splitting assertion.
Source: Aschbacher–Smith, B.5.6, printed p.105, and 9.3.1.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceOldResidual
open ChapterB.SourceInduction ChapterB.QuasisimpleSource

private theorem symmetric_three_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

private theorem residual_of_factor_model {E : Type*} [Group E] [Finite E]
    (hm : Nonempty (E ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 5)) ∨
      (IsSimpleGroup E ∧ Group.IsPerfect E)) :
    solvableResidual E = ⊥ ∨ IsQuasisimple (solvableResidual E) := by
  rcases hm with he | he | ⟨hs,hp⟩
  · obtain ⟨e⟩ := he
    let := symmetric_three_solvable
    let : Group.IsSolvable E := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    exact Or.inl solvableResidual_eq_bot
  · obtain ⟨e⟩ := he
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsQuasisimple (alternatingGroup (Fin 5)) :=
      ⟨((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup⟩
    have hr : solvableResidual (Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) := by
      apply le_antisymm
      · have h := solvableResidual_le_derivedSeries (G := Equiv.Perm (Fin 5)) 1
        rw [derivedSeries_one] at h
        exact h.trans_eq (alternatingGroup.commutator_perm_eq (by simp))
      · exact le_solvableResidual_of_isPerfect _
    let f : solvableResidual E ≃* alternatingGroup (Fin 5) :=
      (e.subgroupMap _).trans (MulEquiv.subgroupCongr
        ((map_solvableResidual_eq _ e.surjective).trans hr))
    exact Or.inr (IsQuasisimple.of_mulEquiv f.symm)
  · let := hs
    let := hp
    have hz : center E = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center E) inferInstance).resolve_right
        (fun he => Group.IsPerfect.not_isMulCommutative E (center_eq_top_iff.mp he))
    let : IsQuasisimple E :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
    let e : solvableResidual E ≃* E :=
      (MulEquiv.subgroupCongr solvableResidual_eq_top).trans topEquiv
    exact Or.inr (IsQuasisimple.of_mulEquiv e.symm)

private theorem cComponent_quasisimple_of_product {D A B : Type*}
    [Group D] [Group A] [Group B] (e : D ≃* A × B)
    (hA : solvableResidual A = ⊥ ∨ IsQuasisimple (solvableResidual A))
    (hB : solvableResidual B = ⊥ ∨ IsQuasisimple (solvableResidual B))
    {C : Subgroup D} (hC : C.IsCComponent) : IsQuasisimple C := by
  have heC := hC.map_equiv e
  rcases cComponent_eq_residual_factor hA hB heC with he | he
  · rcases hA with hb | hq
    · exact (heC.ne_bot (by simpa only [hb,bot_prod_bot] using he)).elim
    · let := hq
      exact IsQuasisimple.of_mulEquiv
        (((e.subgroupMap C).trans (MulEquiv.subgroupCongr he)).trans residualLeftEquiv).symm
  · rcases hB with hb | hq
    · exact (heC.ne_bot (by simpa only [hb,bot_prod_bot] using he)).elim
    · let := hq
      exact IsQuasisimple.of_mulEquiv
        (((e.subgroupMap C).trans (MulEquiv.subgroupCongr he)).trans residualRightEquiv).symm

private theorem linear_two_factor_model (F : BinaryField)
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

private theorem binary_three_factor_model {E : Type*} [Group E]
    (e : E ≃* SL(3,ZMod 2)) :
    Nonempty (E ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 5)) ∨
      (IsSimpleGroup E ∧ Group.IsPerfect E) := by
  let : IsSimpleGroup PSL(3,ZMod 2) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
  exact Or.inr (Or.inr
    ⟨(e.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
      (n := 1) (by simp) (by decide))).isSimpleGroup,
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩)

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

private theorem cComponent_quasisimple_of_twoFactors (c : SourceTwoFactorCase ρ)
    (hC : C.IsCComponent) : IsQuasisimple C :=
  cComponent_quasisimple_of_product c.product.equiv.symm
    (residual_of_factor_model c.firstCase.group_models)
    (residual_of_factor_model c.secondCase.group_models) hC

private theorem cComponent_quasisimple_of_hyperplane (c : HyperplaneCase ρ)
    (hC : C.IsCComponent) : IsQuasisimple C := by
  apply cComponent_quasisimple_of_product c.product.equiv.symm
    (residual_of_factor_model (binary_three_factor_model c.firstEquiv)) _ hC
  cases c.secondCase with
  | linearThree _ _ hn =>
    obtain ⟨e⟩ := hn
    exact residual_of_factor_model (binary_three_factor_model e.groupEquiv)
  | linearTwo F hn =>
    obtain ⟨e⟩ := hn
    exact residual_of_factor_model (linear_two_factor_model F e.groupEquiv)

/-- Every C-component in an actor satisfying the full adopted B.5.6
alternatives is quasisimple. No generation by that component and a Sylow
subgroup is required. -/
theorem cComponent_quasisimple_of_adequate (h : AdequateAlternative ρ)
    (hC : C.IsCComponent) : IsQuasisimple C := by
  rcases h with ht | h
  · let := ht
    exact (hC.ne_bot (Subsingleton.elim _ _)).elim
  cases h with
  | quasisimple hq _ =>
    have hF : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
    have he : C = generalizedFitting D := by
      rcases hF.subnormal_dichotomy C hC.subnormal with hle | hc
      · exact (hF.isCComponent.eq_of_le hC hle).symm
      · apply hC.eq_of_le hF.isCComponent
        exact (commutator_eq_bot_iff_le_centralizer.mp
          ((commutator_comm (generalizedFitting D) C).symm.trans hc)).trans
            (centralizer_generalizedFitting_le D)
    exact he.symm ▸ hq
  | symmetricThree c =>
    let := symmetric_three_solvable
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    exact (hC.not_isSolvable inferInstance).elim
  | twoFactors c => exact cComponent_quasisimple_of_twoFactors c hC
  | outerSixThree c =>
    let := hC.perfect
    let := c.first_normal
    let := c.quotient_first_solvable
    have he : C = c.first := hC.eq_of_le c.first_isComponent.isCComponent
      (le_of_isPerfect_of_solvable_quotient C c.first)
    exact he.symm ▸ c.first_isComponent.2
  | hyperplane c => exact cComponent_quasisimple_of_hyperplane c hC

end CFSG.Quasithin.Chapter10.SourceOldResidual
