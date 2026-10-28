module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Basic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Residuals of the actual B.5.6 product factors

SL₂ over a binary field of degree at least two is quasisimple, and its
center is trivial. The degree-one case is identified with the actual S₃
permutation group. SL₃ is quasisimple; odd field degree makes its scalar
center trivial and identifies it with the projective model required by
`PerfectFactorModel`. The residual of S₅ is its actual alternating subgroup.
Thus every listed factor has either trivial residual and an S₃ equivalence,
or a quasisimple residual with an actual perfect-factor or A₅ equivalence.
The explicit three-cycle in A₅ supplies the S₅ branch's cubic witness.

Source: Aschbacher–Smith B.5.6(3),(5), printed p.105, as used in
15.3.49(i), printed pp.1143–1144. Linear simplicity and field transport
reuse the attributed ATLAS ports in the imported Theory modules.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases

variable {D E : Type*} [Group D] [Group E]

def ComponentModel (D : Type*) [Group D] : Prop :=
  PerfectLifting.PerfectFactorModel D ∨ Nonempty (D ≃* alternatingGroup (Fin 5))

theorem ComponentModel.of_equiv (e : D ≃* E) (h : ComponentModel E) : ComponentModel D := by
  rcases h with h | h
  · left
    cases h with
    | linear_two F n hn hc f => exact .linear_two F n hn hc ⟨e.trans f.some⟩
    | linear_three F n hn ho hc f => exact .linear_three F n hn ho hc ⟨e.trans f.some⟩
  · obtain ⟨f⟩ := h
    exact Or.inr ⟨e.trans f⟩

noncomputable def sl2Projective (F : FFAlternatives.BinaryField) :
    SL(2, F.Carrier) ≃* PSL(2, F.Carrier) :=
  (QuotientGroup.quotientMulEquivOfEq
    (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F.Carrier))).trans
    QuotientGroup.quotientBot |>.symm

private theorem sl2_quasisimple (F : FFAlternatives.BinaryField) (hn : 2 ≤ F.degree) :
    IsQuasisimple SL(2, F.Carrier) := by
  have hcard : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    change 2 ^ 2 ≤ 2 ^ F.degree
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hfield : ∃ a : F.Carrier, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ : IsCyclic F.Carrierˣ := inferInstance
    refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
    grw [Nat.card_eq_card_units_add_one F.Carrier,
      ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hcard
    omega
  exact { toIsPerfect := ⟨Matrix.SL2.commutator_eq_top hfield.choose_spec.1 hfield.choose_spec.2⟩
          simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard }

private theorem odd_power_two_mod_three (n : ℕ) (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add, pow_mul]
  simp [Nat.mul_mod, Nat.pow_mod]

noncomputable def sl3Projective (F : FFAlternatives.BinaryField) (hn : Odd F.degree) :
    SL(3, F.Carrier) ≃* PSL(3, F.Carrier) :=
  Matrix.SL3.equivProjectiveOfCenterEqBot F.Carrier
    ((Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mpr (by
      rw [F.card_eq, odd_power_two_mod_three _ hn]
      decide))

private theorem sl3_quasisimple (F : FFAlternatives.BinaryField) : IsQuasisimple SL(3, F.Carrier) :=
  { toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }

private theorem a5_quasisimple : IsQuasisimple (alternatingGroup (Fin 5)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
          simple := ((QuotientGroup.quotientMulEquivOfEq
            (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }

private theorem s5_residual : solvableResidual (Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) := by
  let := a5_quasisimple
  exact le_antisymm (le_of_isPerfect_of_index_eq_two _ _ alternatingGroup.index_eq_two)
    (le_solvableResidual_of_isPerfect _)

private noncomputable def residualEquiv [Finite D] (e : D ≃* E) :
    solvableResidual D ≃* solvableResidual E :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_solvableResidual_eq _ e.surjective))

private theorem residual_model_of_quasisimple [Finite D] [IsQuasisimple D]
    (h : ComponentModel D) :
    IsQuasisimple (solvableResidual D) ∧ ComponentModel (solvableResidual D) := by
  let e : solvableResidual D ≃* D :=
    (MulEquiv.subgroupCongr solvableResidual_eq_top).trans topEquiv
  exact ⟨IsQuasisimple.of_mulEquiv e.symm, h.of_equiv e⟩

theorem factor_residual [Finite D] (h : FFAlternatives.FactorModel D) :
    (Nonempty (D ≃* Equiv.Perm (Fin 3)) ∧ solvableResidual D = ⊥) ∨
    (IsQuasisimple (solvableResidual D) ∧ ComponentModel (solvableResidual D)) := by
  cases h with
  | linearTwo F e =>
    by_cases hn : F.degree = 1
    · left
      have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq, hn]; rfl
      let := Fintype.ofFinite F.Carrier
      let f : F.Carrier ≃+* ZMod 2 :=
        (ZMod.ringEquivOfPrime F.Carrier (by decide)
          (by simpa only [← Nat.card_eq_fintype_card] using hc)).symm
      obtain ⟨g⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
      let ee : D ≃* Equiv.Perm (Fin 3) := e.trans ((Atlas.fieldEquivSL 2 f).trans g)
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
        apply Group.isSolvable_of_ker_le_range
          (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
        rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
      let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective (f := ee.toMonoidHom) ee.injective
      exact ⟨⟨ee⟩, solvableResidual_eq_bot⟩
    · have hn : 2 ≤ F.degree := by have := F.degree_pos; omega
      let := sl2_quasisimple F hn
      let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
      exact Or.inr (residual_model_of_quasisimple
        (Or.inl (.linear_two F.Carrier F.degree hn F.card_eq ⟨e.trans (sl2Projective F)⟩)))
  | symmetricFive e =>
    right
    let f : solvableResidual D ≃* alternatingGroup (Fin 5) :=
      (residualEquiv e).trans (MulEquiv.subgroupCongr s5_residual)
    let := a5_quasisimple
    exact ⟨IsQuasisimple.of_mulEquiv f.symm, Or.inr ⟨f⟩⟩
  | linearThree F hn e =>
    let := sl3_quasisimple F
    let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
    exact Or.inr (residual_model_of_quasisimple
      (Or.inl (.linear_three F.Carrier F.degree F.degree_pos hn F.card_eq
        ⟨e.trans (sl3Projective F hn)⟩)))

/-- The explicit three-cycle (0 1)(1 2) in the actual A₅ component of S₅. -/
def a5ThreeCycle : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

theorem a5ThreeCycle_order : orderOf a5ThreeCycle = 3 :=
  orderOf_eq_prime (by decide) (by decide)

theorem a5ThreeCycle_noncentral : a5ThreeCycle ∉ center (alternatingGroup (Fin 5)) := by
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot]
  decide

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents
