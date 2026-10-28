module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.SpecificGroups.PSL3.FullParabolicProperness
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.LocalGeneration
public import Theory.GroupTheory.CComponent.SolvableSupplement

/-!
# Both PSL₃(4) residuals over the same Sylow subgroup

The point and line parabolic residuals are distinct, proper and generate
PSL₃(4). Every proper local C-component over the standard unipotent Sylow
is one of these two literal subgroups. The proof uses full-Sylow parabolic
placement, then perfectness and rank-one core-cover rigidity. No separate
conjugation is chosen for the two residuals.

This is the model input to the construction of K₀ in 11.1.2. The next
module lifts both residuals through the original two-core map, and
OtherResidual applies the result to the first chosen-flag normalizer.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed p.762, using A.3.12--14, pp.47--50.
-/


open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
open CFSG.Quasithin.Chapter1.Section02
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

def rootLocal (b : Bool) : Subgroup PSL(3,F) := if b then pointLocal F else lineLocal F

omit [Finite F] [CharP F 2] in
theorem rootLocal_false : rootLocal F false = lineLocal F := by rfl

omit [Finite F] [CharP F 2] in
theorem rootLocal_true : rootLocal F true = pointLocal F := by rfl

omit [CharP F 2] in
theorem rootLocal_perfect (hF : Nat.card F = 4) (b : Bool) :
    Group.IsPerfect (rootLocal F b) := by
  cases b
  · exact lineLocal_isPerfect F (by omega)
  · exact pointLocal_isPerfect F (by omega)

def rootLocalQuotient (b : Bool) :
    (rootLocal F b ⧸ pCore 2 (rootLocal F b)) ≃* SL(2,F) := by
  cases b
  · exact lineLocalCoreQuotientEquiv F
  · exact pointLocalCoreQuotientEquiv F

omit [CharP F 2] in
theorem rootLocal_ne_top (b : Bool) : rootLocal F b ≠ ⊤ := by
  cases b
  · intro he
    exact (Matrix.PSL3.RootPlaneGeometry.parabolic_lt_top F false).ne
      (top_le_iff.mp (he ▸ map_mono (lineLocalSL_le F)))
  · intro he
    exact (Matrix.PSL3.RootPlaneGeometry.parabolic_lt_top F true).ne
      (top_le_iff.mp (he ▸ map_mono (pointLocalSL_le F)))

omit [CharP F 2] in
theorem rootLocal_sup (b : Bool) : rootLocal F b ⊔ rootLocal F (!b) = ⊤ := by
  cases b
  · exact (sup_comm _ _).trans (locals_sup_eq_top F)
  · exact locals_sup_eq_top F

omit [CharP F 2] in
theorem rootLocal_injective : Function.Injective (rootLocal F) := by
  intro b d he
  cases b <;> cases d
  · rfl
  · have h := rootLocal_sup F false
    simp only [Bool.not_false, he, sup_idem] at h
    exact (rootLocal_ne_top F true h).elim
  · have h := rootLocal_sup F true
    simp only [Bool.not_true, he, sup_idem] at h
    exact (rootLocal_ne_top F false h).elim
  · rfl

omit [Finite F] [CharP F 2] in
theorem unipotent_le_rootLocal (b : Bool) : unipotent F ≤ rootLocal F b := by
  cases b
  · exact unipotent_le_lineLocal F
  · exact unipotent_le_pointLocal F

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A] [Group.IsPerfect A] :
    IsPPerfect 2 A := by
  intro N hN hq
  let := hN
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)

theorem rootLocal_top_component (hF : Nat.card F = 4) (b : Bool) :
    (⊤ : Subgroup (rootLocal F b)).IsCComponent := by
  let := rootLocal_perfect F hF b
  let : IsSimpleGroup SL(2,F) :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple (by omega)
  let : Group.IsPerfect SL(2,F) :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect (by omega)
  have hz : center SL(2,F) = ⊥ := by
    rcases (inferInstance : (center SL(2,F)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative SL(2,F) (center_eq_top_iff.mp ht)).elim
  let : IsQuasisimple SL(2,F) :=
    { toIsPerfect := inferInstance
      simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (rootLocal F b ⧸ pCore 2 (rootLocal F b)) :=
    IsQuasisimple.of_mulEquiv (rootLocalQuotient F b).symm
  exact isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (rootLocal F b)) pCore_isPGroup perfect_twoPerfect

/-- Fixed-Sylow placement, with the same two literal residuals for every input. -/
theorem standard_local_cases (hF : Nat.card F = 4) {B : Subgroup PSL(3,F)}
    (hB : B ∈ localCComponents (unipotent F)) (hproper : B ≠ ⊤) :
    ∃ b : Bool, B = rootLocal F b := by
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  have hjoin : B ⊔ unipotent F ≠ ⊤ := by
    intro ht
    have hc : B.IsCComponent := by
      change (B.subgroupOf (B ⊔ unipotent F)).IsCComponent at hB
      rw [ht] at hB
      simpa only [map_subgroupOf_eq_of_le le_top] using hB.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hproper
  let := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ unipotent F from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  obtain hp | hp := UnipotentOvergroups.overgroup_unipotent F (B ⊔ unipotent F)
    le_sup_right hjoin
  · refine ⟨true,?_⟩
    let := pointLocal_isPerfect F (by omega)
    apply local_eq_of_sl2_core_quotient (pointLocal F) (by omega)
      (pointLocalCoreQuotientEquiv F) (unipotentSylow F (by decide : 0 < 2) (by simpa using hF)) B hB
    · rw [←ParabolicResiduals.pointParabolic_residual F (by omega)]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    · exact unipotent_le_pointLocal F
  · refine ⟨false,?_⟩
    let := lineLocal_isPerfect F (by omega)
    apply local_eq_of_sl2_core_quotient (lineLocal F) (by omega)
      (lineLocalCoreQuotientEquiv F) (unipotentSylow F (by decide : 0 < 2) (by simpa using hF)) B hB
    · rw [←ParabolicResiduals.lineParabolic_residual F (by omega)]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    · exact unipotent_le_lineLocal F


end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
