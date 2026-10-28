module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.Fusion
/-!
# The eight quaternion pairs over a crossing core intersection

Interchanging the middle coordinates puts the two block decompositions in
transverse position. The four off-block entries vanish precisely when both
quaternion blocks are diagonal; equality of the two diagonal products is the
remaining projective condition. Exactly eight pairs satisfy these equations.
Small kernel-checked calculations on Q₈ × Q₈ supply this coordinate fact,
retaining every nonzero scalar of the concrete field of nine elements.

Source: Aschbacher, *Sporadic Groups* (1994), type U₄(3), printed p.244.
-/

@[expose] public section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
open RepresentativeCore
open RepresentativeCore.QuotientCore.Blocks

def crossedQuaternion (q : QuaternionGroup 2 × QuaternionGroup 2) : Mat₄ :=
  fusionMatrix * RepresentativeCore.block (quaternionMatrix q.1) (quaternionMatrix q.2) * fusionMatrix

def crossedCondition (q : QuaternionGroup 2 × QuaternionGroup 2) : Prop :=
  crossedQuaternion q 0 2 = 0 ∧ crossedQuaternion q 2 0 = 0 ∧
  crossedQuaternion q 1 3 = 0 ∧ crossedQuaternion q 3 1 = 0 ∧
  crossedQuaternion q 0 0 * crossedQuaternion q 1 1 = crossedQuaternion q 2 2 * crossedQuaternion q 3 3

instance (q : QuaternionGroup 2 × QuaternionGroup 2) : Decidable (crossedCondition q) := by unfold crossedCondition; infer_instance

theorem crossedCondition_of_scalar (q r : QuaternionGroup 2 × QuaternionGroup 2) (u : FiniteField.Nine) (hu : u ≠ 0)
    (h : crossedQuaternion q=u • RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) :
    crossedCondition q := by
  have off : ∀r : QuaternionGroup 2 × QuaternionGroup 2,
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 0 2=0 ∧
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 2 0=0 ∧
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 1 3=0 ∧
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 3 1=0 := by decide +kernel
  have cross_off : ∀ q : QuaternionGroup 2 × QuaternionGroup 2,
      crossedQuaternion q 0 1 = 0 ∧ crossedQuaternion q 2 3 = 0 := by decide +kernel
  have hr01 : RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2) 0 1=0 := by
    have hh := congrArg (fun A : Mat₄ => A 0 1) h
    rw [(cross_off q).1] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hu
  have hr23 : RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2) 2 3=0 := by
    have hh := congrArg (fun A : Mat₄ => A 2 3) h
    rw [(cross_off q).2] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hu
  have diag : ∀r : QuaternionGroup 2 × QuaternionGroup 2,
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 0 1=0 →
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 2 3=0 →
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 0 0 *
        (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 1 1 =
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 2 2 *
        (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 3 3 := by decide +kernel
  unfold crossedCondition
  rw [h]
  simp only [Matrix.smul_apply,smul_eq_mul]
  obtain ⟨h1,h2,h3,h4⟩ := off r
  refine ⟨by rw [h1,mul_zero],by rw [h2,mul_zero],by rw [h3,mul_zero],by rw [h4,mul_zero],?_⟩
  calc
    _ = u^2 * ((RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 0 0 *
      (RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2)) 1 1) := by ring
    _ = _ := by rw [diag r hr01 hr23]; ring

theorem crossedCondition_card : Fintype.card {q : QuaternionGroup 2 × QuaternionGroup 2 // crossedCondition q}=8 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem crossedCondition_suffices : ∀q : QuaternionGroup 2 × QuaternionGroup 2,
    crossedCondition q → ∃(r : QuaternionGroup 2 × QuaternionGroup 2) (u : FiniteField.Nine),
      u ≠ 0 ∧ crossedQuaternion q=u • RepresentativeCore.block (quaternionMatrix r.1) (quaternionMatrix r.2) := by
  decide +kernel
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
