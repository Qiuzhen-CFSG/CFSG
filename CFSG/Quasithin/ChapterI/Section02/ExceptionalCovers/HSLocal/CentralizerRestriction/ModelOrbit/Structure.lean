module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelCore
public import Theory.Frattini.BinarySquares

/-!
# Center, squares, commutators and Frattini subgroup of the HS core

The published quaternion and cyclic embeddings cover the actual pair kernel.
Commuting with the four quaternion generators forces the quaternion part of
a central element into the common involution line. Hence the center is exactly
the cyclic factor. Squares are calculated in the individual commuting factors;
commutators and the Frattini subgroup then follow from the binary square
closure theorem and one explicit nontrivial commutator.

The universal square formula includes the center. Its two elements of order
four are explicitly the cyclic generator and its inverse, with common square
the marked involution. No assertion about a noncentral orbit is used here.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423;
16.1.5(10), printed p.1172. All finite checks use the existing ATLAS carrier
and its checked embedded quaternion and cyclic factors.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction

open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
open scoped commutatorElement

private theorem quaternion_square_test : ∀ a : QuaternionGroup 2,
    a ^ 2 = 1 ∨ a ^ 2 = QuaternionGroup.a 2 := by
  decide +kernel

theorem model_commonInvolution_square : commonInvolution ^ 2 = 1 := by
  change (leftI ^ 2) ^ 2 = 1
  rw [← pow_mul]
  exact core_fourth_power leftI

private theorem square_test (a b : QuaternionGroup 2) (c : C4) :
    (leftEmbedding a * rightEmbedding b * cyclicEmbedding c) ^ 2 = 1 ∨
    (leftEmbedding a * rightEmbedding b * cyclicEmbedding c) ^ 2 = commonInvolution := by
  have hl : leftEmbedding a ^ 2 = 1 ∨ leftEmbedding a ^ 2 = commonInvolution := by
    rw [← map_pow]
    rcases quaternion_square_test a with h | h <;> rw [h]
    · exact Or.inl (map_one _)
    · exact Or.inr (by decide +kernel)
  have hr : rightEmbedding b ^ 2 = 1 ∨ rightEmbedding b ^ 2 = commonInvolution := by
    rw [← map_pow]
    rcases quaternion_square_test b with h | h <;> rw [h]
    · exact Or.inl (map_one _)
    · exact Or.inr (by decide +kernel)
  have hc : cyclicEmbedding c ^ 2 = 1 ∨ cyclicEmbedding c ^ 2 = commonInvolution := by
    revert c
    decide +kernel
  have hq : Commute (leftEmbedding a) (rightEmbedding b) :=
    factors_commute _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
  have hp : Commute (leftEmbedding a * rightEmbedding b) (cyclicEmbedding c) :=
    parts_commute _ ((mem_quaternionPart _).mpr ⟨a,b,rfl⟩) _ ⟨c,rfl⟩
  rw [hp.mul_pow, hq.mul_pow]
  rcases hl with hl | hl <;> rcases hr with hr | hr <;> rcases hc with hc | hc <;>
    simp [hl,hr,hc, ← pow_two,model_commonInvolution_square]

@[instance_reducible] private def coreDecidableEq : DecidableEq core := inferInstance
attribute [local instance] coreDecidableEq

set_option maxRecDepth 10000 in
private theorem center_test : ∀ a b : QuaternionGroup 2,
    let x := leftEmbedding a * rightEmbedding b
    leftI * x = x * leftI → leftJ * x = x * leftJ →
    rightI * x = x * rightI → rightJ * x = x * rightJ →
    x = 1 ∨ x = commonInvolution := by
  dsimp only
  decide +kernel

theorem model_core_square (x : core) : x ^ 2 = 1 ∨ x ^ 2 = commonInvolution := by
  obtain ⟨a,b,c,rfl⟩ := model_core_expression x
  exact square_test a b c

private theorem cyclic_le_center : cyclicPart ≤ center core := by
  rintro z ⟨d,rfl⟩
  apply mem_center_iff.mpr
  intro x
  obtain ⟨a,b,c,rfl⟩ := model_core_expression x
  have hq : Commute (leftEmbedding a * rightEmbedding b) (cyclicEmbedding d) :=
    parts_commute _ ((mem_quaternionPart _).mpr ⟨a,b,rfl⟩) _ ⟨d,rfl⟩
  have hc : Commute (cyclicEmbedding c) (cyclicEmbedding d) :=
    (Commute.all c d).map cyclicEmbedding
  exact (hq.mul_left hc).eq

theorem model_core_center : center core = cyclicPart := by
  apply le_antisymm ?_ cyclic_le_center
  intro x hx
  obtain ⟨a,b,c,rfl⟩ := model_core_expression x
  have hq : leftEmbedding a * rightEmbedding b ∈ center core := by
    have := (center core).mul_mem hx
      ((center core).inv_mem (cyclic_le_center (show cyclicEmbedding c ∈ cyclicPart from ⟨c,rfl⟩)))
    simpa only [mul_inv_cancel_right] using this
  have hh := center_test a b (mem_center_iff.mp hq leftI)
    (mem_center_iff.mp hq leftJ) (mem_center_iff.mp hq rightI)
    (mem_center_iff.mp hq rightJ)
  apply cyclicPart.mul_mem ?_ ⟨c,rfl⟩
  rcases hh with hh | hh
  · rw [hh]; exact cyclicPart.one_mem
  · rw [hh]; exact ((parts_intersection_mem _).mpr (Or.inr rfl)).2

theorem model_core_square_mem (x : core) : x ^ 2 ∈ zpowers commonInvolution := by
  rcases model_core_square x with h | h <;> rw [h]
  · exact one_mem _
  · exact mem_zpowers _

theorem model_core_derived : _root_.commutator core = zpowers commonInvolution := by
  apply le_antisymm
  · apply commutator_le_closure_squares.trans
    apply (closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    exact model_core_square_mem x
  · apply zpowers_le.mpr
    have h : ⁅leftI, leftJ⁆ = commonInvolution := by decide +kernel
    rw [← h]
    exact commutator_mem_commutator (mem_top _) (mem_top _)

theorem model_core_frattini : frattini core = zpowers commonInvolution := by
  rw [core_isPGroup.frattini_eq_closure_squares]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    exact model_core_square_mem x
  · apply zpowers_le.mpr
    exact subset_closure ⟨cyclicGenerator, cyclicGenerator_square⟩

theorem model_core_commutator_le_center : _root_.commutator core ≤ center core := by
  rw [model_core_derived, model_core_center]
  exact zpowers_le.mpr (((parts_intersection_mem _).mpr (Or.inr rfl)).2)

theorem model_commonInvolution_ne_one : commonInvolution ≠ 1 := by
  intro h
  apply e0_nontrivial
  rw [← commonInvolution_eq_e0]
  exact congrArg (fun x : core => x.val.val) h

theorem cyclicGenerator_mem_center : cyclicGenerator ∈ center core := by
  rw [model_core_center]
  refine ⟨Multiplicative.ofAdd (1 : ZMod 4), ?_⟩
  change cyclicGenerator ^ 1 = cyclicGenerator
  exact pow_one _

theorem model_core_order_four_iff (x : core) : orderOf x = 4 ↔ x ^ 2 = commonInvolution := by
  constructor
  · intro hx
    rcases model_core_square x with h | h
    · have hd := orderOf_dvd_of_pow_eq_one h
      rw [hx] at hd
      norm_num at hd
    · exact h
  · intro hx
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one, hx] using model_commonInvolution_ne_one
    · exact core_fourth_power x

theorem cyclicGenerator_order_four : orderOf cyclicGenerator = 4 :=
  (model_core_order_four_iff _).mpr cyclicGenerator_square

theorem model_core_central_order_four (x : core) (hx : x ∈ center core) :
    orderOf x = 4 ↔ x = cyclicGenerator ∨ x = cyclicGenerator⁻¹ := by
  rw [model_core_center] at hx
  obtain ⟨c,rfl⟩ := hx
  rw [model_core_order_four_iff]
  have h : ∀ c : C4, cyclicEmbedding c ^ 2 = commonInvolution ↔
      cyclicEmbedding c = cyclicGenerator ∨ cyclicEmbedding c = cyclicGenerator⁻¹ := by
    decide +kernel
  exact h c

theorem model_core_square_carrier (x : core) : x.val.val ^ 2 = 1 ∨ x.val.val ^ 2 = e0 := by
  rcases model_core_square x with h | h
  · exact Or.inl (congrArg (fun y : core => y.val.val) h)
  · exact Or.inr ((congrArg (fun y : core => y.val.val) h).trans commonInvolution_eq_e0)
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
