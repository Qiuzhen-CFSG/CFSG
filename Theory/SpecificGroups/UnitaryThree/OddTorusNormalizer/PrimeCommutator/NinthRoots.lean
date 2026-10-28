module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.PrimeCommutator.CubicMonomial
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer
public import Theory.GroupTheory.CyclicInversionObstruction

/-!
# Opposite order-nine torus witnesses in unitary groups

The frame theorem places an odd subgroup normalized by an involution in
an actual torus normalizer. The monomial cubic calculation places each
order-nine witness in its diagonal torus. If both witnesses are inverted
by the involution, they belong to the cyclic torus commutator. An operator
fixing one and inverting the other then contradicts their common order.

These special and projective carrier statements retain only the genuine
odd-subgroup geometry and the two marked witnesses. No invariant-frame
assumption on their additional operator is required.

Source application: GLS IV, Chapter 2, Proposition 16.5, the paired
square-field tori when their three-parts contain elements of order nine.
-/

noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E] [Finite E]

/-- Two oppositely acted-on order-nine witnesses are impossible in the
actual special-unitary odd subgroup from the frame theorem. -/
public theorem special_false_of_opposite_order_nine
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x=x} = 2^n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (t : J.specialSubgroup) (ht : orderOf t=2)
    (htH : t ∈ normalizer H) (hB : SpecialNoBorel J H)
    (x y : J.specialSubgroup) (hxH : x∈H) (hyH : y∈H)
    (hx : orderOf x=9) (hy : orderOf y=9)
    (htx : t*x*t⁻¹=x⁻¹) (hty : t*y*t⁻¹=y⁻¹)
    (a : J.specialSubgroup →* J.specialSubgroup)
    (hax : a x=x) (hay : a y=y⁻¹) : False := by
  obtain ⟨P,hN,_,_,_,⟨eC⟩⟩ :=
    special_odd_subgroup_torus J hn hcard hfixed H hodd t ht htH hB
  have hq : 2 ≤ 2^n := Nat.le_self_pow (by omega : n≠0) 2
  have hxA := specialFrameNormalizer_mem_of_order_nine J P (2^n) hq hcard hfixed
    x (hN (mem_sup_left hxH)) hx
  have hyA := specialFrameNormalizer_mem_of_order_nine J P (2^n) hq hcard hfixed
    y (hN (mem_sup_left hyH)) hy
  exact false_of_order_nine_opposite_actions (specialFrameTorus J P)
    (eC.isCyclic.mpr inferInstance) hx hy hxA hyA htx hty a hax hay

/-- The same literal order-nine obstruction after the scalar quotient. -/
public theorem projective_false_of_opposite_order_nine
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x=x} = 2^n)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t=2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H)
    (x y : ProjectiveSpecialUnitaryMatrixGroup J) (hxH : x∈H) (hyH : y∈H)
    (hx : orderOf x=9) (hy : orderOf y=9)
    (htx : t*x*t⁻¹=x⁻¹) (hty : t*y*t⁻¹=y⁻¹)
    (a : ProjectiveSpecialUnitaryMatrixGroup J →* ProjectiveSpecialUnitaryMatrixGroup J)
    (hax : a x=x) (hay : a y=y⁻¹) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨P,hN,_,_,_,⟨eC⟩⟩ :=
    projective_odd_subgroup_torus J hn hcard hfixed H hodd t ht htH hB
  have hq : 2 ≤ 2^n := Nat.le_self_pow (by omega : n≠0) 2
  have hxA := projectiveFrameNormalizer_mem_of_order_nine J P (2^n) hq hcard hfixed
    x (hN (mem_sup_left hxH)) hx
  have hyA := projectiveFrameNormalizer_mem_of_order_nine J P (2^n) hq hcard hfixed
    y (hN (mem_sup_left hyH)) hy
  exact false_of_order_nine_opposite_actions (projectiveFrameTorus J P)
    (eC.isCyclic.mpr inferInstance) hx hy hxA hyA htx hty a hax hay

end UnitaryThree.OddTorusNormalizer
