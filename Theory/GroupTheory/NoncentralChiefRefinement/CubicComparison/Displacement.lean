module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
public import Theory.GroupTheory.Commutator.SimpleImageDisplacement

/-!
# Recovering cubic displacement from the fixed-point budget

For a three-group acting on a two-group, the fixed-point index is an exact
power of four. Equality of cubic lengths on W ≤ Q therefore forces trivial
action on Q/W, and hence [Q,A] ≤ W. An upper budget on a larger two-group,
a lower budget on W and an outer-section contribution force this equality.
A simple image with a two-group kernel extends the
bound from the cubic subgroup to the required two-perfect component.

All normality in the quotient criterion is relative to Q. The original
application is Aschbacher–Smith 13.4.7(4), printed p.903, where the total
budget is three, the omega module uses two and the outer section uses one.
-/

public noncomputable section
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {G : Type*} [Group G] [Finite G]

/-- Equality of cubic fixed lengths detects trivial action on the actual quotient. -/
theorem commutator_le_of_length_eq (A Q W : Subgroup G)
    (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (hWQ : W ≤ Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hAW : A ≤ normalizer (W : Set G)) [(W.subgroupOf Q).Normal]
    (he : conjugationCubicLength A W = conjugationCubicLength A Q) :
    ⁅Q,A⁆ ≤ W := by
  let := quotientConjugationAction A Q W hAQ hAW
  have hz : FixedPoints.cubicLength A (Q ⧸ W.subgroupOf Q) = 0 := by
    rw [← sectionCubicLength_eq_quotient_of_twoGroup A Q W hA hQ hWQ hAQ hAW]
    simp only [sectionCubicLength,he,Nat.sub_self]
  have hi := FixedPoints.index_eq_four_pow_cubicLength hA (hQ.to_quotient (W.subgroupOf Q))
  rw [hz,pow_zero] at hi
  have ht : FixedPoints.subgroup A (Q ⧸ W.subgroupOf Q) = ⊤ := index_eq_one.mp hi
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha q hq
  have hf : (⟨a,ha⟩ : A) • (QuotientGroup.mk' (W.subgroupOf Q) ⟨q,hq⟩) =
      QuotientGroup.mk' (W.subgroupOf Q) ⟨q,hq⟩ :=
    (ht.symm ▸ mem_top _) ⟨a,ha⟩
  have hh := QuotientGroup.eq_iff_div_mem.mp hf
  change a * q * a⁻¹ / q ∈ W at hh
  simpa only [commutatorElement_def,div_eq_mul_inv] using hh

/-- A two-layer budget forces the whole remaining section to be fixed. -/
theorem commutator_le_of_length_budget (A P Q W : Subgroup G)
    (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (hWQ : W ≤ Q) (hQP : Q ≤ P)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hAW : A ≤ normalizer (W : Set G)) [(W.subgroupOf Q).Normal]
    (n k : ℕ) (hP : conjugationCubicLength A P ≤ n + k)
    (hW : n ≤ conjugationCubicLength A W)
    (hsection : k ≤ sectionCubicLength A Q P) : ⁅Q,A⁆ ≤ W := by
  apply commutator_le_of_length_eq A Q W hA hQ hWQ hAQ hAW
  have hm := conjugationCubicLength_mono A hWQ
  have hm' := conjugationCubicLength_mono A hQP
  unfold sectionCubicLength at hsection
  omega

/-- A simple action image extends the budget from one cubic to every two-perfect
subgroup, retaining the full two-group kernel. -/
theorem perfect_commutator_le_of_length_budget
    {F : Type*} [Group F] [IsSimpleGroup F]
    (f : G →* F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (A K P Q W : Subgroup G) [Q.Normal] [W.Normal]
    (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q) (hK : IsPPerfect 2 K)
    (himage : A.map f ≠ ⊥) (hWQ : W ≤ Q) (hQP : Q ≤ P)
    (n k : ℕ) (hP : conjugationCubicLength A P ≤ n + k)
    (hW : n ≤ conjugationCubicLength A W)
    (hsection : k ≤ sectionCubicLength A Q P) : ⁅Q,K⁆ ≤ W := by
  apply commutator_le_of_pPerfect_simple_image f hf hk Q W K A hK himage
  exact commutator_le_of_length_budget A P Q W hA hQ hWQ hQP
    le_normalizer_of_normal le_normalizer_of_normal n k hP hW hsection
end NoncentralChiefRefinement.CubicComparison
