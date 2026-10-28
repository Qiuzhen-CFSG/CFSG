module
public import Theory.GroupTheory.FixedInvertedFactorization
public import Mathlib.GroupTheory.Nilpotent

/-!
# An inverted element centralizing the fixed subgroup

For an involutive automorphism of a finite odd-order `p`-group, a proper
fixed subgroup has a nonidentity centralizing element inverted by the
automorphism. Inverted elements are treated as a set, not as a subgroup.
This is Alperin--Brauer--Gorenstein, Chapter II, Section 8, Lemma 1(ii),
article page 63 / PDF page 64 (`refs/files/alperin-brauer-gorenstein.pdf`).

The source applies the general `P × Q` lemma and then the fixed/inverted
factorization. Here the normalizer condition for finite `p`-groups gives a
direct proof, avoiding any elementary-abelian restriction on the target.
Choose an element of the normalizer of the fixed subgroup outside that
subgroup. The existing odd-order factorization writes it as a fixed factor
times a nonidentity inverted factor, which still normalizes the fixed
subgroup. Applying the automorphism to its conjugates of fixed elements
shows that its square centralizes the fixed subgroup. Uniqueness of square
roots in an odd-order group then shows that the inverted factor itself
centralizes it. No general `P × Q` theorem is assumed.
-/

namespace Theory.GroupAction

/-- ABG II.8 Lemma 1(ii): a proper fixed subgroup in an odd-order finite
`p`-group admits a nonidentity inverted element centralizing it. -/
public theorem exists_ne_one_inverted_centralizing_fixedPoints
    {p : ℕ} [Fact p.Prime] {K : Type*} [Group K] [Finite K]
    (hK : IsPGroup p K) (hodd : Odd (Nat.card K))
    (α : MulAut K) (hα : Function.Involutive α)
    (hproper : α.toMonoidHom.eqLocus (MonoidHom.id K) < ⊤) :
    ∃ element : K, element ≠ 1 ∧ α element = element⁻¹ ∧
      ∀ fixed : K, α fixed = fixed → Commute element fixed := by
  let F := α.toMonoidHom.eqLocus (MonoidHom.id K)
  let N := Subgroup.normalizer (F : Set K)
  let : Group.IsNilpotent K := hK.isNilpotent
  obtain ⟨witness, hwitnessN, hwitnessF⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent F hproper)
  obtain ⟨⟨fixedFactor, element⟩, ⟨hfixedFactor, hinverted, hproduct⟩, _⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd α hα witness
  have hfixedF : fixedFactor ∈ F := hfixedFactor
  have helementN : element ∈ N := by
    have := N.mul_mem (N.inv_mem (Subgroup.le_normalizer hfixedF)) hwitnessN
    simpa [← hproduct] using this
  have hne : element ≠ 1 := by
    intro heq
    apply hwitnessF
    simpa [← hproduct, heq] using hfixedF
  refine ⟨element, hne, hinverted, ?_⟩
  intro fixed hfixed
  have hconj : α (element * fixed * element⁻¹) = element * fixed * element⁻¹ :=
    (Subgroup.mem_normalizer_iff.mp helementN fixed).mp hfixed
  have heq : element⁻¹ * fixed * element = element * fixed * element⁻¹ := by
    simpa [map_mul, map_inv, hinverted, hfixed] using hconj
  have hsquare : (fixed * element * fixed⁻¹) ^ 2 = element ^ 2 := by
    calc
      (fixed * element * fixed⁻¹) ^ 2 =
          element * (element⁻¹ * fixed * element) * element * fixed⁻¹ := by
        simp [pow_two, mul_assoc]
      _ = element * (element * fixed * element⁻¹) * element * fixed⁻¹ := by rw [heq]
      _ = element ^ 2 := by simp [pow_two, mul_assoc]
  have hroot : fixed * element * fixed⁻¹ = element :=
    hodd.coprime_two_right.pow_left_bijective.injective hsquare
  change element * fixed = fixed * element
  calc
    element * fixed = (fixed * element * fixed⁻¹) * fixed := by rw [hroot]
    _ = fixed * element := by simp [mul_assoc]

end Theory.GroupAction
