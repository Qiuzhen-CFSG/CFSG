module
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.Covering
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# The small odd-prime rows of the replacement model calculation

The actual field-five equivalence gives the binary field-four model. Field
three is excluded by perfection of the literal component two-core quotient.
Thus every remaining odd-prime model has parameter at least seven.

Source: Aschbacher--Smith 10.3.3 and its final reuse, pp.756--757; E.1.14(6),
p.214. The imported exceptional equivalence retains its ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
variable {H : Type*} [Group H]

theorem binary_model_of_prime_five (hm : ClassicalGroup.IsPSL H 2 5) :
    ClassicalGroup.IsPSL H 2 (2 ^ 2) := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  exact ⟨GaloisField 2 2, inferInstance, inferInstance,
    GaloisField.card 2 2 (by decide),
    ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hc)⟩⟩

theorem prime_model_binary_or_ge_seven [IsQuasisimple H]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL H 2 p) :
    ClassicalGroup.IsPSL H 2 (2 ^ 2) ∨ 7 ≤ p := by
  by_cases h5 : p = 5
  · exact Or.inl (binary_model_of_prime_five (h5 ▸ hm))
  right
  by_contra hn
  have h3 : p = 3 := by
    have hp2 := hp.two_le
    have hp4 : p ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hp)
    have hp6 : p ≠ 6 := fun h => (by decide : ¬ Nat.Prime 6) (h ▸ hp)
    have ho2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ ho)
    omega
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  apply Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (hc.trans h3)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
