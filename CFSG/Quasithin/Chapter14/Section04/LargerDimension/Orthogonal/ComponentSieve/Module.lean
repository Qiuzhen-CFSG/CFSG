module

public import Theory.Representation.BinaryPermutation.FiveConjugation
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The natural-block obstruction in the orthogonal sieve

A genuine binary A₅ action on the intrinsic two-core cannot satisfy the
natural SL₂(4) conjugation identity. Both identifications use the same
normal subgroup and the literal quotient by it, allowing the action
comparison to exclude the L₂(4)-block cases of A.3.14 once their local
subgroup and block data have been constructed.

Source: Aschbacher–Smith, A.3.14(6)–(7), p.49, and Lemma 14.4.9, p.1010.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
variable {X : Type*} [Group X]

/-- The source's natural block is distinguished by its conjugation action,
not merely by its abstract group quotient or module cardinality. -/
theorem binaryFive_not_naturalSL2 {V : Subgroup X} [V.Normal]
    (h : BinaryPermutation.FiveConjugation X V) :
    ¬ Chapter1.Section02.LocalModels.NaturalSL2Action X V 4 := by
  rintro ⟨F, hF, hfin, hc, e, ρ, hρ⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hc)
  exact h.no_natural_plane e ρ hρ

/-- Specialization to the intrinsic two-core of the smaller subgroup in
A.3.14. Identifying that core with UD/D remains a source obligation. -/
theorem binary_core_not_natural_block
    (h : BinaryPermutation.FiveConjugation X (pCore 2 X)) :
    ¬ Chapter1.Section02.LocalModels.NaturalSL2Action X (pCore 2 X) 4 :=
  binaryFive_not_naturalSL2 h

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
