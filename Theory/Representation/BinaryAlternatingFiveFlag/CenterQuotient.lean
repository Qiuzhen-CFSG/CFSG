module
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel
/-!
# Center detection modulo the binary five-point fixed line

A permutation of five letters whose differences on the even-weight module
all lie in the point-stabilizer fixed line is the identity. For the regular
four-group's exchange, a vector has difference in that line precisely when
its fifth coordinate vanishes. These finite calculations supply the center
bound in Aschbacher--Smith 14.6.9(k), printed p.1027.
-/

public section
namespace BinaryPermutation.AlternatingFiveFlag
open Subgroup
theorem permutation_eq_one_of_line_displacements (g : Perm)
    (h : ∀ v : Multiplicative FiveCentralizerGeometry.Space,
      Multiplicative.ofAdd (rho g v.toAdd - v.toAdd) ∈ line) : g = 1 := by
  have hf : ∀ g : Perm, (∀ v : Multiplicative FiveCentralizerGeometry.Space,
      Multiplicative.ofAdd (rho g v.toAdd - v.toAdd) ∈ line) → g = 1 := by
    decide +kernel
  exact hf g h

theorem mem_three_of_exchange_difference (v : Multiplicative FiveCentralizerGeometry.Space)
    (h : Multiplicative.ofAdd (rho k₁ v.toAdd - v.toAdd) ∈ line) : v ∈ three := by
  have hf : ∀ v : Multiplicative FiveCentralizerGeometry.Space,
      Multiplicative.ofAdd (rho k₁ v.toAdd - v.toAdd) ∈ line → v ∈ three := by
    decide +kernel
  exact hf v h
end BinaryPermutation.AlternatingFiveFlag
