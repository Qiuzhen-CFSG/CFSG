module

public import Theory.Representation.PSL3Two.SingerRestriction.Orbits
public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace

/-!
# Complete Singer restriction for the natural and Steinberg modules

This boundary assembles the natural orbit, the Steinberg fixed plane and its
exact stabilizers, and the decomposition of every invariant five-space
containing that plane. The moving factor is the literal displacement span.
The only group hypotheses are the two subgroup orders and normalization;
no orbit, stabilizer, decomposition or cubic-invariance premise is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

public section

open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
namespace BinaryLinearThree.SingerRestriction

/-- All concrete module restrictions used in the Singer centralizer argument.
The five-space conclusion is uniform over every actual invariant subspace
of dimension five containing the fixed plane. -/
theorem restriction (H D : Subgroup Group) (hH : Nat.card H = 7)
    (hD : Nat.card D = 3) (hDH : D ≤ Subgroup.normalizer H) :
    fixedSpace W H = ⊥ ∧
    (∀ u v : Vector, u ≠ 0 → v ≠ 0 → ∃ h ∈ H, W h u = v) ∧
    Module.finrank (ZMod 2) (fixedSpace S H) = 2 ∧
    (∀ u v : Steinberg, u ∈ fixedSpace S H → v ∈ fixedSpace S H →
      u ≠ 0 → v ≠ 0 → ∃ g ∈ D, S g u = v) ∧
    (∀ v : Steinberg, v ∈ fixedSpace S H → v ≠ 0 →
      ∀ g : Group, S g v = v ↔ g ∈ H) ∧
    (∀ A : Submodule (ZMod 2) Steinberg, Module.finrank (ZMod 2) A = 5 →
      fixedSpace S H ≤ A → (∀ h ∈ H, ∀ a ∈ A, S h a ∈ A) →
      let M := displacementSpan S H A
      Module.finrank (ZMod 2) M = 3 ∧
      A = fixedSpace S H ⊔ M ∧ fixedSpace S H ⊓ M = ⊥ ∧
      (∀ g ∈ D, A.map (S g) = A ∧ M.map (S g) = M) ∧
      (∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ H, S h v = w)) := by
  exact ⟨natural_fixedSpace_order_seven H hH,
    natural_transitive_order_seven H hH,
    finrank_fixedSpace_order_seven H hH,
    transitive_order_three H D hH hD hDH,
    stabilizer_order_seven H hH,
    FiveSpace.restriction H D hH hD hDH⟩

end BinaryLinearThree.SingerRestriction
