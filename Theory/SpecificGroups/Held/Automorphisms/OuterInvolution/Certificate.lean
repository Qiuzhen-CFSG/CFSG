module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCoverCommutator

/-!
# The concrete Held outer involution fixed-subgroup certificate

Every noninner involutory action induced by the full permutation normalizer
is Held-conjugate to the checked representative. Transport of its actual
triple-A7 covering subgroup supplies a normal quasisimple subgroup of index
two and center order three. This subgroup is the commutator of the literal
fixed subgroup, giving a canonical witness for every implementing permutation.

Both the representative calculation and the full-normalizer conjugacy coverage
are discharged here. Only the induced action is assumed to have order two;
faithfulness in the coverage proof supplies the implementing permutation's order.
No abstract automorphism realization or simplicity hypothesis is required.

Source: GLS3 Table 5.3p, outer 2C row `3#S7 = 3A7.2`, and the interpretation
on pp.260–261. The certificate states the component facts used in E.6.23.
-/

public section

open Subgroup Theory.GroupTheory
namespace Held.OuterInvolution

/-- The commutator of the actual fixed subgroup is its normal quasisimple
subgroup of index two with center order three. -/
theorem fixed_commutator
    (n : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))))
    (hn : orderOf (permutationGroup.normalizerMonoidHom n) = 2)
    (hout : ¬ ∃ g : He, MulAut.conj g = permutationGroup.normalizerMonoidHom n) :
    let L := commutator (permutationGroup.normalizerMonoidHom n).fixedSubgroup
    L.Normal ∧ IsQuasisimple L ∧ L.index = 2 ∧ Nat.card (center L) = 3 :=
  (Fusion.outerRow_of_fixed_cover fixed_cover n hn hout).commutator

/-- The full outer covering row on the concrete degree-2058 Held carrier,
with the commutator as its explicit covering subgroup. -/
theorem outerRow : InvolutionFixedData.OuterRow := by
  intro n hn hout
  exact ⟨commutator (permutationGroup.normalizerMonoidHom n).fixedSubgroup,
    fixed_commutator n hn hout⟩

end Held.OuterInvolution
