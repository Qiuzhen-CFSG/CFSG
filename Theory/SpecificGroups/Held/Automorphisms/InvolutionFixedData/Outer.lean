module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Certificate

/-!
# The outer Held involution fixed-subgroup row

Every outer involution induced by the full degree-2058 permutation normalizer
has a normal quasisimple subgroup of index two and center order three in its
literal fixed subgroup. We choose that fixed subgroup's commutator, using
the concrete representative calculation and full-normalizer fusion certificate.
The certificate proves faithfulness before passing from the order of the action
to the order of its implementing permutation.

This discharges the outer-row input to the Held component exclusion in E.6.23.
No abstract automorphism realization or additional model hypothesis is needed.
The simplicity and perfectness hypotheses inherited by that consumer are also
unnecessary for this concrete calculation.

Sources: GLS3 Table 5.3p, printed p.277, outer `2C` row `3#S7 = 3A7.2`,
with the covering conventions on pp.260–261; Aschbacher–Smith, Theorem C,
printed p.33, and E.6.23, printed p.254 (PDF p.265).
-/

public section

namespace Held.InvolutionFixedData

/-- The genuine triple-cover row for every implemented outer involution.
The witness is normal in the fixed subgroup itself. -/
theorem outerRow : OuterRow := by
  intro n hn hout
  exact ⟨commutator (permutationGroup.normalizerMonoidHom n).fixedSubgroup,
    OuterInvolution.fixed_commutator n hn hout⟩

end Held.InvolutionFixedData
