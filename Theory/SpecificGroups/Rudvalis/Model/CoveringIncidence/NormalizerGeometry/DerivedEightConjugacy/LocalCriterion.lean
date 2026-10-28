module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Data
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A local centralizer criterion for the Rudvalis derived eight-group

This defines the remaining finite-group obligation for the fixed `localP`.
For the centralizer of an involution inside `localP`, order 256 and centrality
of all its involutions should imply that its derived subgroup is normalized
by `localP`. The criterion is a proposition, not an asserted theorem.

`DerivedEightConjugacy` proves that this criterion suffices for the literal
centralizer E₄ × Sz(8) in Rudvalis: Sylow conjugacy places its actual Sylow in
`localP`, maximality identifies the centralizer intersection, and the checked
normal elementary catalogue identifies its derived subgroup.

Source: GLS3 Table 5.3r and pp.291–292; Aschbacher–Smith I.2.2(7), pp.412–413.
This finite local criterion is a sufficient route to the source incidence;
it is not itself a statement quoted from the books.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover

/-- The outstanding local normalization statement. Merely placing a subgroup
in `localP` does not establish this property. -/
@[expose] public def LocalCentralizerDerivedNormal : Prop :=
  ∀ i ∈ localP, i ^ 2 = 1 →
    let K := localP ⊓ centralizer ({i} : Set Model)
    Nat.card K = 256 →
    (∀ x ∈ K, x ^ 2 = 1 → x ∈ centralizer (K : Set Model)) →
    localP ≤ normalizer ((⁅K, K⁆ : Subgroup Model) : Set Model)

end Rudvalis.CoveringIncidence.NormalizerGeometry
