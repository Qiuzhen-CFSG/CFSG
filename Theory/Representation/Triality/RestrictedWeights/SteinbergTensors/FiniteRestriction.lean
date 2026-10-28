module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Contracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.HighestWeight
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FixedLine

/-!
# Reductions for D4 graph-field finite restriction

The shared geometric hypotheses and exact restricted-weight statements are in
`Geometry` and `Contracts`. The equal-weight direction follows from algebraic
highest-weight uniqueness. The irreducibility reduction below uses a finite
two-group fixed line and the orbit of its generator under the actual elementary
group; it does not identify that group with all graph-field fixed points.

The finite highest-line, orbit-span, separation, and exhaustivity theorems are
still required to establish GLS3 Theorem 2.8.2. The conditional deductions here
do not assert that source theorem.

Source: `refs/KGroup/GLS3/chapter2.tex`, Definition 2.8.1 and Theorem 2.8.2.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The finite highest-line and orbit-span calculation suffices on the literal
elementary group, with no passage from the full fixed-point group. -/
theorem restriction_irreducible_of_highestLine (S : Geometry K)
    (n : ℕ) (hn : 0 < n) (A : RationalFactor K) (v : A.Space)
    (hU : IsPGroup 2 (positiveUnipotent S n))
    (hline : ∀ w : A.Space,
      (∀ g : positiveUnipotent S n, (A.restrict (S.inclusion n)).ρ g.val w = w) →
        w ∈ Submodule.span k ({v} : Set A.Space))
    (hspan : Submodule.span k (Set.range (fun g =>
      (A.restrict (S.inclusion n)).ρ g v)) = ⊤) :
    Representation.IsIrreducible (A.restrict (S.inclusion n)).ρ := by
  let := S.elementary_finite n hn
  let : Nontrivial (A.restrict (S.inclusion n)) := inferInstanceAs (Nontrivial A.Space)
  exact irreducible_of_fixedLine_of_orbitSpan
    (A.restrict (S.inclusion n)).ρ (positiveUnipotent S n) hU v hline hspan

/-- Once finite separation is proved, the already proved equal-weight
direction gives the full equivalence criterion. -/
theorem restriction_equivalent_iff_of_separation (S : Geometry K) (n : ℕ)
    (hsep : RestrictedSeparation S n) (A C : RationalFactor K) {a b : Weight}
    (har : InRestrictedRange n a) (hbr : InRestrictedRange n b)
    (ha : HasHighestWeight S A a) (hb : HasHighestWeight S C b) :
    Nonempty (Representation.Equiv (A.restrict (S.inclusion n)).ρ
      (C.restrict (S.inclusion n)).ρ) ↔ a = b := by
  exact ⟨hsep A C a b har hbr ha hb,
    fun hab => restriction_equivalent_of_highestWeight_eq S A C ha hb hab n⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
