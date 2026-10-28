module

public import Theory.Representation.DualCommutator

/-!
# FF-modules for SQTK-groups: duality reduction

This module begins the formalization of Aschbacher–Smith, *The Classification
of Quasithin Groups*, §B.5 (combined 1 March 2004 manuscript). The terminal
lemma B.5.13 reduces its bound on the original module to a quadratic subgroup
with a bounded commutator space on the dual. The bridge below proves that
reduction at the level of a chosen subgroup. The classification and the
construction of that subgroup remain separate mathematical obligations.

The reusable pairing and dimension arguments live in
`Theory.Representation.DualCommutator`.
-/

namespace CFSG.Quasithin.ChapterB

/-- The subgroup-level duality step in B.5.13: a quadratic action with dual
commutator dimension at most twice `r` is equivalent to a quadratic action
with fixed-space codimension at most twice `r` on the original module.
In the source application `r` is the binary rank of the chosen offender. -/
public theorem quadratic_dual_bound_iff
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) (A : Subgroup G) (r : ℕ) :
    (Representation.Coinvariants.ker (Representation.dual (ρ.comp A.subtype)) ≤
        Representation.invariants (Representation.dual (ρ.comp A.subtype)) ∧
      Module.finrank k (Representation.Coinvariants.ker (Representation.dual (ρ.comp A.subtype))) ≤ 2 * r) ↔
    (Representation.Coinvariants.ker (ρ.comp A.subtype) ≤
        Representation.invariants (ρ.comp A.subtype) ∧
      Module.finrank k (V ⧸ Representation.invariants (ρ.comp A.subtype)) ≤ 2 * r) := by
  rw [Representation.quadratic_dual_iff,
    Representation.finrank_quotient_invariants_eq_dual_commutator]

end CFSG.Quasithin.ChapterB
