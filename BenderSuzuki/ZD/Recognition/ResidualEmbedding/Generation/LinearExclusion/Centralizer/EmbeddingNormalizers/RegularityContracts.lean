module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceInterfaces

/-!
# The source split-torus action in the linear branch

This is the exact fixed-coset assertion of GLS IV, Chapter 2, Proposition
12.13. It connects its Sylow and weak-closure proof with the prime-stabilizer
argument of Lemma 12.14. Both concern the original quotient G/M and the
literal residual commutator K. This declaration supplies no proof of the
assertion; the embedding assembly must construct it from the original Context.

Source: refs/KGroup/GLS4/Chapter2.tex, Proposition 12.13 and Lemma 12.14.
-/

namespace BenderSuzuki.ZD.LinearExclusion

/-- The only fixed cosets of a nonidentity source torus element are the
original two distinguished cosets. -/
@[expose] public def TorusSemiregular {G : Type*} [Group G]
    (M : Subgroup G) (t : G) : Prop :=
  ∀ x ∈ residualCommutator M t, x ≠ 1 → ∀ beta : G ⧸ M,
    x • beta = beta ↔ beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t

end BenderSuzuki.ZD.LinearExclusion
