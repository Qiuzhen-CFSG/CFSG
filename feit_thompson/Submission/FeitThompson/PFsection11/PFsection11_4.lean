module

public import FeitThompson.PFsection11.Basic
import FeitThompson.BGsection6.lemma_6_5_a
import FeitThompson.BGsection6.lemma_6_3_a_1
import FeitThompson.PFsection6.PFsection6_2
import FeitThompson.PFsection6.PFsection6_3
import FeitThompson.PFsection6.PFsection6_5_b
import FeitThompson.PFsection2.PFsection2_7_11
import FeitThompson.PFsection8.PFsection8_5_a
import FeitThompson.PFsection8.PFsection8_5_b
import FeitThompson.PFsection8.PFsection8_8
import FeitThompson.PFsection8.SourceTypePBridge
import FeitThompson.PFsection4.PFsection4_4
import FeitThompson.PFsection5.PFsection5_7
import FeitThompson.PFsection5.PFsection5_8
import FeitThompson.PFsection5.PFsection5_9
import FeitThompson.PFsection5.RealVirtualParity
import FeitThompson.PFsection9.PFsection9_3
import FeitThompson.PFsection9.PFsection9_4
import FeitThompson.PFsection9.PFsection9_6
import FeitThompson.PFsection9.PFsection9_7
import FeitThompson.PFsection9.PFsection9_8
import FeitThompson.PFsection9.PFsection9_11
import FeitThompson.PFsection4.PFsection4_5_to_10

/-!
# Peterfalvi, Section 11: Theorem (11.4)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section11
universe u v w

/-! ## (11.4) -/

/-- Peterfalvi `(11.4)`. -/
@[expose] public def theorem_11_4_statement
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF H U C H0 H1 W1 W2 : Subgroup G)
    (S S1 : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ) : Prop :=
  hypothesis_11_2_data M MF H U C H0 W1 W2 S τ p q →
    coherentNormalSubgroupData M H1 S S1 τ →
      2 * q * (Nat.card U / Nat.card C) ≥ H1.relIndex (ambientDerivedSubgroup M) - 1

end Section11
