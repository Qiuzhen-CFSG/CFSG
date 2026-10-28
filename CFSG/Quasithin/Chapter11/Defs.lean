module

public import Theory.PGroupCore

/-!
# Legacy elementary interfaces for Chapter 11

The declarations in this file are retained for public compatibility. They do
not formalize §§11.1–11.2 of Aschbacher–Smith. In particular the alternatives
below are uninformative labels, `ComponentEmbedding.normal` is ambient
normality rather than normality in `H`, and `Section11Input` is not the
chapter's counterexample setup. No recognition theorem produces these records
in the current development.

Genuine group-dependent definitions are in `Section01To02.SourceDefs`.
The elementary normalizer notation here remains useful independently.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter11

open Subgroup

variable {G : Type*} [Group G]

/-- The three rank-two Lie types occurring in Lemma 11.0.2. -/
inductive LieRankTwoType where
  | sl3
  | sp4
  | g2
  deriving DecidableEq, Repr

/-- Legacy labels, not the exceptional alternatives of 11.1.1(3). -/
inductive ExceptionalType where
  | a7
  | a7Hat
  | l2Prime (p : ℕ)
  | l2TwentyFive
  | sl3Five
  | m22
  | m22Hat
  | m23
  | j1
  | j2
  | j4
  | hs
  | ru
  | sl2FiveOverOdd
  | sl2PrimeOverTwo (p : ℕ)
  deriving DecidableEq, Repr

/-- A subgroup which is invariant under a subgroup `T`. -/
def TInvariant (T U : Subgroup G) : Prop := T ≤ normalizer (U : Set G)

/-- The normalizer notation used in §§11.1–11.2. -/
def NG (U : Subgroup G) : Subgroup G := normalizer (U : Set G)

/-- Legacy invariant subgroup with a numerical label. No field, vector-space
structure or dimension assertion is encoded by `rank`. -/
structure InvariantSubspace (T V : Subgroup G) where
  carrier : Subgroup G
  le_ambient : carrier ≤ V
  rank : ℕ
  invariant : TInvariant T carrier

/-- Legacy, always-inhabited labels. This is not a classification predicate. -/
inductive ComponentAlternative (n : ℕ) : Prop where
  | equal
  | lie (kind : LieRankTwoType)
  | exceptional (kind : ExceptionalType) (p : ℕ := 0)

/-- Legacy data with ambient normality. Neither the source component condition
nor quotient-model isomorphisms are encoded here. -/
structure ComponentEmbedding (H L : Subgroup G) (n : ℕ) where
  K : Subgroup G
  le_component : L ≤ K
  normal : K.Normal
  contained : K ≤ H
  alternative : ComponentAlternative n

/-- Legacy numerical record; these fields do not define weak-closure parameters. -/
structure WeakClosureData (T M V : Subgroup G) where
  r : ℕ
  w : ℕ
  s : ℕ
  r_lower : s ≤ r
  weakClosure : Subgroup G
  weakClosure_le : weakClosure ≤ NG V

/-- Legacy elementary inputs. Not the source hypotheses of Chapter 11. -/
structure Section11Input (G : Type*) [Group G] [Finite G] where
  T : Subgroup G
  L : Subgroup G
  M : Subgroup G
  V : Subgroup G
  V1 : Subgroup G
  V2 : Subgroup G
  V3 : Subgroup G
  L1 : Subgroup G
  L2 : Subgroup G
  n : ℕ
  n_gt_one : 1 < n
  t_invariant_V : TInvariant T V
  t_invariant_V1 : TInvariant T V1
  t_invariant_V2 : TInvariant T V2
  v1_le_v2 : V1 ≤ V2
  v2_le_v : V2 ≤ V
  v1_le_v : V1 ≤ V
  normalizer_V1 : ComponentEmbedding (NG V1) L1 n
  normalizer_V2 : ComponentEmbedding (NG V2) L2 n

end CFSG.Quasithin.Chapter11
