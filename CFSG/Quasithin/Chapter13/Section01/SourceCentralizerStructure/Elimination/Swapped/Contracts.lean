module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits

/-!
# Remaining geometric contracts for the exchanged centralizer components

These are intermediate conclusions to be constructed, not additional source
hypotheses. The orbit and swapping factorization use T_u = T intersect C_G(u).
Every model marks K/O₂(K), leaving the actual component and its central covers
intact. The last contract is an actual pair of order-p subgroups of the chosen
Sylow complement, permuted by its normalizer in L.

Source: Aschbacher--Smith, 13.1.12(3), printed pp.874--875.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G]

/-- The source rows before the characteristic-two/ordinary-component split.
The odd-prime row is refined further in the ordinary-component argument. -/
inductive SwappedRow (p : ℕ) (Q : Type*) [Group Q] : Prop
  | linear_even (n : ℕ) (hn : 2 ≤ n) (congruence : Nat.ModEq p (2 ^ n) 1)
      (model : ClassicalGroup.IsPSL Q 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m) (congruence : Nat.ModEq p (2 ^ (2 * m + 1)) 1)
      (model : Nonempty (Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | janko (prime : p = 7) (model : Nonempty (Q ≃* Janko1.Model))
  | linear_prime (r : ℕ) (prime : r.Prime) (odd : Odd r)
      (model : ClassicalGroup.IsPSL Q 2 r)

/-- The precise output of the orbit-containment and Sylow-factor sieve.
P is the ambient image of the chosen Sylow subgroup in all consumers. -/
structure SwappedData (T : Sylow 2 G) (L : Subgroup G) (p : ℕ) (u : G)
    (K P : Subgroup G) : Prop where
  contained : XiP p L ≤ componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
  plane : Nonempty (P ≃* Plane p)
  factors : SwappedFactors ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) P K
  permutable : (P : Set G) * (((T : Subgroup G) ⊓ centralizer ({u} : Set G)) : Set G) =
    ((((T : Subgroup G) ⊓ centralizer ({u} : Set G)) : Set G) * (P : Set G))
  row : SwappedRow p (XiQuotient K)

/-- A genuine pair of distinct order-p subgroups under the actual N_L(P)-action. -/
structure NormalizerLinePair (L P : Subgroup G) (p : ℕ) where
  first : Subgroup G
  second : Subgroup G
  first_le : first ≤ P
  second_le : second ≤ P
  first_card : Nat.card first = p
  second_card : Nat.card second = p
  distinct : first ≠ second
  permuted : ∀ g ∈ L ⊓ normalizer (P : Set G),
    first.conjBy g = first ∨ first.conjBy g = second

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
