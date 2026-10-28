module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Foundations

/-!
# Interfaces between the centralizer arguments of Sections 12 and 13

These propositions specify the outstanding local recognition, counting,
and unitary-exclusion arguments. They are conclusions to be constructed,
not additional axioms or assertions that the corresponding book results
have been proved. Their assembly belongs to `Centralizers`.

The local contract separates Lemmas 12.3–12.4 from shearing and counting.
The counting contract retains the actual coset action, the uniform choice
of the three cases in Lemma 12.10, and the fusion conclusion of 12.11.
The unitary covers are actual special or projective special unitary matrix
groups: the matrix field has order `q²` and its fixed field has order `q`.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.3–12.11 and Section 13.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup _root_.BenderSuzuki.MatrixGroups
open scoped Pointwise
universe u

/-- The two actual unitary covers in Lemma 12.3, with fixed-field exponent `n`.
The rank-three Hermitian form and both field orders are part of the model. -/
@[expose] public def IsUnitaryCentralizerCoverAt
    (n : ℕ) (H : Type u) [Group H] : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = (2 ^ n) ^ 2 ∧
    Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
    (Nonempty (H ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (H ≃* J.specialSubgroup))

variable {G : Type u} [Group G] [Finite G]

/-- The local source conclusions required before the shearing/counting
argument. Its producer must prove these from the original proper-`L` inputs. -/
public structure ResidualCentralizerLocalData
    (Z : Set G) (M : Subgroup G) (z t : G) : Prop where
  /-- Lemma 12.3, including the actual central cover and the same field size. -/
  centralizing_extension : ∀ v ∈ centralizer (residualGenerated M z t : Set G), v ≠ 1 →
    centralizerClosure Z v = residualGenerated M z t ∨
      ∃ n : ℕ, 2 ≤ n ∧ Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n ∧
        Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup n) ∧
        residualGenerated M z t < centralizerClosure Z v ∧
        IsUnitaryCentralizerCoverAt n (centralizerClosure Z v)
  /-- Lemma 12.4(b), retaining the actual centralizer inside `L`. -/
  involution_action : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    v ∈ centralizer (residualGenerated M z t : Set G) ∨
      ∃ k : ℕ, 2 ≤ k ∧
        Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k ∧
        Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup (2 * k)) ∧
        Nonempty ((residualGenerated M z t ⊓ centralizer ({v} : Set G) : Subgroup G) ≃*
          PSL2BinaryMatrixGroup k)
  /-- Lemma 12.4(c), for the literal odd-core quotient. -/
  quotient_models : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    pPrimeCore 2 (centralizerClosure Z v) = center (centralizerClosure Z v) ∧
      ∃ k : ℕ, 2 ≤ k ∧
        Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k ∧
        IsSimpleBenderGroupAtExponent k
          (centralizerClosure Z v ⧸ pPrimeCore 2 (centralizerClosure Z v))
  /-- Lemma 12.4(d), transitivity on the punctured distinguished coset. -/
  punctured_coset_conjugacy : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    ∀ a ∈ closure (Z ∩ (M : Set G)), Commute a v → a ≠ 1 →
    ∀ b ∈ closure (Z ∩ (M : Set G)), Commute b v → b ≠ 1 →
      ∃ g ∈ M ⊓ centralizerClosure Z v, MulAut.conj g (a * v) = b * v
  /-- Lemma 12.4(e), as an equality of actual set products. -/
  centralizer_factorization : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    (centralizer ({v} : Set G) : Set G) = (centralizerClosure Z v : Set G) *
      ((residualPairStabilizer M t ⊓ centralizer ({v} : Set G) : Subgroup G) : Set G)

/-- Shearing in Definition 12.5 and Lemma 12.7, including the identity in
the fixed subgroup. This is a fusion assertion, not a counting premise. -/
@[expose] public def ResidualCentralizerShearing
    (Z : Set G) (M : Subgroup G) (t : G) : Prop :=
  ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    ∀ a ∈ closure (Z ∩ (M : Set G)), Commute a v → IsConj v (a * v)

/-- The remaining Section 13 alternative, uniform over the involutions of
`D`. The special-unitary central kernel has not been discarded. -/
@[expose] public def ResidualUnitaryCentralizers
    (Z : Set G) (M : Subgroup G) (z t : G) (n : ℕ) : Prop :=
  ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    residualGenerated M z t < centralizerClosure Z v ∧
      IsUnitaryCentralizerCoverAt n (centralizerClosure Z v)

/-- The uniform alternatives of Lemma 12.10, with its actual fixed-coset
counts. The two first branches include centralizer collapse; the third
still requires the independent unitary exclusion. -/
@[expose] public def ResidualCentralizerCases
    (Z : Set G) (M : Subgroup G) (z t : G) (n : ℕ) : Prop :=
  let L := residualGenerated M z t
  let D := residualPairStabilizer M t
  let q := 2 ^ n
  (Nonempty (L ≃* PSL2BinaryMatrixGroup n) ∧
    Nat.card (G ⧸ M) = q ^ 3 + 1 ∧
    ∀ v ∈ D, PFAppendixIII.IsInvolution v → centralizerClosure Z v = L ∧
      Nat.card {beta : G ⧸ M // v • beta = beta} = q + 1) ∨
  (∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧ Nonempty (L ≃* SuzukiMatrixGroup m) ∧
    Nat.card (G ⧸ M) = (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) ∧
    ∀ v ∈ D, PFAppendixIII.IsInvolution v → centralizerClosure Z v = L ∧
      Nat.card {beta : G ⧸ M // v • beta = beta} = q ^ 2 + 1) ∨
  (Nonempty (L ≃* PSL2BinaryMatrixGroup n) ∧
    ResidualUnitaryCentralizers Z M z t n ∧
    Nat.card (G ⧸ M) = (q ^ 3 + 1) * (q ^ 3 * (q - 1) + 1) ∧
    ∀ v ∈ D, PFAppendixIII.IsInvolution v →
      Nat.card {beta : G ⧸ M // v • beta = beta} = q ^ 3 + 1)

/-- The part of Sections 12.7–12.11 consumed by Proposition 13.1 and the
independent Suzuki exclusion. Every field is a remaining proof obligation. -/
public structure ResidualCentralizerCountingData
    (Z : Set G) (M : Subgroup G) (z t : G) : Prop where
  shearing : ResidualCentralizerShearing Z M t
  /-- Lemma 12.9. -/
  centralizes : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    v ∈ centralizer (residualGenerated M z t : Set G)
  /-- Lemma 12.11(b); `Z` already consists of two-central involutions. -/
  nondistinguished_fusion : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
    ∃ d ∈ residualPairStabilizer M t, IsConj v d
  /-- Lemma 12.10, with the field exponent tied to the distinguished subgroup. -/
  cases : ∃ n : ℕ, 2 ≤ n ∧ Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n ∧
    ResidualCentralizerCases Z M z t n

end BenderSuzuki.ZD
