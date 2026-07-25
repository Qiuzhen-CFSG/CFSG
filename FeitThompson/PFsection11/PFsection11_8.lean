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
# Peterfalvi, Section 11: Theorem (11.8)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section11
universe u v w

/-! ## (11.8) -/

/-- Peterfalvi `(11.8)`. -/
@[expose] public def theorem_11_8_statement
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF H U C H0 W1 W2 : Subgroup G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S SHC : Finset (Section1.ClassFunction M))
    (R : Finset (Section1.ClassFunction G))
    (i0 : I) (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction M)
    (p q : ℕ) : Prop :=
  hypothesis_11_2_data M MF H U C H0 W1 W2 S τ p q →
    Section10.section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ →
      section11Subfamily (H ⊔ C) S SHC →
        ζ ∈ SHC →
          transformedIrreducibleFamily R σ →
            theorem_11_8_nonorthogonality R τ ζ (Section10.muColumn μ j0)
              (fun i : I => σ (ω i j0))

/-- Peterfalvi `(11.8.1)`. -/
@[expose] public def theorem_11_8_1_statement
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J]
    (M MF H U C H0 W1 W2 : Subgroup G)
    (S S1 : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (p q d u n : ℕ) (δ : ℤ) : Prop :=
  hypothesis_11_2_data M MF H U C H0 W1 W2 S τ p q →
    Section10.uniformMuData W1 W2 j0 μ δSign d n δ →
      section11Subfamily (H ⊔ C) S S1 →
        u = Nat.card U / Nat.card C →
          Section11.theorem_11_8_1_characterCountData S1 j0 μ q u →
          d = u ∧
            δ = 1 ∧
            n = S1.card ∧
            n = (u - 1) / q

/-- Peterfalvi `(11.8.2)`. -/
@[expose] public def theorem_11_8_2_statement
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M W1 W2 : Subgroup G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S1 : Finset (Section1.ClassFunction M))
    (S1τ : Finset (Section1.ClassFunction G))
    (i0 : I) (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction M)
    (i : I) (j : J)
    (d n : ℕ) (δ : ℤ) : Prop :=
  Section10.section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ →
    Section10.uniformMuData W1 W2 j0 μ δSign d n δ →
      j ≠ j0 →
        ζ ∈ S1 →
          transformedSubfamily S1 S1τ τ₁ →
            Section7.isCoherentExtension S1 τ τ₁ →
              δ = 1 →
              n = S1.card →
              (∃ X : Section1.ClassFunction G, ∃ a : ℕ,
                theorem_11_8_2_projectionData S1τ τ τ₁
                  (Section10.alphaChar μ ζ n δ j0 i j) ζ X
                  (σ (ω i j)) (σ (ω i j0)) a n) →
              ∃ X : Section1.ClassFunction G, ∃ a : ℕ,
                theorem_11_8_2_expansionData S1τ τ τ₁
                  (Section10.alphaChar μ ζ n δ j0 i j) ζ X
                  (σ (ω i j)) (σ (ω i j0)) a n

/-- Peterfalvi `(11.8.3)`. -/
@[expose] public def theorem_11_8_3_statement
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M W1 W2 : Subgroup G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S1 : Finset (Section1.ClassFunction M))
    (i0 : I) (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction M)
    (d n : ℕ) (δ : ℤ) : Prop :=
  Section10.section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ →
    Section10.uniformMuData W1 W2 j0 μ δSign d n δ →
      ζ ∈ S1 →
        Section7.isCoherentExtension S1 τ τ₁ →
          δ = 1 →
          theorem_11_8_3_realityData τ τ₁ μ
            (fun i j => σ (ω i j))
            (fun i => σ (ω i j0))
            ζ n δ j0 →
          ∃ β : I → J → Section1.ClassFunction G,
            theorem_11_8_3_betaData τ τ₁
              (fun i j => Section10.alphaChar μ ζ n δ j0 i j)
              (fun i j => σ (ω i j))
              (fun i => σ (ω i j0))
              ζ n j0 β

/-- Peterfalvi `(11.8.4)`. -/
@[expose] public def theorem_11_8_4_statement
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (M : Subgroup G)
    (W : Subgroup M)
    (S1 : Finset (Section1.ClassFunction M))
    (R : Finset (Section1.ClassFunction G))
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ μ0 : Section1.ClassFunction M)
    (ω0 : I → Section1.ClassFunction W) : Prop :=
  transformedIrreducibleFamily R σ →
    ζ ∈ S1 →
    Section7.isCoherentExtension S1 τ τ₁ →
    Section5.orthogonalToFinset R
        (τ (μ0 - ζ) - Finset.sum Finset.univ (fun i : I => σ (ω0 i))) →
    theorem_11_8_4_replacementData S1 τ τ₁ ζ μ0 (fun i : I => σ (ω0 i)) →
      τ (μ0 - ζ) =
          Finset.sum Finset.univ (fun i : I => σ (ω0 i)) - τ₁ ζ ∨
        ∃ τ₁' : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
          Section7.isCoherentExtension S1 τ τ₁' ∧
            τ (μ0 - ζ) =
              Finset.sum Finset.univ (fun i : I => σ (ω0 i)) - τ₁' ζ

/-- Peterfalvi `(11.8.5)`. -/
@[expose] public def theorem_11_8_5_statement
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {W : Type u} [Group W] [Finite W]
    {I J : Type*} [Fintype I] [Fintype J]
    (S1τ : Finset (Section1.ClassFunction G))
    (i0 : I) (j0 : J)
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (μ : I → J → Section1.ClassFunction M)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (i : I) (j : J)
    (ζ μ0 : Section1.ClassFunction M)
    (X : Section1.ClassFunction G)
    (β : I → J → Section1.ClassFunction G)
    (a n : ℕ) (δ : ℤ) : Prop :=
  i ≠ i0 →
    j ≠ j0 →
    theorem_11_8_2_expansionData S1τ τ τ₁
        (Section10.alphaChar μ ζ n δ j0 i j) ζ X (σ (ω i j)) (σ (ω i j0)) a n →
    theorem_11_8_3_betaData τ τ₁
        (fun i j => Section10.alphaChar μ ζ n δ j0 i j)
        (fun i j => σ (ω i j))
        (fun i => σ (ω i j0))
        ζ n j0 β →
      τ (μ0 - ζ) =
          Finset.sum Finset.univ (fun i : I => σ (ω i j0)) - τ₁ ζ →
        theorem_11_8_5_scalarData a →
        a = 0

/-- Peterfalvi `(11.8.6)`. -/
@[expose] public def theorem_11_8_6_statement
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J]
    (M MF H U C H0 W1 W2 : Subgroup G)
    (W : Subgroup M)
    (S SHC S2 SC : Finset (Section1.ClassFunction M))
    (S1τ S2τ : Finset (Section1.ClassFunction G))
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ τ₁ τ₂ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction M)
    (p q d : ℕ)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (ω : I → J → Section1.ClassFunction W) : Prop :=
  hypothesis_11_2_data M MF H U C H0 W1 W2 S τ p q →
    section11Subfamily (H ⊔ C) S SHC →
      section11Subfamily C S SC →
        theorem_11_8_6_contradictionData SHC S2 SC S1τ S2τ σ τ τ₁ τ₂ ζ j0 μ ω d →
          ¬ Section6.coherentFamily SC τ

end Section11
