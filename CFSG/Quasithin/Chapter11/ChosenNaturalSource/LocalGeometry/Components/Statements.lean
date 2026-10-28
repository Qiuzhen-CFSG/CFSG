module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.MainForward.SourceFamilies
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The complete relative-component alternatives in 11.1

These are output specifications, not recognition assumptions or proved
classification results. Every model refers to the literal two-core quotient.
The odd extensions have an actual normal kernel; no splitting is imposed.
The exceptional triangle retains the original K, X, L₁, L₂ and its other
parabolic residual K₀. Its two orientations are both allowed.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.1--11.1.2, printed pp.761--765; extension notation as in A.3.12--14.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G]

/-- All the characteristic-two rows, with the field tied to the original q.
The last triality row uses q = (2^m)^3, not an unrestricted smaller field. -/
inductive LieOvergroup (A : Type*) [Group A] (n : ℕ) : Prop where
  | sl3 (model : Source.IsSL A 3 (2 ^ n))
  | psl3 (model : ClassicalGroup.IsPSL A 3 (2 ^ n))
  | sp4 (model : Source.IsSp A 2 (2 ^ n))
  | g2 (model : ClassificationModels.IsG2At A (2 ^ n))
  | ree (m : ℕ) (positive : 1 ≤ m) (field : n = 2 * m + 1)
      (model : IsReeF4At A m)
  | triality (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) A)
  | trialityCube (m : ℕ) (positive : 1 ≤ m) (field : n = 3 * m)
      (model : Triality.Standard.IsTrialityGroupAt (2 ^ m) A)

/-- The full extra list at q=4. The covering rows mean central three-covers,
and E_(p²) means an elementary abelian kernel of order p². -/
inductive FieldFourOvergroup (A : Type*) [Group A] : Prop where
  | alternating (model : IsAlternating A 7)
  | alternatingCover (model : IsAlternatingCover A 7)
  | primeLinear (p : ℕ) (prime : Source.ExceptionalPrime p)
      (model : ClassicalGroup.IsPSL A 2 p)
  | linearTwentyFive (model : ClassicalGroup.IsPSL A 2 25)
  | three (unitary : Bool)
      (model : IsPSLSign A unitary 3 5 ∨ IsSLSign A unitary 3 5)
  | m22 (model : Nonempty (A ≃* Sporadic.Mathieu.M22))
  | m22Cover (model : IsM22Cover A)
  | m23 (model : Nonempty (A ≃* Sporadic.Mathieu.M23))
  | j1 (model : Nonempty (A ≃* Janko1.Model))
  | j2 (model : Nonempty (A ≃* Sporadic.LeechRelated.J2.Carrier))
  | j4 (model : Nonempty (A ≃* Janko4.Model))
  | hs (model : Nonempty (A ≃* Sporadic.LeechRelated.HS.Carrier))
  | ru (model : Nonempty (A ≃* Rudvalis.Model))
  | nilpotentExtension (model : HasExtension A
      (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
      (fun Q _ => Source.IsSL Q 2 5))
  | elementaryExtension (p : ℕ) (prime : Source.ExceptionalPrime p)
      (model : HasExtension A (ElementaryModel p 2) (fun Q _ => Source.IsSL Q 2 p))

/-- The alternatives of 11.1.1, including actual equality in its first row. -/
inductive ComponentAlternative (Li K : Subgroup G) (n : ℕ) : Prop where
  | equal (eq : Li = K)
  | lie (model : LieOvergroup (K ⧸ pCore 2 K) n)
  | four (field : n = 2) (model : FieldFourOvergroup (K ⧸ pCore 2 K))

/-- The literal projective general linear model used in the triangle. -/
def IsPGLThreeFour (A : Type*) [Group A] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (A ≃* Matrix.ProjGenLinGroup (Fin 3) F)

/-- The source permits interchanging L and I, so neither orientation is discarded. -/
def TriangleOrientation (L I : Subgroup G) : Prop :=
  (ClassificationModels.IsG2At (L ⧸ pCore 2 L) 4 ∧ Source.IsSp (I ⧸ pCore 2 I) 2 4) ∨
  (Source.IsSp (L ⧸ pCore 2 L) 2 4 ∧ ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)

/-- All clauses of 11.1.2(3), with the product KX represented by its join.
The normalizer hypotheses on X in the source make this join the product. -/
def FieldFourTriangle (T : Sylow 2 G) (L L₁ L₂ K X : Subgroup G) : Prop :=
  IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) ∧
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ L₁ ∧
      (∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K → J ≠ K → J ≠ L₁ → J = K₀) ∧
      (K₀ ⊔ L₂) ∈ Chapter1.LStar G T ∧
      (K₀ ⊔ L₂) ∈ MainForward.faithfulLocalComponents T ∧
      TriangleOrientation L (K₀ ⊔ L₂)

/-- All alternatives of 11.1.2. Index zero means source i=1, index one i=2. -/
inductive RefinementAlternative (T : Sylow 2 G) (L L₁ L₂ K X : Subgroup G)
    (i : Fin 2) (n : ℕ) : Prop where
  | equal (eq : (if i = 0 then L₁ else L₂) = K)
  | sl2 (index : i = 0) (field : n = 2) (p : ℕ)
      (prime : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
      (model : Source.IsSL (Source.TwoOddQuotient K) 2 p)
  | psl2 (index : i = 0) (field : n = 2) (p : ℕ) (prime : p.Prime) (large : 11 ≤ p)
      (model : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p)
      (excluded : ¬ Source.IsSL (L ⧸ pCore 2 L) 3 4)
  | triangle (index : i = 0) (field : n = 2)
      (geometry : FieldFourTriangle T L L₁ L₂ K X)

/-- The output of the local sieve before constructing the third vertex of
the PGL₃(4) triangle. This is deliberately weaker than 11.1.2. -/
inductive RefinementReduction (L L₁ L₂ K X : Subgroup G)
    (i : Fin 2) (n : ℕ) : Prop where
  | equal (eq : (if i = 0 then L₁ else L₂) = K)
  | sl2 (index : i = 0) (field : n = 2) (p : ℕ)
      (prime : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
      (model : Source.IsSL (Source.TwoOddQuotient K) 2 p)
  | psl2 (index : i = 0) (field : n = 2) (p : ℕ) (prime : p.Prime) (large : 11 ≤ p)
      (model : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p)
      (excluded : ¬ Source.IsSL (L ⧸ pCore 2 L) 3 4)
  | pgl3 (index : i = 0) (field : n = 2)
      (model : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))

/-- Assembly of the local sieve and the independent triangle construction.
The callback is a still-required source proof, never a substitute for it. -/
theorem RefinementReduction.complete {T : Sylow 2 G} {L L₁ L₂ K X : Subgroup G}
    {i : Fin 2} {n : ℕ} (h : RefinementReduction L L₁ L₂ K X i n)
    (triangle : i = 0 → n = 2 →
      IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) →
      FieldFourTriangle T L L₁ L₂ K X) :
    RefinementAlternative T L L₁ L₂ K X i n := by
  cases h with
  | equal he => exact .equal he
  | sl2 hi hn p hp hm => exact .sl2 hi hn p hp hm
  | psl2 hi hn p hp hl hm hx => exact .psl2 hi hn p hp hl hm hx
  | pgl3 hi hn hm => exact .triangle hi hn (triangle hi hn hm)

/-- The second-normalizer equality does not depend on constructing the triangle. -/
theorem RefinementReduction.second_eq {L L₁ L₂ K X : Subgroup G}
    {n : ℕ} (h : RefinementReduction L L₁ L₂ K X 1 n) : L₂ = K := by
  cases h with
  | equal he => simpa using he
  | sl2 hi _ _ _ _ => exact (by cases hi)
  | psl2 hi _ _ _ _ _ _ => exact (by cases hi)
  | pgl3 hi _ _ => exact (by cases hi)

/-- In the second flag normalizer the refinement leaves only equality. -/
theorem RefinementAlternative.second_eq {T : Sylow 2 G} {L L₁ L₂ K X : Subgroup G}
    {n : ℕ} (h : RefinementAlternative T L L₁ L₂ K X 1 n) : L₂ = K := by
  cases h with
  | equal h => simpa using h
  | sl2 hi _ _ _ _ => exact (by cases hi)
  | psl2 hi _ _ _ _ _ _ => exact (by cases hi)
  | triangle hi _ _ => exact (by cases hi)

/-- The actual second-normalizer application, retaining relative normality. -/
theorem second_normal_component {T : Sylow 2 G} {L L₁ L₂ H K X : Subgroup G}
    {n : ℕ} (hK : Source.NormalComponentIn H K)
    (h : RefinementAlternative T L L₁ L₂ K X 1 n) : Source.NormalComponentIn H L₂ := by
  rw [h.second_eq]
  exact hK

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
