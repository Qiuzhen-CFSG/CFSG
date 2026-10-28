module

public import BenderSuzuki.MatrixGroups.Unitary
public import BenderSuzuki.SE.Basic
public import Theory.GroupTheory.SetStrongClosure

/-!
# The unitary commuting-pair fusion input

This is a specification of the remaining intrinsic model calculation, not
an assertion that it holds. In an automorphism overgroup of the actual PSU₃
matrix group, two commuting subgroups of a Sylow two-subgroup have a strongly
closed union and only inner involutions. The required conclusion identifies
an elementary smaller factor. The elementary clause is needed when lifting
back through an ambient action whose kernel need not have odd order.

The intended binary specialization keeps matrix-field order q² and Hermitian
fixed-field order q separately. Its application is the terminal argument of
Aschbacher, *On finite groups of component type* (1975), Lemma 3.4, pp.94–96,
after Theorem ZD of GLS, Volume 4, Chapter 2.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.HermitianForm
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The precise intrinsic fusion calculation still needed for the binary
unitary branch. Containment alone is not the requested model output. -/
def StronglyClosedPairRigidity : Prop :=
  ∀ (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))),
    (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K →
    ∀ (T : Sylow 2 K) (B₁ B₂ : Subgroup K),
      B₁ ≤ (T : Subgroup K) → B₂ ≤ (T : Subgroup K) →
      ⁅B₁, B₂⁆ = ⊥ → TwoRankAtLeastTwo B₁ → TwoRankAtLeastTwo B₂ →
      IsStronglyClosedSet ((B₁ : Set K) ∪ B₂) (T : Subgroup K) ⊤ →
      (∀ b : K, b ∈ (B₁ : Set K) ∪ B₂ → BenderSuzuki.PFAppendixIII.IsInvolution b →
        (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ∈
          (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range) →
      (B₁ ≤ B₂ ∧ ∀ b ∈ B₁, b ^ 2 = 1) ∨
        (B₂ ≤ B₁ ∧ ∀ b ∈ B₂, b ^ 2 = 1)

end BenderSuzuki.MatrixGroups.HermitianForm
end
