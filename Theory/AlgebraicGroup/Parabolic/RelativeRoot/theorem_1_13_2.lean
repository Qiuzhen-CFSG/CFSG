module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.theorem_1_12_9
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.UnipotentCandidate

/-!
This module contains the standard-parabolic classification statement of GLS3
Theorem 1.13.2 and the derived and semisimple candidates used in Theorem 1.13.3.
It re-exports the topic-level standard unipotent candidate, defined as the
Zariski closure of the positive root factor outside the chosen subsystem.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_13_2
    {K : Variety k} [AlgebraicGroup K]
    (T B : ClosedSubgroup K) (D : RootGroupData K T)
    (hK : IsReductiveAlgebraicGroup K)
    (hAligned : IsAlignedStandardBorelSetup T B D D.positive) :
    (∀ J : Set D.Root, J ⊆ D.simple →
      IsParabolicSubgroup (parabolicCandidate T D D.positive J) ∧
      B ≤ parabolicCandidate T D D.positive J) ∧
    (∀ J : Set D.Root, J ⊆ D.simple →
      ∀ x : Variety.Point K,
        x ∈ parabolicCandidate T D D.positive J ↔
          ∃ b₁ n b₂ : Variety.Point K,
            b₁ ∈ B ∧ n ∈ parabolicNormalizerPart T D J ∧
              b₂ ∈ B ∧ x = b₁ * n * b₂) ∧
    (∀ Q : ClosedSubgroup K, IsParabolicSubgroup Q →
      ∃ J : Set D.Root, J ⊆ D.simple ∧
        ∃ g : Variety.Point K,
          Q = (parabolicCandidate T D D.positive J).conjugate g) ∧
    (∀ J J' : Set D.Root, J ⊆ D.simple → J' ⊆ D.simple →
      (parabolicCandidate T D D.positive J ≤
        parabolicCandidate T D D.positive J' ↔ J ⊆ J')) ∧
    (∀ Q : ClosedSubgroup K, IsParabolicSubgroup Q → B ≤ Q →
      ∃ J : Set D.Root, J ⊆ D.simple ∧
        Q = parabolicCandidate T D D.positive J) ∧
    parabolicCandidate T D D.positive ∅ = B ∧
    parabolicCandidate T D D.positive D.simple = ClosedSubgroup.top (G := K) ∧
    (∀ P : ClosedSubgroup K, IsParabolicSubgroup P → P.normalizer = P) ∧
    (∀ J J' : Set D.Root, J ⊆ D.simple → J' ⊆ D.simple →
      ∀ g : Variety.Point K,
        (parabolicCandidate T D D.positive J).conjugate g =
          parabolicCandidate T D D.positive J' →
        J = J' ∧ g ∈ parabolicCandidate T D D.positive J) := by sorry

public noncomputable def derivedCandidate
    {K : Variety k} [AlgebraicGroup K]
    (L : ClosedSubgroup K) : ClosedSubgroup K :=
  subgroupZariskiClosure K ⁅L.toSubgroup, L.toSubgroup⁆

public noncomputable def mCandidate
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (J : Set D.Root) : ClosedSubgroup K :=
  subgroupZariskiClosure K (standardLeviRootFactor D (RootSubsystemSpan D J))

public def HasRootSubsystem
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (L : ClosedSubgroup K) (D : RootGroupData K T)
    (sigmaJ : Set D.Root) : Prop :=
  ∀ α, α ∈ sigmaJ ↔ D.rootSubgroup α ≤ L

end Theory.AlgebraicGroup
