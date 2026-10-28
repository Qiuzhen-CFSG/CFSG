module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.CharacteristicTwo
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The component needed by the quintic model comparison

This records the intermediate conclusions at the end of printed p.1034
and the start of p.1035. It is a target for component extraction in the
actual second normalizer, not an existence assertion or a proof of the
classification. The final comparison must still prove K₁ ≤ J and exclude
the surviving rank-one Borel configuration.

All normality is relative to N_G(K₂). The prime-to-five residual below is
formed in the actual relative centralizer and then mapped to G. The
source J₊ is the Q₁-conjugate span of J, not the join J ⊔ Q₁.
Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
variable {G : Type*} [Group G] [Finite G]

/-- The precise output of the C.2.6 extraction before the two terminal
model comparisons. The constructor must discharge every field. -/
structure EscapingComponent (Mc Kz K1 K2 Q1 : Subgroup G) where
  J : Subgroup G
  component_le : J ≤ normalizer (K2 : Set G)
  component : (J.subgroupOf (normalizer (K2 : Set G))).IsCComponent
  quasisimple : IsQuasisimple (J ⧸ pCore 2 J)
  characteristic_normalizer : generalizedFitting (normalizer (K2 : Set G)) =
    pCore 2 (normalizer (K2 : Set G))
  characteristic_component : generalizedFitting J = pCore 2 J
  outside : ¬ J ≤ Mc ⊓ normalizer (K2 : Set G)
  normalized_by_closure : Kz ≤ normalizer (J : Set G)
  generated_commutator : J = ⁅J,K1⁆
  second_commutator : ⁅J,K2⁆ ≤ J.pCoreIn 2
  quintic_rank : primeRank 5 J ≤ 1
  rank_one_identification : primeRank 5 J = 1 →
    J = (primeToResidual 5
      (normalizer (K2 : Set G) ⊓ centralizer (K2 : Set G) : Subgroup G)).map
        (normalizer (K2 : Set G) ⊓ centralizer (K2 : Set G)).subtype ∧
      (J.subgroupOf (normalizer (K2 : Set G))).Normal
  intersection_normalizes_first :
    conjugateSpanBy J Q1 ⊓ (Mc ⊓ normalizer (K2 : Set G)) ≤ normalizer (K1 : Set G)
  pushingUp_alternative : Chapter1.IsSylowIn 2 (Q1 ⊓ J) J ∨
    Q1 ≤ normalizer (J : Set G)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
