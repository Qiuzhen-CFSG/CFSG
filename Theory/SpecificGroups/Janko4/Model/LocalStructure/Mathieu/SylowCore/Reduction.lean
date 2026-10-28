module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Counting

/-!
# Reducing max1 Sylow-core characteristicity to a quotient action bound

The literal kernel is normal elementary of order 2048 and lies in every local
Sylow two-subgroup. For a normal elementary subgroup `A` not contained in the
kernel, it suffices to bound `|AE/E| |C_E(A)|` by 1024. The counting argument
then makes the kernel the unique normal elementary subgroup of order 2048,
and hence characteristic. The numerical action bound remains explicit.

Source context: Kleidman–Wilson, *The maximal subgroups of J₄* (1988),
pp.484–510; GLS3 Table 5.3i. All groups here are the actual ATLAS word subgroup
and its certified normal closure, not abstract extension-shape labels.
-/

@[expose] public section

namespace Janko4.LocalStructure
open Subgroup Cardinality

namespace SylowCore

/-- The literal ATLAS max1 subgroup. -/
abbrev Local := max1Subgroup matrixA_mul_self matrixB_pow_four

/-- The certified binary kernel, restricted to a local Sylow subgroup. -/
abbrev core (P : Sylow 2 Local) : Subgroup P :=
  (localKernel matrixA_mul_self matrixB_pow_four).subgroupOf P.toSubgroup

/-- The intrinsic action inequality to be obtained from the finite star calculation. -/
def QuotientCentralizerBound : Prop :=
  ∀ (P : Sylow 2 Local) (A : Subgroup P),
    A.Normal → IsElementaryAbelian 2 A → ¬ A ≤ core P →
      Nat.card (A.map (QuotientGroup.mk' (core P))) *
        Nat.card ((centralizer (A : Set P)).subgroupOf (core P)) ≤ 1024

end SylowCore

attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- Normality and the two-power order put the kernel inside every local Sylow. -/
theorem localKernel_le_sylow (P : Sylow 2 SylowCore.Local) :
    localKernel matrixA_mul_self matrixB_pow_four ≤ P.toSubgroup :=
  (IsPGroup.of_card (n := 11)
    (localKernel_card matrixA_mul_self matrixB_pow_four)).le_sylow_of_normal P

/-- Restriction to a local Sylow preserves the full order of the kernel. -/
theorem localKernel_sylow_card (P : Sylow 2 SylowCore.Local) :
    Nat.card (SylowCore.core P) = 2048 :=
  (Nat.card_congr (subgroupOfEquivOfLe (localKernel_le_sylow P)).toEquiv).trans
    (localKernel_card matrixA_mul_self matrixB_pow_four)

/-- The restricted kernel retains its elementary abelian structure. -/
theorem localKernel_sylow_elementary (P : Sylow 2 SylowCore.Local) :
    IsElementaryAbelian 2 (SylowCore.core P) := by
  have := localKernel_elementary matrixA_mul_self matrixB_pow_four
  exact IsElementaryAbelian.subgroupOf (localKernel_le_sylow P)

/-- The numerical bound implies uniqueness among normal elementary subgroups
of order 2048 (and also rules out any larger such subgroup). -/
theorem localKernel_sylow_unique_of_quotientCentralizerBound
    (hbound : SylowCore.QuotientCentralizerBound) (P : Sylow 2 SylowCore.Local)
    (A : Subgroup P) [A.Normal] [IsElementaryAbelian 2 A]
    (hcard : 2048 ≤ Nat.card A) : A = SylowCore.core P := by
  apply SylowCore.eq_of_card_le_of_image_centralizer_bound
  · intro hn
    rw [localKernel_sylow_card]
    exact lt_of_le_of_lt (hbound P A inferInstance inferInstance hn) (by decide)
  · simpa only [localKernel_sylow_card] using hcard

/-- Conditional assembly: the finite quotient action bound is still required. -/
theorem localKernel_sylow_characteristic_of_quotientCentralizerBound
    (hbound : SylowCore.QuotientCentralizerBound) (P : Sylow 2 SylowCore.Local) :
    ((localKernel matrixA_mul_self matrixB_pow_four).subgroupOf P.toSubgroup).Characteristic := by
  have := localKernel_sylow_elementary P
  apply SylowCore.characteristic_of_image_centralizer_bound (p := 2)
  intro A hA hAe hn
  rw [localKernel_sylow_card]
  exact lt_of_le_of_lt (hbound P A hA hAe hn) (by decide)

end Janko4.LocalStructure
