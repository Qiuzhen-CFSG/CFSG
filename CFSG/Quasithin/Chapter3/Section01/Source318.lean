module

public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.GroupTheory.PResidual.Defs
public import CFSG.Quasithin.Defs

/-!
# The original ratio assertion of Theorem 3.1.8(1)

This is the universal earlier-source implication, with the original local
subgroup, reduced module, full Sylow centralizer, and unique maximal two-local
hypotheses. Its representation is the literal quotient by the module's
centralizer. The general qrc source producer owns this implication; the
3.2.13 application constructs all its hypotheses for the actual Xi module.

Source: Aschbacher–Smith, Theorem 3.1.8(1), printed p.576.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u

/-- The genuine earlier 3.1.8(1) assertion, for the fixed original ambient group. -/
def SourceTheorem318One (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L M : Subgroup G),
    IsPPerfect 2 L → L ≤ M → (L.subgroupOf M).Normal →
    IsMaximalTwoLocal M → L ⊔ (T : Subgroup G) ≤ M →
    (∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M) →
    ∀ (V : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G)) (hV : IsPReduced 2 V),
      (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
        centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G)) = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) →
      letI := hV.normal
      letI := hV.elementary
      cubicRatio (Representation.NormalElementaryQuotient.representation V
        (QuotientGroup.mk' (centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G))))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2

end CFSG.Quasithin.Chapter3
