module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Inputs
public import CFSG.Quasithin.Chapter4.Defs
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import Stellmacher.OmegaOneCenterMap

/-!
# Hall faithfulness and the two order branches of original 10.2.3

These are source obligations, not theorems. They concern an abelian odd
Hall subgroup of the literal H intersect M, permuting with the prescribed T.
The setup may be chosen with minimal full module: M=N_G(L₀) is independent
of this choice. Neither obligation assumes point-centralizer control or the
later survivor or normalization theorem. Faithfulness on L₀/O₂(L₀) is a
common independent input to the two order branches.

When H centralizes Z=Ω₁Z(T), the linear-three row gives a three-group. In the
other surviving row, the Hall group embeds in the centralizer of Z in the
orthogonal torus, whose exponent divides 2ⁿ+1. Its order need not divide
2ⁿ+1: that torus has two factors. When H moves Z, the source eliminates the
even-field natural row by its block argument, leaving the linear-three row.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
10.2.3(1--4), printed pp.745--747, using 10.1.1--2 and 10.2.1--2.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- Original 10.2.3(2), specialized to the actual non-A₅ Hall actor needed
by the numerical consumer. The kernel uses O₂(L₀), not O²(L₀). -/
def SourceNonnormalHallFaithfulAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      1 < generationParameter H →
      ∀ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H →
        IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) →
        IsMulCommutative B →
        (B.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (B.map H.subtype : Set G) →
        B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥

/-- The centralizing-Z branch retains the exponent of the actual full Hall
subgroup, rather than an order bound on an unrelated model or quotient. -/
def SourceNonnormalCentralHallAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      1 < generationParameter H →
      ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), H⁆ = ⊥ →
      ∀ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H →
        IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) →
        IsMulCommutative B →
        (B.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (B.map H.subtype : Set G) →
        B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥ →
        IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2 ^ n + 1

/-- The moving-Z branch includes the elimination of the natural even-field
row on pp.746--747. A three-group conclusion cannot be inferred from the
abstract nonnormal component model list alone. -/
def SourceNonnormalMovingHallAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      1 < generationParameter H →
      ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥ →
      ∀ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H →
        IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) →
        IsMulCommutative B →
        (B.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (B.map H.subtype : Set G) →
        B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥ →
        IsPGroup 3 B

end CFSG.Quasithin.Chapter10
