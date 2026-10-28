module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Contracts

/-!
# The two remaining source inputs for nonnormal Hall faithfulness

These propositions are obligations, not asserted source theorems. The opening
argument of 10.2.3(2) first makes the odd Hall kernel centralize a suitable full
module, using 4.4.14 in the non-FF case and 10.1.3 in the FF case. Module selection
may change the seed but keeps the original G, T, L, L₀ and M. The second input
is the nonnormal case of 4.4.3: an elementary odd kernel fixing that module has
its normalizer in M. The exceptional alternatives of 4.4.3 have L normal in M.

The assembly combines these inputs with the proved 4.4.13 and Hall conjugacy.
In particular neither input assumes Hall faithfulness, the later generation
bound, or the survivor/normalization conclusion.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
4.4.1--3, 4.4.13--14 and 10.2.3(2), printed pp.619,623--625,745.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The Hall kernel fixes a full module after permissible seed selection.
This does not claim irreducibility or centralization for an arbitrary fixed seed. -/
def SourceNonnormalHallKernelModuleAt : Prop :=
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
        ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
          B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
            centralizer (E.fullModule : Set G)

/-- Only the nonnormal, non-A₅ instance of 4.4.3 consumed by this assembly.
The normalizer is the ambient N_G(A), and the section uses O₂(L₀). -/
def SourceNonnormalOddKernelNormalizerAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (E : FundamentalSetup KnownSimple.IsKnownSimple T L),
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ (p : ℕ), p.Prime → Odd p → ∀ A : Subgroup G,
      A ≠ ⊥ → IsElementaryAbelian p A →
      A ≤ sectionCentralizer (localOrbit T L) →
      A ≤ centralizer (E.fullModule : Set G) →
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) →
      normalizer (A : Set G) ≤ E.maximalLocal

end CFSG.Quasithin.Chapter10
