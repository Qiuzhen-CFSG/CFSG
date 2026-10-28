module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.SupplementCyclic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.SupplementSpan

/-!
# The TI and abelian-span clauses for the original cyclic supplement

The marked reflection exclusions discharge the cyclicity premise in the
original supplement-span theorem. All subgroups, conjugate spans, normalizers
and two-cores retain their original ambient group and source hypotheses.
The later three-conjugate fusion argument remains a separate source branch.

Source: Aschbacher–Smith 14.3.22, printed p.998.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

/-- The original supplement span, with cyclicity proved from the source context. -/
theorem source_supplement_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) :
    let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
    let X := supplementSpan D (T : Subgroup G)
    Nat.card D = 4 ∧ IsTISubgroup D ∧ IsMulCommutative X ∧
      rankTwoSeed T M ≤ X ∧
      X ≤ (T : Subgroup G) ⊓ centralizer (rankTwoSeed T M : Set G) ∧
      (T : Subgroup G) ⊓ centralizer (rankTwoSeed T M : Set G) ≤
        (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (∀ a : G, conjSubgroup X a ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2 →
        conjSubgroup X a = X) ∧
      sourceResidual M Mc ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
      normalizer (X : Set G) ≤ M := by
  exact source_supplement_span_of_cyclic
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper
    (source_supplement_cyclic hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
