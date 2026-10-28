module

public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.SmallTwoPart
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionQuotientBounds

/-!
# The reduced catalogue on the original opposite-centralizer component

Apply the intrinsic two-part calculation to the actual component quotient
embedded in C_G(w)/⟨w⟩. The original conjugation by z, fixed Sylow subgroup,
and fixed-subgroup order bound all survive. Large Lie parameters, the
G₂(4) cover and the large sporadic rows are excluded; the L₃(4) cover,
alternating, odd and M₁₁/M₁₂ alternatives remain explicit.

This removes those rows from the source recognition problem without adding
any premise to the existing local construction. Final recognition using
both marked local centralizers, and the core-collapse assembly, remain
with qt-e-14322-core-collapse.

Source: Aschbacher--Smith 14.3.22, printed p.999, applying 1.1.5(3),
printed pp.501--503; refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
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
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s



/-- The reduced complete catalogue on an actual source component, with the
original involution action, fixed Sylow subgroup and centralizer marking. -/
theorem source_triple_small_marked_component
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := ResidualFusion.C (tripleProduct d a)
    ∃ (D : Subgroup C) (α : MulAut D) (P : Sylow 2 D),
      IsComponent C D ∧
      (∀ x : D, ((α x : C) : G) = z * (x : G) * z⁻¹) ∧
      Chapter1.SmallTwoPart.SmallModelAction115 D α ∧ orderOf α = 2 ∧
      Nat.card P ∣ 128 ∧ (∀ x : P, α (x : D) = x) ∧
      Nat.card α.fixedSubgroup ∣ 384 ∧ ¬128 ∣ Nat.card (D ⧸ pCore 2 D) := by
  intro C
  obtain ⟨D, α, P, hD, hα, hm, ho, hP, hfix, hfc⟩ :=
    source_triple_marked_component
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hb := source_triple_component_quotient_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
  let := hD.2
  exact ⟨D, α, P, hD, hα, Chapter1.SmallTwoPart.smallModelAction115_of_not_dvd hm hb,
    ho, hP, hfix, hfc, hb⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
