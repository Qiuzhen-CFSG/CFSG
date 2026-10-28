module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.RankOneChi
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.AlternatingFive
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.BinaryThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ModelPruning
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ComponentInputs
/-!
# The full exchanged source case from the actual B.5 rows

The proved intrinsic model restriction prunes the complete B.5 conclusion
on the original omega-core module. Its rank-one row constructs a χ-block
and reaches the source Borel endgame. Its A₅ and binary SL₃ rows contradict
the original seed's Sylow centralizer by explicit cubic fixed-space witnesses.
The complete component input is constructed from the actual exchanged
embedding branch, so no C.2.7 or C.1.34 classification is supplied.
Source: Aschbacher–Smith 15.4.20, printed p.1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {K₁ : Subgroup G} {r : G}

theorem source_selected_sieve_contradiction
    (c₀ : BlockEndgame.ContraryData KnownSimple.IsKnownSimple d i j)
    (h : Input d i j c₀.H c₀.U c₀.K) (s : Selected c₀.H c₀.U c₀.K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple c₀.H ((sourceRadical d c₀.U).subgroupOf c₀.H)
      (d.M₁.subgroupOf c₀.H) (K₁.subgroupOf c₀.H)) : False := by
  obtain ⟨_,c,hcases⟩ := source_selected_ff_pruned_classification h s hc
  cases hcases with
  | irreducible hi hf hirr hrow he =>
    cases hrow with
    | linearTwo F _ e ho hr => exact source_rankOne_row_contradiction c₀ h s hc c hi F e hr ho
    | linearThree F hF _ e _ => exact source_binaryThree_row_contradiction h s hc.normalized c F hF e
    | symmetricFive e _ _ => exact source_symmetricFive_row_contradiction h s hc.normalized c e
  | doubleThree F hF _ e _ _ => exact source_doubleThree_row_contradiction h s hc.normalized c F hF e

theorem source_exchanged_case_contradiction
    (c : BlockEndgame.ContraryData KnownSimple.IsKnownSimple d i j)
    (h : Input d i j c.H c.U c.K) (P : Sylow 3 d.wholeX)
    (branch : EmbeddingReduction.ExchangedCase c.H c.U
      ((P : Subgroup d.wholeX).map d.wholeX.subtype) c.K) : False := by
  obtain ⟨L,r,s,hc⟩ := exchanged_selected_hypotheses c.ambient h c.unique_X P branch
  exact source_selected_sieve_contradiction c h s hc
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
