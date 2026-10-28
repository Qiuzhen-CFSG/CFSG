module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.AlternatingSevenLocals
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.AlternatingSevenExtension
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication

/-!
# Actual ambient and marked local conclusions in row nine

The original O₃′ quotient has trivial two-core. Combining the alternating
extension theorem with the residual nongeneration argument gives the actual
S7 or triple-S7 ambient model and both compatible original vertex markings.
The component alternatives are precisely the alternating-seven branches
of `component_models_of_split_sixteen_refined`; no local recognition input
is retained here.

Source: Aschbacher--Smith F.6.18(9), printed p.310.
-/

public section
universe u
open Subgroup Theory.GroupTheory Theory.GroupTheory.RankTwoAmalgam Equiv
open GLS3.Chapter5.OddCentralCovers
namespace CFSG.Quasithin.ChapterF.SourceAssembly

/-- Row nine on the literal quotient and original generating pair, with the
full compatible amalgam retained up to interchanging its endpoints. -/
theorem source_alternating_seven_row_nine
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H ⧸ pPrimeCore 3 H)
    {G₁ G₂ : Subgroup G} (h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hm : Nonempty (pResidual 2 G ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (pResidual 2 G ≃* TripleSeven)) :
    (Nonempty (G ≃* Perm (Fin 7)) ∨
      Nonempty (Theory.AlternatingSevenExtension.TripleSymmetricExtension G)) ∧
    (let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
     Nonempty (RankTwoAmalgam.Iso α MixedSixteen.standard) ∨
       Nonempty (RankTwoAmalgam.Iso α.reverse MixedSixteen.standard)) := by
  exact ⟨source_alternating_seven_extension_models h hFstar hq eT hm,
    source_alternating_seven_row_nine_amalgam h
      (Noncyclic.twoCore_eq_bot_of_cover e) hFstar hq eT hm⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
