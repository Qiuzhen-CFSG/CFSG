module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveMixedCanonicalEdge
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableA5Exclusion

/-!
# Excluding the original symmetric-five wreath H-star quotient

The original chosen small source produces a faithful D₁₀-or-Sz(2) / A₅
F.1.1 pair at critical distance one. The directed local analysis excludes
that pair, closing the wreath-five H-star branch with its original source
hypotheses. No small-parabolic recognition callback remains.
Source: Aschbacher--Smith 15.2.4--8, printed pp.1106--1110;
DGS, *Groups and Graphs* (1985), (11.4)--(11.8), pp.171--176.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChapterF.Source.DGS85
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original chosen small-source configuration has no symmetric-five
wreath H-star quotient. The faithful mixed-pair exclusion is unconditional. -/
theorem ChosenSmallSource.HStar_not_wreath_five
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) := by
  intro he
  let := h.prepared.elementary
  obtain ⟨A,hA,hfin,L,S,_,hF,_,hq,ha⟩ :=
    source_HStar_wreath_five_faithful_mixed_pair h.ambient T h.empty h.maximal
      h.centralizing h.partner h.many h.prepared h.small hH he
  let := hA
  let := hfin
  exact Assembly.small_solvable_a5_exclusion hF hq ha

end CFSG.Quasithin.Chapter15.Section02
