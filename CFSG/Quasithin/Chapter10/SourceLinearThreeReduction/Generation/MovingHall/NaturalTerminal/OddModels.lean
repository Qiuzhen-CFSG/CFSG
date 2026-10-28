module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddEmbedding
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.NaturalRankTwo

/-!
# Remaining models for the actual odd-degree central quotient

The original block remains a proper, centerless natural block with its full
two-core in the literal central quotient. Its full-Sylow local membership
therefore fixes the field in the linear rank-two family and excludes the
symplectic and G₂ families. Order arguments exclude all three small derived
endpoints. The only remaining alternatives to the desired PSL₃ model are
actual triality and Ree isomorphisms.

The genuine A.3.12 embedding and the exclusion of those last two families
remain with qt-d-10-nona5-moving-hall-three, together with natural-row selection
and placement of the original Hall subgroup. This does not identify the
two-core quotient with the central quotient or assume the central cover splits.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 10.2.3(4), p.747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open ChapterC ChapterA.Section03 Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem CommonOvercomponent.center_quotient_rank_two_models
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)))
    (hRank : RankTwoTheoremC (⊤ : Subgroup (c.overcomponent ⧸ center c.overcomponent))) :
    let Q := c.overcomponent ⧸ center c.overcomponent
    ClassicalGroup.IsPSL Q 3 (2^n) ∨
      (∃ f : ℕ, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2^f) Q) ∨
      (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At Q m) := by
  obtain ⟨hJ,hz,hc,_,_,_,_,hp,S,hl,_⟩ := c.center_quotient_pair hi
  exact ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalRankTwo.rank_two_alternatives
    S _ hl hp hJ hc hz ho hRank

end CFSG.Quasithin.Chapter10.MovingHall
