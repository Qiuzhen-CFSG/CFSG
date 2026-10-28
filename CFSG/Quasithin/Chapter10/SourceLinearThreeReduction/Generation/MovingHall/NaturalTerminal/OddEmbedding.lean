module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CenterQuotient
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.NaturalBlock

/-!
# The actual central quotient's odd-degree embedding row

The common overcomponent is quasisimple. Its full central quotient is simple,
so the unique C-component containing the original natural block is the whole
quotient. The block retains its full elementary two-core, trivial center,
properness and perfectness under this literal quotient map. The odd-degree
natural-block reduction therefore eliminates all A.3.12 alternatives except
the maximal rank-two parabolic row.

The genuine A.3.12 embedding and identification of the surviving rank-two
model remain with qt-d-10-nona5-moving-hall-three. This result does not replace
those obligations with a group-family tag or assert triviality of the actual
two-core before projective recognition.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 10.2.3(4), p.747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open ChapterC ChapterA.Section03 Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem CommonOvercomponent.center_quotient_rank_two
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)))
    (hrows : A312Conclusion ((c.original.subgroupOf c.overcomponent).map
      (QuotientGroup.mk' (center c.overcomponent)))) :
    let Q := c.overcomponent ⧸ center c.overcomponent
    let J := (c.original.subgroupOf c.overcomponent).map
      (QuotientGroup.mk' (center c.overcomponent))
    RankTwoTheoremC (⊤ : Subgroup Q) ∧ IsParabolicResidual J ⊤ true := by
  let C := c.overcomponent
  let Q := C ⧸ center C
  let J := (c.original.subgroupOf C).map (QuotientGroup.mk' (center C))
  let : IsQuasisimple C := c.quasisimple hi
  let : IsSimpleGroup Q := IsQuasisimple.simple
  let : IsSimpleGroup (⊤ : Subgroup Q) := (topEquiv (G := Q)).isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup Q) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := Q)).symm.toMonoidHom) (topEquiv (G := Q)).symm.surjective
  let : IsQuasisimple (⊤ : Subgroup Q) :=
    Chapter1.RadicalNormalizers.Embedding.Alternatives.quasisimple_of_perfect_simple
  obtain ⟨hJ,hz,hc,_,_,_,_,hnt,S,hlocal,_⟩ := c.center_quotient_pair hi
  let : Group.IsPerfect (J.subgroupOf (J ⊔ (S : Subgroup Q))) := hlocal.perfect
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show J ≤ J ⊔ (S : Subgroup Q) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have ht : (⊤ : Subgroup Q).IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect .top
  obtain ⟨K,hK,_,_,he⟩ := hrows
  have heq : K = ⊤ := hK.eq_of_le ht le_top
  rw [heq] at he
  exact ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalBlock.select_rank_two
    J ⊤ hJ hc hz ho (lt_of_le_of_ne le_top hnt) he
end CFSG.Quasithin.Chapter10.MovingHall
