module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddModels
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddCover
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.NaturalRankTwoTwisted

/-!
# Odd-degree recognition and the full central cover from the genuine embedding

The literal full central quotient is simple, and the original block remains
proper, centerless, natural and a full-Sylow local component there. The actual
A.3.12 embedding reduces it to the rank-two row. The completed model sieve now
recognizes PSL₃ over the original field, including the triality and Ree
exclusions. The ordinary center bound then kills the full center and actual
two-core of the common overcomponent and supplies its terminal configuration.

The genuine A.3.12 embedding, original natural marking and Hall placement
remain obligations of qt-d-10-nona5-moving-hall-three. The literal source
consumer in MovingHall/Source retains just those premises; no further model
recognition, exceptional exclusion or central-cover premise is imposed.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 10.2.3(4), p.747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open ChapterC ChapterA.Section03 Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Recognize the literal central quotient from its genuine source embedding. -/
theorem CommonOvercomponent.center_quotient_recognition_of_embedding
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)))
    (hrows : A312Conclusion ((c.original.subgroupOf c.overcomponent).map
      (QuotientGroup.mk' (center c.overcomponent)))) :
    ClassicalGroup.IsPSL (c.overcomponent ⧸ center c.overcomponent) 3 (2^n) := by
  let C := c.overcomponent
  let Q := C ⧸ center C
  let : IsQuasisimple C := c.quasisimple hi
  let : IsSimpleGroup Q := IsQuasisimple.simple
  let : IsSimpleGroup (⊤ : Subgroup Q) := (topEquiv (G := Q)).isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup Q) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := Q)).symm.toMonoidHom) (topEquiv (G := Q)).symm.surjective
  have ht : (⊤ : Subgroup Q).IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect .top
  obtain ⟨hJ,hz,hc,_,_,_,_,hp,S,hl,_⟩ := c.center_quotient_pair hi
  exact ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalRankTwo.recognize
    S _ ht hl hp hJ hc hz ho (c.center_quotient_rank_two ho hi hrows).1

/-- The full center and actual two-core vanish before constructing the terminal
configuration. Only the genuine embedding remains as a terminal input. -/
theorem CommonOvercomponent.terminal_of_odd_embedding
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (hn : 1 < n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)))
    (hrows : A312Conclusion ((c.original.subgroupOf c.overcomponent).map
      (QuotientGroup.mk' (center c.overcomponent)))) :
    center c.overcomponent = ⊥ ∧ pCore 2 c.overcomponent = ⊥ ∧
      Nonempty (TerminalConfiguration T L (B.map H.subtype) n) := by
  exact c.terminal_of_odd_center_quotient hn ho hi
    (c.center_quotient_recognition_of_embedding ho hi hrows)

end CFSG.Quasithin.Chapter10.MovingHall
