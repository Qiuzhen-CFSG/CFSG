module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges10

/-!
# The 693-coset cover of the fixed max2 presentation

The fixed words and transitions replay `source/special_scan.json`.
Tree edges are word extensions; 17 special edges have subgroup tails and
relations derived from the 29 published relators. Every remaining edge is
obtained by cancelling known paths in an original relator loop.
The untrusted producer uses GAP only to discover this finite witness.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000

theorem edge704 : Holds level0Subgroup PresentedGroup.of representative ⟨268, [(true, false)], 296⟩ :=
  special 268 296 (true, false) [(6, true), (4, true), (2, true), (2, true), (0, true), (6, true)] LiftedRelations.word93
    false 116 (by decide +kernel) LiftedRelations.valid93

theorem edge704Inv : Holds level0Subgroup PresentedGroup.of representative ⟨296, [(true, true)], 268⟩ :=
  holds_reverse edge704

theorem edge705 : Holds level0Subgroup PresentedGroup.of representative ⟨276, [(true, false)], 295⟩ :=
  special 276 295 (true, false) [(4, true), (4, true), (0, true), (2, false), (2, false), (0, false), (6, true)] LiftedRelations.word78
    true 99 (by decide +kernel) LiftedRelations.valid78

theorem edge705Inv : Holds level0Subgroup PresentedGroup.of representative ⟨295, [(true, true)], 276⟩ :=
  holds_reverse edge705

theorem edge706 : Holds level0Subgroup PresentedGroup.of representative ⟨281, [(true, true)], 305⟩ :=
  special 281 305 (true, true) [(5, false), (2, true), (2, true), (0, true), (4, false)] LiftedRelations.word54
    false 124 (by decide +kernel) LiftedRelations.valid54

theorem edge706Inv : Holds level0Subgroup PresentedGroup.of representative ⟨305, [(true, false)], 281⟩ :=
  holds_reverse edge706

theorem edge707 : Holds level0Subgroup PresentedGroup.of representative ⟨283, [(true, false)], 294⟩ :=
  special 283 294 (true, false) [(0, false), (4, true), (4, true), (5, true), (6, true)] LiftedRelations.word96
    false 51 (by decide +kernel) LiftedRelations.valid96

theorem edge707Inv : Holds level0Subgroup PresentedGroup.of representative ⟨294, [(true, true)], 283⟩ :=
  holds_reverse edge707

theorem edge708 : Holds level0Subgroup PresentedGroup.of representative ⟨287, [(true, false)], 334⟩ :=
  special 287 334 (true, false) [(6, false), (5, false), (3, false), (2, true), (4, true)] LiftedRelations.word97
    false 273 (by decide +kernel) LiftedRelations.valid97

theorem edge708Inv : Holds level0Subgroup PresentedGroup.of representative ⟨334, [(true, true)], 287⟩ :=
  holds_reverse edge708

theorem edge709 : Holds level0Subgroup PresentedGroup.of representative ⟨1, [(false, true)], 0⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨0, [(false, true)], 1⟩ :=
    edge0
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨0, [], 0⟩ :=
    (holds_refl 0)
  exact scanFacts hp hs (holds_relator 0 (level0Relator 0) (level0_relator 0))

theorem edge709Inv : Holds level0Subgroup PresentedGroup.of representative ⟨0, [(false, false)], 1⟩ :=
  holds_reverse edge709

theorem edge710 : Holds level0Subgroup PresentedGroup.of representative ⟨2, [(true, true)], 3⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨1, [(true, true)], 2⟩ :=
    edge1
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨3, [(true, true)], 1⟩ :=
    edge2Inv
  exact scanFacts hp hs (holds_relator 1 (level0Relator 1) (level0_relator 1))

theorem edge710Inv : Holds level0Subgroup PresentedGroup.of representative ⟨3, [(true, false)], 2⟩ :=
  holds_reverse edge710

theorem edge711 : Holds level0Subgroup PresentedGroup.of representative ⟨4, [(false, true)], 2⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨2, [(false, true)], 4⟩ :=
    edge3
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨2, [], 2⟩ :=
    (holds_refl 2)
  exact scanFacts hp hs (holds_relator 2 (level0Relator 0) (level0_relator 0))

theorem edge711Inv : Holds level0Subgroup PresentedGroup.of representative ⟨2, [(false, false)], 4⟩ :=
  holds_reverse edge711

theorem edge712 : Holds level0Subgroup PresentedGroup.of representative ⟨5, [(false, true)], 3⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨3, [(false, true)], 5⟩ :=
    edge4
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨3, [], 3⟩ :=
    (holds_refl 3)
  exact scanFacts hp hs (holds_relator 3 (level0Relator 0) (level0_relator 0))

theorem edge712Inv : Holds level0Subgroup PresentedGroup.of representative ⟨3, [(false, false)], 5⟩ :=
  holds_reverse edge712

theorem edge713 : Holds level0Subgroup PresentedGroup.of representative ⟨6, [(true, true)], 7⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨4, [(true, true)], 6⟩ :=
    edge5
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨7, [(true, true)], 4⟩ :=
    edge6Inv
  exact scanFacts hp hs (holds_relator 4 (level0Relator 1) (level0_relator 1))

theorem edge713Inv : Holds level0Subgroup PresentedGroup.of representative ⟨7, [(true, false)], 6⟩ :=
  holds_reverse edge713

theorem edge714 : Holds level0Subgroup PresentedGroup.of representative ⟨8, [(true, true)], 9⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨5, [(true, true)], 8⟩ :=
    edge7
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨9, [(true, true)], 5⟩ :=
    edge8Inv
  exact scanFacts hp hs (holds_relator 5 (level0Relator 1) (level0_relator 1))

theorem edge714Inv : Holds level0Subgroup PresentedGroup.of representative ⟨9, [(true, false)], 8⟩ :=
  holds_reverse edge714

theorem edge715 : Holds level0Subgroup PresentedGroup.of representative ⟨10, [(false, true)], 6⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨6, [(false, true)], 10⟩ :=
    edge9
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨6, [], 6⟩ :=
    (holds_refl 6)
  exact scanFacts hp hs (holds_relator 6 (level0Relator 0) (level0_relator 0))

theorem edge715Inv : Holds level0Subgroup PresentedGroup.of representative ⟨6, [(false, false)], 10⟩ :=
  holds_reverse edge715

theorem edge716 : Holds level0Subgroup PresentedGroup.of representative ⟨11, [(false, true)], 7⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨7, [(false, true)], 11⟩ :=
    edge10
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨7, [], 7⟩ :=
    (holds_refl 7)
  exact scanFacts hp hs (holds_relator 7 (level0Relator 0) (level0_relator 0))

theorem edge716Inv : Holds level0Subgroup PresentedGroup.of representative ⟨7, [(false, false)], 11⟩ :=
  holds_reverse edge716

theorem edge717 : Holds level0Subgroup PresentedGroup.of representative ⟨12, [(false, true)], 8⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨8, [(false, true)], 12⟩ :=
    edge11
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨8, [], 8⟩ :=
    (holds_refl 8)
  exact scanFacts hp hs (holds_relator 8 (level0Relator 0) (level0_relator 0))

theorem edge717Inv : Holds level0Subgroup PresentedGroup.of representative ⟨8, [(false, false)], 12⟩ :=
  holds_reverse edge717

theorem edge718 : Holds level0Subgroup PresentedGroup.of representative ⟨13, [(false, true)], 9⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨9, [(false, true)], 13⟩ :=
    edge12
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨9, [], 9⟩ :=
    (holds_refl 9)
  exact scanFacts hp hs (holds_relator 9 (level0Relator 0) (level0_relator 0))

theorem edge718Inv : Holds level0Subgroup PresentedGroup.of representative ⟨9, [(false, false)], 13⟩ :=
  holds_reverse edge718

theorem edge719 : Holds level0Subgroup PresentedGroup.of representative ⟨14, [(true, true)], 15⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨10, [(true, true)], 14⟩ :=
    edge13
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨15, [(true, true)], 10⟩ :=
    edge14Inv
  exact scanFacts hp hs (holds_relator 10 (level0Relator 1) (level0_relator 1))

theorem edge719Inv : Holds level0Subgroup PresentedGroup.of representative ⟨15, [(true, false)], 14⟩ :=
  holds_reverse edge719

theorem edge720 : Holds level0Subgroup PresentedGroup.of representative ⟨16, [(true, true)], 17⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨11, [(true, true)], 16⟩ :=
    edge15
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨17, [(true, true)], 11⟩ :=
    edge16Inv
  exact scanFacts hp hs (holds_relator 11 (level0Relator 1) (level0_relator 1))

theorem edge720Inv : Holds level0Subgroup PresentedGroup.of representative ⟨17, [(true, false)], 16⟩ :=
  holds_reverse edge720

theorem edge721 : Holds level0Subgroup PresentedGroup.of representative ⟨18, [(true, true)], 19⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨12, [(true, true)], 18⟩ :=
    edge17
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨19, [(true, true)], 12⟩ :=
    edge18Inv
  exact scanFacts hp hs (holds_relator 12 (level0Relator 1) (level0_relator 1))

theorem edge721Inv : Holds level0Subgroup PresentedGroup.of representative ⟨19, [(true, false)], 18⟩ :=
  holds_reverse edge721

theorem edge722 : Holds level0Subgroup PresentedGroup.of representative ⟨20, [(true, true)], 21⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨13, [(true, true)], 20⟩ :=
    edge19
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨21, [(true, true)], 13⟩ :=
    edge20Inv
  exact scanFacts hp hs (holds_relator 13 (level0Relator 1) (level0_relator 1))

theorem edge722Inv : Holds level0Subgroup PresentedGroup.of representative ⟨21, [(true, false)], 20⟩ :=
  holds_reverse edge722

theorem edge723 : Holds level0Subgroup PresentedGroup.of representative ⟨21, [(false, true)], 14⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨14, [(false, true)], 21⟩ :=
    edge693
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨14, [], 14⟩ :=
    (holds_refl 14)
  exact scanFacts hp hs (holds_relator 14 (level0Relator 0) (level0_relator 0))

theorem edge723Inv : Holds level0Subgroup PresentedGroup.of representative ⟨14, [(false, false)], 21⟩ :=
  holds_reverse edge723

theorem edge724 : Holds level0Subgroup PresentedGroup.of representative ⟨22, [(false, true)], 15⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨15, [(false, true)], 22⟩ :=
    edge21
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨15, [], 15⟩ :=
    (holds_refl 15)
  exact scanFacts hp hs (holds_relator 15 (level0Relator 0) (level0_relator 0))

theorem edge724Inv : Holds level0Subgroup PresentedGroup.of representative ⟨15, [(false, false)], 22⟩ :=
  holds_reverse edge724

theorem edge725 : Holds level0Subgroup PresentedGroup.of representative ⟨23, [(false, true)], 16⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨16, [(false, true)], 23⟩ :=
    edge22
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨16, [], 16⟩ :=
    (holds_refl 16)
  exact scanFacts hp hs (holds_relator 16 (level0Relator 0) (level0_relator 0))

theorem edge725Inv : Holds level0Subgroup PresentedGroup.of representative ⟨16, [(false, false)], 23⟩ :=
  holds_reverse edge725

theorem edge726 : Holds level0Subgroup PresentedGroup.of representative ⟨24, [(false, true)], 17⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨17, [(false, true)], 24⟩ :=
    edge23
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨17, [], 17⟩ :=
    (holds_refl 17)
  exact scanFacts hp hs (holds_relator 17 (level0Relator 0) (level0_relator 0))

theorem edge726Inv : Holds level0Subgroup PresentedGroup.of representative ⟨17, [(false, false)], 24⟩ :=
  holds_reverse edge726

theorem edge727 : Holds level0Subgroup PresentedGroup.of representative ⟨25, [(false, true)], 18⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨18, [(false, true)], 25⟩ :=
    edge24
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨18, [], 18⟩ :=
    (holds_refl 18)
  exact scanFacts hp hs (holds_relator 18 (level0Relator 0) (level0_relator 0))

theorem edge727Inv : Holds level0Subgroup PresentedGroup.of representative ⟨18, [(false, false)], 25⟩ :=
  holds_reverse edge727

theorem edge728 : Holds level0Subgroup PresentedGroup.of representative ⟨26, [(false, true)], 19⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨19, [(false, true)], 26⟩ :=
    edge25
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨19, [], 19⟩ :=
    (holds_refl 19)
  exact scanFacts hp hs (holds_relator 19 (level0Relator 0) (level0_relator 0))

theorem edge728Inv : Holds level0Subgroup PresentedGroup.of representative ⟨19, [(false, false)], 26⟩ :=
  holds_reverse edge728

theorem edge729 : Holds level0Subgroup PresentedGroup.of representative ⟨27, [(false, true)], 20⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨20, [(false, true)], 27⟩ :=
    edge26
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨20, [], 20⟩ :=
    (holds_refl 20)
  exact scanFacts hp hs (holds_relator 20 (level0Relator 0) (level0_relator 0))

theorem edge729Inv : Holds level0Subgroup PresentedGroup.of representative ⟨20, [(false, false)], 27⟩ :=
  holds_reverse edge729

theorem edge730 : Holds level0Subgroup PresentedGroup.of representative ⟨28, [(true, true)], 29⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨22, [(true, true)], 28⟩ :=
    edge27
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨29, [(true, true)], 22⟩ :=
    edge28Inv
  exact scanFacts hp hs (holds_relator 22 (level0Relator 1) (level0_relator 1))

theorem edge730Inv : Holds level0Subgroup PresentedGroup.of representative ⟨29, [(true, false)], 28⟩ :=
  holds_reverse edge730

theorem edge731 : Holds level0Subgroup PresentedGroup.of representative ⟨30, [(true, true)], 31⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨23, [(true, true)], 30⟩ :=
    edge29
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨31, [(true, true)], 23⟩ :=
    edge30Inv
  exact scanFacts hp hs (holds_relator 23 (level0Relator 1) (level0_relator 1))

theorem edge731Inv : Holds level0Subgroup PresentedGroup.of representative ⟨31, [(true, false)], 30⟩ :=
  holds_reverse edge731

theorem edge732 : Holds level0Subgroup PresentedGroup.of representative ⟨32, [(true, true)], 33⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨24, [(true, true)], 32⟩ :=
    edge31
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨33, [(true, true)], 24⟩ :=
    edge32Inv
  exact scanFacts hp hs (holds_relator 24 (level0Relator 1) (level0_relator 1))

theorem edge732Inv : Holds level0Subgroup PresentedGroup.of representative ⟨33, [(true, false)], 32⟩ :=
  holds_reverse edge732

theorem edge733 : Holds level0Subgroup PresentedGroup.of representative ⟨34, [(true, true)], 35⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨25, [(true, true)], 34⟩ :=
    edge33
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨35, [(true, true)], 25⟩ :=
    edge34Inv
  exact scanFacts hp hs (holds_relator 25 (level0Relator 1) (level0_relator 1))

theorem edge733Inv : Holds level0Subgroup PresentedGroup.of representative ⟨35, [(true, false)], 34⟩ :=
  holds_reverse edge733

theorem edge734 : Holds level0Subgroup PresentedGroup.of representative ⟨36, [(true, true)], 37⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨26, [(true, true)], 36⟩ :=
    edge35
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨37, [(true, true)], 26⟩ :=
    edge36Inv
  exact scanFacts hp hs (holds_relator 26 (level0Relator 1) (level0_relator 1))

theorem edge734Inv : Holds level0Subgroup PresentedGroup.of representative ⟨37, [(true, false)], 36⟩ :=
  holds_reverse edge734

theorem edge735 : Holds level0Subgroup PresentedGroup.of representative ⟨38, [(true, true)], 39⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨27, [(true, true)], 38⟩ :=
    edge37
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨39, [(true, true)], 27⟩ :=
    edge38Inv
  exact scanFacts hp hs (holds_relator 27 (level0Relator 1) (level0_relator 1))

theorem edge735Inv : Holds level0Subgroup PresentedGroup.of representative ⟨39, [(true, false)], 38⟩ :=
  holds_reverse edge735

theorem edge736 : Holds level0Subgroup PresentedGroup.of representative ⟨40, [(false, true)], 28⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨28, [(false, true)], 40⟩ :=
    edge39
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨28, [], 28⟩ :=
    (holds_refl 28)
  exact scanFacts hp hs (holds_relator 28 (level0Relator 0) (level0_relator 0))

theorem edge736Inv : Holds level0Subgroup PresentedGroup.of representative ⟨28, [(false, false)], 40⟩ :=
  holds_reverse edge736

theorem edge737 : Holds level0Subgroup PresentedGroup.of representative ⟨41, [(false, true)], 29⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨29, [(false, true)], 41⟩ :=
    edge40
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨29, [], 29⟩ :=
    (holds_refl 29)
  exact scanFacts hp hs (holds_relator 29 (level0Relator 0) (level0_relator 0))

theorem edge737Inv : Holds level0Subgroup PresentedGroup.of representative ⟨29, [(false, false)], 41⟩ :=
  holds_reverse edge737

theorem edge738 : Holds level0Subgroup PresentedGroup.of representative ⟨42, [(false, true)], 30⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨30, [(false, true)], 42⟩ :=
    edge41
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨30, [], 30⟩ :=
    (holds_refl 30)
  exact scanFacts hp hs (holds_relator 30 (level0Relator 0) (level0_relator 0))

theorem edge738Inv : Holds level0Subgroup PresentedGroup.of representative ⟨30, [(false, false)], 42⟩ :=
  holds_reverse edge738

theorem edge739 : Holds level0Subgroup PresentedGroup.of representative ⟨43, [(false, true)], 31⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨31, [(false, true)], 43⟩ :=
    edge42
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨31, [], 31⟩ :=
    (holds_refl 31)
  exact scanFacts hp hs (holds_relator 31 (level0Relator 0) (level0_relator 0))

theorem edge739Inv : Holds level0Subgroup PresentedGroup.of representative ⟨31, [(false, false)], 43⟩ :=
  holds_reverse edge739

theorem edge740 : Holds level0Subgroup PresentedGroup.of representative ⟨44, [(false, true)], 32⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨32, [(false, true)], 44⟩ :=
    edge43
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨32, [], 32⟩ :=
    (holds_refl 32)
  exact scanFacts hp hs (holds_relator 32 (level0Relator 0) (level0_relator 0))

theorem edge740Inv : Holds level0Subgroup PresentedGroup.of representative ⟨32, [(false, false)], 44⟩ :=
  holds_reverse edge740

theorem edge741 : Holds level0Subgroup PresentedGroup.of representative ⟨45, [(false, true)], 33⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨33, [(false, true)], 45⟩ :=
    edge44
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨33, [], 33⟩ :=
    (holds_refl 33)
  exact scanFacts hp hs (holds_relator 33 (level0Relator 0) (level0_relator 0))

theorem edge741Inv : Holds level0Subgroup PresentedGroup.of representative ⟨33, [(false, false)], 45⟩ :=
  holds_reverse edge741

theorem edge742 : Holds level0Subgroup PresentedGroup.of representative ⟨46, [(false, true)], 34⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨34, [(false, true)], 46⟩ :=
    edge45
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨34, [], 34⟩ :=
    (holds_refl 34)
  exact scanFacts hp hs (holds_relator 34 (level0Relator 0) (level0_relator 0))

theorem edge742Inv : Holds level0Subgroup PresentedGroup.of representative ⟨34, [(false, false)], 46⟩ :=
  holds_reverse edge742

theorem edge743 : Holds level0Subgroup PresentedGroup.of representative ⟨47, [(false, true)], 35⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨35, [(false, true)], 47⟩ :=
    edge46
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨35, [], 35⟩ :=
    (holds_refl 35)
  exact scanFacts hp hs (holds_relator 35 (level0Relator 0) (level0_relator 0))

theorem edge743Inv : Holds level0Subgroup PresentedGroup.of representative ⟨35, [(false, false)], 47⟩ :=
  holds_reverse edge743

theorem edge744 : Holds level0Subgroup PresentedGroup.of representative ⟨48, [(false, true)], 36⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨36, [(false, true)], 48⟩ :=
    edge47
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨36, [], 36⟩ :=
    (holds_refl 36)
  exact scanFacts hp hs (holds_relator 36 (level0Relator 0) (level0_relator 0))

theorem edge744Inv : Holds level0Subgroup PresentedGroup.of representative ⟨36, [(false, false)], 48⟩ :=
  holds_reverse edge744

theorem edge745 : Holds level0Subgroup PresentedGroup.of representative ⟨49, [(false, true)], 37⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨37, [(false, true)], 49⟩ :=
    edge48
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨37, [], 37⟩ :=
    (holds_refl 37)
  exact scanFacts hp hs (holds_relator 37 (level0Relator 0) (level0_relator 0))

theorem edge745Inv : Holds level0Subgroup PresentedGroup.of representative ⟨37, [(false, false)], 49⟩ :=
  holds_reverse edge745

theorem edge746 : Holds level0Subgroup PresentedGroup.of representative ⟨50, [(false, true)], 38⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨38, [(false, true)], 50⟩ :=
    edge49
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨38, [], 38⟩ :=
    (holds_refl 38)
  exact scanFacts hp hs (holds_relator 38 (level0Relator 0) (level0_relator 0))

theorem edge746Inv : Holds level0Subgroup PresentedGroup.of representative ⟨38, [(false, false)], 50⟩ :=
  holds_reverse edge746

theorem edge747 : Holds level0Subgroup PresentedGroup.of representative ⟨51, [(false, true)], 39⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨39, [(false, true)], 51⟩ :=
    edge50
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨39, [], 39⟩ :=
    (holds_refl 39)
  exact scanFacts hp hs (holds_relator 39 (level0Relator 0) (level0_relator 0))

theorem edge747Inv : Holds level0Subgroup PresentedGroup.of representative ⟨39, [(false, false)], 51⟩ :=
  holds_reverse edge747

theorem edge748 : Holds level0Subgroup PresentedGroup.of representative ⟨52, [(true, true)], 53⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨40, [(true, true)], 52⟩ :=
    edge51
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨53, [(true, true)], 40⟩ :=
    edge52Inv
  exact scanFacts hp hs (holds_relator 40 (level0Relator 1) (level0_relator 1))

theorem edge748Inv : Holds level0Subgroup PresentedGroup.of representative ⟨53, [(true, false)], 52⟩ :=
  holds_reverse edge748

theorem edge749 : Holds level0Subgroup PresentedGroup.of representative ⟨54, [(true, true)], 55⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨41, [(true, true)], 54⟩ :=
    edge53
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨55, [(true, true)], 41⟩ :=
    edge54Inv
  exact scanFacts hp hs (holds_relator 41 (level0Relator 1) (level0_relator 1))

theorem edge749Inv : Holds level0Subgroup PresentedGroup.of representative ⟨55, [(true, false)], 54⟩ :=
  holds_reverse edge749

theorem edge750 : Holds level0Subgroup PresentedGroup.of representative ⟨56, [(true, true)], 57⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨42, [(true, true)], 56⟩ :=
    edge55
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨57, [(true, true)], 42⟩ :=
    edge56Inv
  exact scanFacts hp hs (holds_relator 42 (level0Relator 1) (level0_relator 1))

theorem edge750Inv : Holds level0Subgroup PresentedGroup.of representative ⟨57, [(true, false)], 56⟩ :=
  holds_reverse edge750

theorem edge751 : Holds level0Subgroup PresentedGroup.of representative ⟨58, [(true, true)], 59⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨43, [(true, true)], 58⟩ :=
    edge57
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨59, [(true, true)], 43⟩ :=
    edge58Inv
  exact scanFacts hp hs (holds_relator 43 (level0Relator 1) (level0_relator 1))

theorem edge751Inv : Holds level0Subgroup PresentedGroup.of representative ⟨59, [(true, false)], 58⟩ :=
  holds_reverse edge751

theorem edge752 : Holds level0Subgroup PresentedGroup.of representative ⟨60, [(true, true)], 61⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨44, [(true, true)], 60⟩ :=
    edge59
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨61, [(true, true)], 44⟩ :=
    edge60Inv
  exact scanFacts hp hs (holds_relator 44 (level0Relator 1) (level0_relator 1))

theorem edge752Inv : Holds level0Subgroup PresentedGroup.of representative ⟨61, [(true, false)], 60⟩ :=
  holds_reverse edge752

theorem edge753 : Holds level0Subgroup PresentedGroup.of representative ⟨62, [(true, true)], 63⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨45, [(true, true)], 62⟩ :=
    edge61
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨63, [(true, true)], 45⟩ :=
    edge62Inv
  exact scanFacts hp hs (holds_relator 45 (level0Relator 1) (level0_relator 1))

theorem edge753Inv : Holds level0Subgroup PresentedGroup.of representative ⟨63, [(true, false)], 62⟩ :=
  holds_reverse edge753

theorem edge754 : Holds level0Subgroup PresentedGroup.of representative ⟨64, [(true, true)], 65⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨46, [(true, true)], 64⟩ :=
    edge63
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨65, [(true, true)], 46⟩ :=
    edge64Inv
  exact scanFacts hp hs (holds_relator 46 (level0Relator 1) (level0_relator 1))

theorem edge754Inv : Holds level0Subgroup PresentedGroup.of representative ⟨65, [(true, false)], 64⟩ :=
  holds_reverse edge754

theorem edge755 : Holds level0Subgroup PresentedGroup.of representative ⟨66, [(true, true)], 67⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨47, [(true, true)], 66⟩ :=
    edge65
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨67, [(true, true)], 47⟩ :=
    edge66Inv
  exact scanFacts hp hs (holds_relator 47 (level0Relator 1) (level0_relator 1))

theorem edge755Inv : Holds level0Subgroup PresentedGroup.of representative ⟨67, [(true, false)], 66⟩ :=
  holds_reverse edge755

theorem edge756 : Holds level0Subgroup PresentedGroup.of representative ⟨68, [(true, true)], 69⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨48, [(true, true)], 68⟩ :=
    edge67
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨69, [(true, true)], 48⟩ :=
    edge68Inv
  exact scanFacts hp hs (holds_relator 48 (level0Relator 1) (level0_relator 1))

theorem edge756Inv : Holds level0Subgroup PresentedGroup.of representative ⟨69, [(true, false)], 68⟩ :=
  holds_reverse edge756

theorem edge757 : Holds level0Subgroup PresentedGroup.of representative ⟨70, [(true, true)], 71⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨49, [(true, true)], 70⟩ :=
    edge69
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨71, [(true, true)], 49⟩ :=
    edge70Inv
  exact scanFacts hp hs (holds_relator 49 (level0Relator 1) (level0_relator 1))

theorem edge757Inv : Holds level0Subgroup PresentedGroup.of representative ⟨71, [(true, false)], 70⟩ :=
  holds_reverse edge757

theorem edge758 : Holds level0Subgroup PresentedGroup.of representative ⟨72, [(true, true)], 73⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨50, [(true, true)], 72⟩ :=
    edge71
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨73, [(true, true)], 50⟩ :=
    edge72Inv
  exact scanFacts hp hs (holds_relator 50 (level0Relator 1) (level0_relator 1))

theorem edge758Inv : Holds level0Subgroup PresentedGroup.of representative ⟨73, [(true, false)], 72⟩ :=
  holds_reverse edge758

theorem edge759 : Holds level0Subgroup PresentedGroup.of representative ⟨74, [(true, true)], 75⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨51, [(true, true)], 74⟩ :=
    edge73
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨75, [(true, true)], 51⟩ :=
    edge74Inv
  exact scanFacts hp hs (holds_relator 51 (level0Relator 1) (level0_relator 1))

theorem edge759Inv : Holds level0Subgroup PresentedGroup.of representative ⟨75, [(true, false)], 74⟩ :=
  holds_reverse edge759

theorem edge760 : Holds level0Subgroup PresentedGroup.of representative ⟨76, [(false, true)], 52⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨52, [(false, true)], 76⟩ :=
    edge75
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨52, [], 52⟩ :=
    (holds_refl 52)
  exact scanFacts hp hs (holds_relator 52 (level0Relator 0) (level0_relator 0))

theorem edge760Inv : Holds level0Subgroup PresentedGroup.of representative ⟨52, [(false, false)], 76⟩ :=
  holds_reverse edge760

theorem edge761 : Holds level0Subgroup PresentedGroup.of representative ⟨77, [(false, true)], 53⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨53, [(false, true)], 77⟩ :=
    edge76
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨53, [], 53⟩ :=
    (holds_refl 53)
  exact scanFacts hp hs (holds_relator 53 (level0Relator 0) (level0_relator 0))

theorem edge761Inv : Holds level0Subgroup PresentedGroup.of representative ⟨53, [(false, false)], 77⟩ :=
  holds_reverse edge761

theorem edge762 : Holds level0Subgroup PresentedGroup.of representative ⟨78, [(false, true)], 55⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨55, [(false, true)], 78⟩ :=
    edge77
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨55, [], 55⟩ :=
    (holds_refl 55)
  exact scanFacts hp hs (holds_relator 55 (level0Relator 0) (level0_relator 0))

theorem edge762Inv : Holds level0Subgroup PresentedGroup.of representative ⟨55, [(false, false)], 78⟩ :=
  holds_reverse edge762

theorem edge763 : Holds level0Subgroup PresentedGroup.of representative ⟨79, [(false, true)], 56⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨56, [(false, true)], 79⟩ :=
    edge78
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨56, [], 56⟩ :=
    (holds_refl 56)
  exact scanFacts hp hs (holds_relator 56 (level0Relator 0) (level0_relator 0))

theorem edge763Inv : Holds level0Subgroup PresentedGroup.of representative ⟨56, [(false, false)], 79⟩ :=
  holds_reverse edge763

theorem edge764 : Holds level0Subgroup PresentedGroup.of representative ⟨80, [(false, true)], 57⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨57, [(false, true)], 80⟩ :=
    edge79
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨57, [], 57⟩ :=
    (holds_refl 57)
  exact scanFacts hp hs (holds_relator 57 (level0Relator 0) (level0_relator 0))

theorem edge764Inv : Holds level0Subgroup PresentedGroup.of representative ⟨57, [(false, false)], 80⟩ :=
  holds_reverse edge764

theorem edge765 : Holds level0Subgroup PresentedGroup.of representative ⟨81, [(false, true)], 58⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨58, [(false, true)], 81⟩ :=
    edge80
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨58, [], 58⟩ :=
    (holds_refl 58)
  exact scanFacts hp hs (holds_relator 58 (level0Relator 0) (level0_relator 0))

theorem edge765Inv : Holds level0Subgroup PresentedGroup.of representative ⟨58, [(false, false)], 81⟩ :=
  holds_reverse edge765

theorem edge766 : Holds level0Subgroup PresentedGroup.of representative ⟨82, [(false, true)], 59⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨59, [(false, true)], 82⟩ :=
    edge81
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨59, [], 59⟩ :=
    (holds_refl 59)
  exact scanFacts hp hs (holds_relator 59 (level0Relator 0) (level0_relator 0))

theorem edge766Inv : Holds level0Subgroup PresentedGroup.of representative ⟨59, [(false, false)], 82⟩ :=
  holds_reverse edge766

theorem edge767 : Holds level0Subgroup PresentedGroup.of representative ⟨83, [(false, true)], 60⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨60, [(false, true)], 83⟩ :=
    edge82
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨60, [], 60⟩ :=
    (holds_refl 60)
  exact scanFacts hp hs (holds_relator 60 (level0Relator 0) (level0_relator 0))

theorem edge767Inv : Holds level0Subgroup PresentedGroup.of representative ⟨60, [(false, false)], 83⟩ :=
  holds_reverse edge767


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
