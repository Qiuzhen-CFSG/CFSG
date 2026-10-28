module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Base

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

theorem edge0 : Holds level0Subgroup PresentedGroup.of representative ⟨0, [(false, true)], 1⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [] [(false, true)]).symm

theorem edge0Inv : Holds level0Subgroup PresentedGroup.of representative ⟨1, [(false, false)], 0⟩ :=
  holds_reverse edge0

theorem edge1 : Holds level0Subgroup PresentedGroup.of representative ⟨1, [(true, true)], 2⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true)] [(true, true)]).symm

theorem edge1Inv : Holds level0Subgroup PresentedGroup.of representative ⟨2, [(true, false)], 1⟩ :=
  holds_reverse edge1

theorem edge2 : Holds level0Subgroup PresentedGroup.of representative ⟨1, [(true, false)], 3⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true)] [(true, false)]).symm

theorem edge2Inv : Holds level0Subgroup PresentedGroup.of representative ⟨3, [(true, true)], 1⟩ :=
  holds_reverse edge2

theorem edge3 : Holds level0Subgroup PresentedGroup.of representative ⟨2, [(false, true)], 4⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true)] [(false, true)]).symm

theorem edge3Inv : Holds level0Subgroup PresentedGroup.of representative ⟨4, [(false, false)], 2⟩ :=
  holds_reverse edge3

theorem edge4 : Holds level0Subgroup PresentedGroup.of representative ⟨3, [(false, true)], 5⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false)] [(false, true)]).symm

theorem edge4Inv : Holds level0Subgroup PresentedGroup.of representative ⟨5, [(false, false)], 3⟩ :=
  holds_reverse edge4

theorem edge5 : Holds level0Subgroup PresentedGroup.of representative ⟨4, [(true, true)], 6⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge5Inv : Holds level0Subgroup PresentedGroup.of representative ⟨6, [(true, false)], 4⟩ :=
  holds_reverse edge5

theorem edge6 : Holds level0Subgroup PresentedGroup.of representative ⟨4, [(true, false)], 7⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge6Inv : Holds level0Subgroup PresentedGroup.of representative ⟨7, [(true, true)], 4⟩ :=
  holds_reverse edge6

theorem edge7 : Holds level0Subgroup PresentedGroup.of representative ⟨5, [(true, true)], 8⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge7Inv : Holds level0Subgroup PresentedGroup.of representative ⟨8, [(true, false)], 5⟩ :=
  holds_reverse edge7

theorem edge8 : Holds level0Subgroup PresentedGroup.of representative ⟨5, [(true, false)], 9⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge8Inv : Holds level0Subgroup PresentedGroup.of representative ⟨9, [(true, true)], 5⟩ :=
  holds_reverse edge8

theorem edge9 : Holds level0Subgroup PresentedGroup.of representative ⟨6, [(false, true)], 10⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge9Inv : Holds level0Subgroup PresentedGroup.of representative ⟨10, [(false, false)], 6⟩ :=
  holds_reverse edge9

theorem edge10 : Holds level0Subgroup PresentedGroup.of representative ⟨7, [(false, true)], 11⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge10Inv : Holds level0Subgroup PresentedGroup.of representative ⟨11, [(false, false)], 7⟩ :=
  holds_reverse edge10

theorem edge11 : Holds level0Subgroup PresentedGroup.of representative ⟨8, [(false, true)], 12⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge11Inv : Holds level0Subgroup PresentedGroup.of representative ⟨12, [(false, false)], 8⟩ :=
  holds_reverse edge11

theorem edge12 : Holds level0Subgroup PresentedGroup.of representative ⟨9, [(false, true)], 13⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge12Inv : Holds level0Subgroup PresentedGroup.of representative ⟨13, [(false, false)], 9⟩ :=
  holds_reverse edge12

theorem edge13 : Holds level0Subgroup PresentedGroup.of representative ⟨10, [(true, true)], 14⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge13Inv : Holds level0Subgroup PresentedGroup.of representative ⟨14, [(true, false)], 10⟩ :=
  holds_reverse edge13

theorem edge14 : Holds level0Subgroup PresentedGroup.of representative ⟨10, [(true, false)], 15⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge14Inv : Holds level0Subgroup PresentedGroup.of representative ⟨15, [(true, true)], 10⟩ :=
  holds_reverse edge14

theorem edge15 : Holds level0Subgroup PresentedGroup.of representative ⟨11, [(true, true)], 16⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge15Inv : Holds level0Subgroup PresentedGroup.of representative ⟨16, [(true, false)], 11⟩ :=
  holds_reverse edge15

theorem edge16 : Holds level0Subgroup PresentedGroup.of representative ⟨11, [(true, false)], 17⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge16Inv : Holds level0Subgroup PresentedGroup.of representative ⟨17, [(true, true)], 11⟩ :=
  holds_reverse edge16

theorem edge17 : Holds level0Subgroup PresentedGroup.of representative ⟨12, [(true, true)], 18⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge17Inv : Holds level0Subgroup PresentedGroup.of representative ⟨18, [(true, false)], 12⟩ :=
  holds_reverse edge17

theorem edge18 : Holds level0Subgroup PresentedGroup.of representative ⟨12, [(true, false)], 19⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge18Inv : Holds level0Subgroup PresentedGroup.of representative ⟨19, [(true, true)], 12⟩ :=
  holds_reverse edge18

theorem edge19 : Holds level0Subgroup PresentedGroup.of representative ⟨13, [(true, true)], 20⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge19Inv : Holds level0Subgroup PresentedGroup.of representative ⟨20, [(true, false)], 13⟩ :=
  holds_reverse edge19

theorem edge20 : Holds level0Subgroup PresentedGroup.of representative ⟨13, [(true, false)], 21⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge20Inv : Holds level0Subgroup PresentedGroup.of representative ⟨21, [(true, true)], 13⟩ :=
  holds_reverse edge20

theorem edge21 : Holds level0Subgroup PresentedGroup.of representative ⟨15, [(false, true)], 22⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge21Inv : Holds level0Subgroup PresentedGroup.of representative ⟨22, [(false, false)], 15⟩ :=
  holds_reverse edge21

theorem edge22 : Holds level0Subgroup PresentedGroup.of representative ⟨16, [(false, true)], 23⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge22Inv : Holds level0Subgroup PresentedGroup.of representative ⟨23, [(false, false)], 16⟩ :=
  holds_reverse edge22

theorem edge23 : Holds level0Subgroup PresentedGroup.of representative ⟨17, [(false, true)], 24⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge23Inv : Holds level0Subgroup PresentedGroup.of representative ⟨24, [(false, false)], 17⟩ :=
  holds_reverse edge23

theorem edge24 : Holds level0Subgroup PresentedGroup.of representative ⟨18, [(false, true)], 25⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge24Inv : Holds level0Subgroup PresentedGroup.of representative ⟨25, [(false, false)], 18⟩ :=
  holds_reverse edge24

theorem edge25 : Holds level0Subgroup PresentedGroup.of representative ⟨19, [(false, true)], 26⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge25Inv : Holds level0Subgroup PresentedGroup.of representative ⟨26, [(false, false)], 19⟩ :=
  holds_reverse edge25

theorem edge26 : Holds level0Subgroup PresentedGroup.of representative ⟨20, [(false, true)], 27⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge26Inv : Holds level0Subgroup PresentedGroup.of representative ⟨27, [(false, false)], 20⟩ :=
  holds_reverse edge26

theorem edge27 : Holds level0Subgroup PresentedGroup.of representative ⟨22, [(true, true)], 28⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge27Inv : Holds level0Subgroup PresentedGroup.of representative ⟨28, [(true, false)], 22⟩ :=
  holds_reverse edge27

theorem edge28 : Holds level0Subgroup PresentedGroup.of representative ⟨22, [(true, false)], 29⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge28Inv : Holds level0Subgroup PresentedGroup.of representative ⟨29, [(true, true)], 22⟩ :=
  holds_reverse edge28

theorem edge29 : Holds level0Subgroup PresentedGroup.of representative ⟨23, [(true, true)], 30⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge29Inv : Holds level0Subgroup PresentedGroup.of representative ⟨30, [(true, false)], 23⟩ :=
  holds_reverse edge29

theorem edge30 : Holds level0Subgroup PresentedGroup.of representative ⟨23, [(true, false)], 31⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge30Inv : Holds level0Subgroup PresentedGroup.of representative ⟨31, [(true, true)], 23⟩ :=
  holds_reverse edge30

theorem edge31 : Holds level0Subgroup PresentedGroup.of representative ⟨24, [(true, true)], 32⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge31Inv : Holds level0Subgroup PresentedGroup.of representative ⟨32, [(true, false)], 24⟩ :=
  holds_reverse edge31

theorem edge32 : Holds level0Subgroup PresentedGroup.of representative ⟨24, [(true, false)], 33⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge32Inv : Holds level0Subgroup PresentedGroup.of representative ⟨33, [(true, true)], 24⟩ :=
  holds_reverse edge32

theorem edge33 : Holds level0Subgroup PresentedGroup.of representative ⟨25, [(true, true)], 34⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge33Inv : Holds level0Subgroup PresentedGroup.of representative ⟨34, [(true, false)], 25⟩ :=
  holds_reverse edge33

theorem edge34 : Holds level0Subgroup PresentedGroup.of representative ⟨25, [(true, false)], 35⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge34Inv : Holds level0Subgroup PresentedGroup.of representative ⟨35, [(true, true)], 25⟩ :=
  holds_reverse edge34

theorem edge35 : Holds level0Subgroup PresentedGroup.of representative ⟨26, [(true, true)], 36⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge35Inv : Holds level0Subgroup PresentedGroup.of representative ⟨36, [(true, false)], 26⟩ :=
  holds_reverse edge35

theorem edge36 : Holds level0Subgroup PresentedGroup.of representative ⟨26, [(true, false)], 37⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge36Inv : Holds level0Subgroup PresentedGroup.of representative ⟨37, [(true, true)], 26⟩ :=
  holds_reverse edge36

theorem edge37 : Holds level0Subgroup PresentedGroup.of representative ⟨27, [(true, true)], 38⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge37Inv : Holds level0Subgroup PresentedGroup.of representative ⟨38, [(true, false)], 27⟩ :=
  holds_reverse edge37

theorem edge38 : Holds level0Subgroup PresentedGroup.of representative ⟨27, [(true, false)], 39⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge38Inv : Holds level0Subgroup PresentedGroup.of representative ⟨39, [(true, true)], 27⟩ :=
  holds_reverse edge38

theorem edge39 : Holds level0Subgroup PresentedGroup.of representative ⟨28, [(false, true)], 40⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge39Inv : Holds level0Subgroup PresentedGroup.of representative ⟨40, [(false, false)], 28⟩ :=
  holds_reverse edge39

theorem edge40 : Holds level0Subgroup PresentedGroup.of representative ⟨29, [(false, true)], 41⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge40Inv : Holds level0Subgroup PresentedGroup.of representative ⟨41, [(false, false)], 29⟩ :=
  holds_reverse edge40

theorem edge41 : Holds level0Subgroup PresentedGroup.of representative ⟨30, [(false, true)], 42⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge41Inv : Holds level0Subgroup PresentedGroup.of representative ⟨42, [(false, false)], 30⟩ :=
  holds_reverse edge41

theorem edge42 : Holds level0Subgroup PresentedGroup.of representative ⟨31, [(false, true)], 43⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge42Inv : Holds level0Subgroup PresentedGroup.of representative ⟨43, [(false, false)], 31⟩ :=
  holds_reverse edge42

theorem edge43 : Holds level0Subgroup PresentedGroup.of representative ⟨32, [(false, true)], 44⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge43Inv : Holds level0Subgroup PresentedGroup.of representative ⟨44, [(false, false)], 32⟩ :=
  holds_reverse edge43

theorem edge44 : Holds level0Subgroup PresentedGroup.of representative ⟨33, [(false, true)], 45⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge44Inv : Holds level0Subgroup PresentedGroup.of representative ⟨45, [(false, false)], 33⟩ :=
  holds_reverse edge44

theorem edge45 : Holds level0Subgroup PresentedGroup.of representative ⟨34, [(false, true)], 46⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge45Inv : Holds level0Subgroup PresentedGroup.of representative ⟨46, [(false, false)], 34⟩ :=
  holds_reverse edge45

theorem edge46 : Holds level0Subgroup PresentedGroup.of representative ⟨35, [(false, true)], 47⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge46Inv : Holds level0Subgroup PresentedGroup.of representative ⟨47, [(false, false)], 35⟩ :=
  holds_reverse edge46

theorem edge47 : Holds level0Subgroup PresentedGroup.of representative ⟨36, [(false, true)], 48⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge47Inv : Holds level0Subgroup PresentedGroup.of representative ⟨48, [(false, false)], 36⟩ :=
  holds_reverse edge47

theorem edge48 : Holds level0Subgroup PresentedGroup.of representative ⟨37, [(false, true)], 49⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge48Inv : Holds level0Subgroup PresentedGroup.of representative ⟨49, [(false, false)], 37⟩ :=
  holds_reverse edge48

theorem edge49 : Holds level0Subgroup PresentedGroup.of representative ⟨38, [(false, true)], 50⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge49Inv : Holds level0Subgroup PresentedGroup.of representative ⟨50, [(false, false)], 38⟩ :=
  holds_reverse edge49

theorem edge50 : Holds level0Subgroup PresentedGroup.of representative ⟨39, [(false, true)], 51⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge50Inv : Holds level0Subgroup PresentedGroup.of representative ⟨51, [(false, false)], 39⟩ :=
  holds_reverse edge50

theorem edge51 : Holds level0Subgroup PresentedGroup.of representative ⟨40, [(true, true)], 52⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge51Inv : Holds level0Subgroup PresentedGroup.of representative ⟨52, [(true, false)], 40⟩ :=
  holds_reverse edge51

theorem edge52 : Holds level0Subgroup PresentedGroup.of representative ⟨40, [(true, false)], 53⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge52Inv : Holds level0Subgroup PresentedGroup.of representative ⟨53, [(true, true)], 40⟩ :=
  holds_reverse edge52

theorem edge53 : Holds level0Subgroup PresentedGroup.of representative ⟨41, [(true, true)], 54⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge53Inv : Holds level0Subgroup PresentedGroup.of representative ⟨54, [(true, false)], 41⟩ :=
  holds_reverse edge53

theorem edge54 : Holds level0Subgroup PresentedGroup.of representative ⟨41, [(true, false)], 55⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge54Inv : Holds level0Subgroup PresentedGroup.of representative ⟨55, [(true, true)], 41⟩ :=
  holds_reverse edge54

theorem edge55 : Holds level0Subgroup PresentedGroup.of representative ⟨42, [(true, true)], 56⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge55Inv : Holds level0Subgroup PresentedGroup.of representative ⟨56, [(true, false)], 42⟩ :=
  holds_reverse edge55

theorem edge56 : Holds level0Subgroup PresentedGroup.of representative ⟨42, [(true, false)], 57⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge56Inv : Holds level0Subgroup PresentedGroup.of representative ⟨57, [(true, true)], 42⟩ :=
  holds_reverse edge56

theorem edge57 : Holds level0Subgroup PresentedGroup.of representative ⟨43, [(true, true)], 58⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge57Inv : Holds level0Subgroup PresentedGroup.of representative ⟨58, [(true, false)], 43⟩ :=
  holds_reverse edge57

theorem edge58 : Holds level0Subgroup PresentedGroup.of representative ⟨43, [(true, false)], 59⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge58Inv : Holds level0Subgroup PresentedGroup.of representative ⟨59, [(true, true)], 43⟩ :=
  holds_reverse edge58

theorem edge59 : Holds level0Subgroup PresentedGroup.of representative ⟨44, [(true, true)], 60⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge59Inv : Holds level0Subgroup PresentedGroup.of representative ⟨60, [(true, false)], 44⟩ :=
  holds_reverse edge59

theorem edge60 : Holds level0Subgroup PresentedGroup.of representative ⟨44, [(true, false)], 61⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge60Inv : Holds level0Subgroup PresentedGroup.of representative ⟨61, [(true, true)], 44⟩ :=
  holds_reverse edge60

theorem edge61 : Holds level0Subgroup PresentedGroup.of representative ⟨45, [(true, true)], 62⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge61Inv : Holds level0Subgroup PresentedGroup.of representative ⟨62, [(true, false)], 45⟩ :=
  holds_reverse edge61

theorem edge62 : Holds level0Subgroup PresentedGroup.of representative ⟨45, [(true, false)], 63⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge62Inv : Holds level0Subgroup PresentedGroup.of representative ⟨63, [(true, true)], 45⟩ :=
  holds_reverse edge62

theorem edge63 : Holds level0Subgroup PresentedGroup.of representative ⟨46, [(true, true)], 64⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge63Inv : Holds level0Subgroup PresentedGroup.of representative ⟨64, [(true, false)], 46⟩ :=
  holds_reverse edge63


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
