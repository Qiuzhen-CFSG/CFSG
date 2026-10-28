module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges08

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

theorem edge576 : Holds level0Subgroup PresentedGroup.of representative ⟨490, [(true, false)], 577⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge576Inv : Holds level0Subgroup PresentedGroup.of representative ⟨577, [(true, true)], 490⟩ :=
  holds_reverse edge576

theorem edge577 : Holds level0Subgroup PresentedGroup.of representative ⟨491, [(true, true)], 578⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge577Inv : Holds level0Subgroup PresentedGroup.of representative ⟨578, [(true, false)], 491⟩ :=
  holds_reverse edge577

theorem edge578 : Holds level0Subgroup PresentedGroup.of representative ⟨491, [(true, false)], 579⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge578Inv : Holds level0Subgroup PresentedGroup.of representative ⟨579, [(true, true)], 491⟩ :=
  holds_reverse edge578

theorem edge579 : Holds level0Subgroup PresentedGroup.of representative ⟨493, [(true, true)], 580⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge579Inv : Holds level0Subgroup PresentedGroup.of representative ⟨580, [(true, false)], 493⟩ :=
  holds_reverse edge579

theorem edge580 : Holds level0Subgroup PresentedGroup.of representative ⟨493, [(true, false)], 581⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge580Inv : Holds level0Subgroup PresentedGroup.of representative ⟨581, [(true, true)], 493⟩ :=
  holds_reverse edge580

theorem edge581 : Holds level0Subgroup PresentedGroup.of representative ⟨495, [(true, true)], 582⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge581Inv : Holds level0Subgroup PresentedGroup.of representative ⟨582, [(true, false)], 495⟩ :=
  holds_reverse edge581

theorem edge582 : Holds level0Subgroup PresentedGroup.of representative ⟨495, [(true, false)], 583⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge582Inv : Holds level0Subgroup PresentedGroup.of representative ⟨583, [(true, true)], 495⟩ :=
  holds_reverse edge582

theorem edge583 : Holds level0Subgroup PresentedGroup.of representative ⟨496, [(true, true)], 584⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge583Inv : Holds level0Subgroup PresentedGroup.of representative ⟨584, [(true, false)], 496⟩ :=
  holds_reverse edge583

theorem edge584 : Holds level0Subgroup PresentedGroup.of representative ⟨496, [(true, false)], 585⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge584Inv : Holds level0Subgroup PresentedGroup.of representative ⟨585, [(true, true)], 496⟩ :=
  holds_reverse edge584

theorem edge585 : Holds level0Subgroup PresentedGroup.of representative ⟨498, [(true, true)], 586⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge585Inv : Holds level0Subgroup PresentedGroup.of representative ⟨586, [(true, false)], 498⟩ :=
  holds_reverse edge585

theorem edge586 : Holds level0Subgroup PresentedGroup.of representative ⟨498, [(true, false)], 587⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge586Inv : Holds level0Subgroup PresentedGroup.of representative ⟨587, [(true, true)], 498⟩ :=
  holds_reverse edge586

theorem edge587 : Holds level0Subgroup PresentedGroup.of representative ⟨499, [(true, true)], 588⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge587Inv : Holds level0Subgroup PresentedGroup.of representative ⟨588, [(true, false)], 499⟩ :=
  holds_reverse edge587

theorem edge588 : Holds level0Subgroup PresentedGroup.of representative ⟨499, [(true, false)], 589⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge588Inv : Holds level0Subgroup PresentedGroup.of representative ⟨589, [(true, true)], 499⟩ :=
  holds_reverse edge588

theorem edge589 : Holds level0Subgroup PresentedGroup.of representative ⟨500, [(true, true)], 590⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge589Inv : Holds level0Subgroup PresentedGroup.of representative ⟨590, [(true, false)], 500⟩ :=
  holds_reverse edge589

theorem edge590 : Holds level0Subgroup PresentedGroup.of representative ⟨500, [(true, false)], 591⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge590Inv : Holds level0Subgroup PresentedGroup.of representative ⟨591, [(true, true)], 500⟩ :=
  holds_reverse edge590

theorem edge591 : Holds level0Subgroup PresentedGroup.of representative ⟨501, [(true, true)], 592⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge591Inv : Holds level0Subgroup PresentedGroup.of representative ⟨592, [(true, false)], 501⟩ :=
  holds_reverse edge591

theorem edge592 : Holds level0Subgroup PresentedGroup.of representative ⟨501, [(true, false)], 593⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge592Inv : Holds level0Subgroup PresentedGroup.of representative ⟨593, [(true, true)], 501⟩ :=
  holds_reverse edge592

theorem edge593 : Holds level0Subgroup PresentedGroup.of representative ⟨502, [(true, true)], 594⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge593Inv : Holds level0Subgroup PresentedGroup.of representative ⟨594, [(true, false)], 502⟩ :=
  holds_reverse edge593

theorem edge594 : Holds level0Subgroup PresentedGroup.of representative ⟨502, [(true, false)], 595⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge594Inv : Holds level0Subgroup PresentedGroup.of representative ⟨595, [(true, true)], 502⟩ :=
  holds_reverse edge594

theorem edge595 : Holds level0Subgroup PresentedGroup.of representative ⟨505, [(true, true)], 596⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge595Inv : Holds level0Subgroup PresentedGroup.of representative ⟨596, [(true, false)], 505⟩ :=
  holds_reverse edge595

theorem edge596 : Holds level0Subgroup PresentedGroup.of representative ⟨505, [(true, false)], 597⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge596Inv : Holds level0Subgroup PresentedGroup.of representative ⟨597, [(true, true)], 505⟩ :=
  holds_reverse edge596

theorem edge597 : Holds level0Subgroup PresentedGroup.of representative ⟨506, [(true, false)], 598⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge597Inv : Holds level0Subgroup PresentedGroup.of representative ⟨598, [(true, true)], 506⟩ :=
  holds_reverse edge597

theorem edge598 : Holds level0Subgroup PresentedGroup.of representative ⟨511, [(true, true)], 599⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge598Inv : Holds level0Subgroup PresentedGroup.of representative ⟨599, [(true, false)], 511⟩ :=
  holds_reverse edge598

theorem edge599 : Holds level0Subgroup PresentedGroup.of representative ⟨511, [(true, false)], 600⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge599Inv : Holds level0Subgroup PresentedGroup.of representative ⟨600, [(true, true)], 511⟩ :=
  holds_reverse edge599

theorem edge600 : Holds level0Subgroup PresentedGroup.of representative ⟨512, [(true, true)], 601⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge600Inv : Holds level0Subgroup PresentedGroup.of representative ⟨601, [(true, false)], 512⟩ :=
  holds_reverse edge600

theorem edge601 : Holds level0Subgroup PresentedGroup.of representative ⟨512, [(true, false)], 602⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge601Inv : Holds level0Subgroup PresentedGroup.of representative ⟨602, [(true, true)], 512⟩ :=
  holds_reverse edge601

theorem edge602 : Holds level0Subgroup PresentedGroup.of representative ⟨513, [(true, true)], 603⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge602Inv : Holds level0Subgroup PresentedGroup.of representative ⟨603, [(true, false)], 513⟩ :=
  holds_reverse edge602

theorem edge603 : Holds level0Subgroup PresentedGroup.of representative ⟨513, [(true, false)], 604⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge603Inv : Holds level0Subgroup PresentedGroup.of representative ⟨604, [(true, true)], 513⟩ :=
  holds_reverse edge603

theorem edge604 : Holds level0Subgroup PresentedGroup.of representative ⟨515, [(true, false)], 605⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge604Inv : Holds level0Subgroup PresentedGroup.of representative ⟨605, [(true, true)], 515⟩ :=
  holds_reverse edge604

theorem edge605 : Holds level0Subgroup PresentedGroup.of representative ⟨516, [(true, true)], 606⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge605Inv : Holds level0Subgroup PresentedGroup.of representative ⟨606, [(true, false)], 516⟩ :=
  holds_reverse edge605

theorem edge606 : Holds level0Subgroup PresentedGroup.of representative ⟨518, [(true, true)], 607⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge606Inv : Holds level0Subgroup PresentedGroup.of representative ⟨607, [(true, false)], 518⟩ :=
  holds_reverse edge606

theorem edge607 : Holds level0Subgroup PresentedGroup.of representative ⟨518, [(true, false)], 608⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge607Inv : Holds level0Subgroup PresentedGroup.of representative ⟨608, [(true, true)], 518⟩ :=
  holds_reverse edge607

theorem edge608 : Holds level0Subgroup PresentedGroup.of representative ⟨521, [(true, true)], 609⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge608Inv : Holds level0Subgroup PresentedGroup.of representative ⟨609, [(true, false)], 521⟩ :=
  holds_reverse edge608

theorem edge609 : Holds level0Subgroup PresentedGroup.of representative ⟨521, [(true, false)], 610⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge609Inv : Holds level0Subgroup PresentedGroup.of representative ⟨610, [(true, true)], 521⟩ :=
  holds_reverse edge609

theorem edge610 : Holds level0Subgroup PresentedGroup.of representative ⟨522, [(true, true)], 611⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge610Inv : Holds level0Subgroup PresentedGroup.of representative ⟨611, [(true, false)], 522⟩ :=
  holds_reverse edge610

theorem edge611 : Holds level0Subgroup PresentedGroup.of representative ⟨522, [(true, false)], 612⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge611Inv : Holds level0Subgroup PresentedGroup.of representative ⟨612, [(true, true)], 522⟩ :=
  holds_reverse edge611

theorem edge612 : Holds level0Subgroup PresentedGroup.of representative ⟨524, [(true, true)], 613⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge612Inv : Holds level0Subgroup PresentedGroup.of representative ⟨613, [(true, false)], 524⟩ :=
  holds_reverse edge612

theorem edge613 : Holds level0Subgroup PresentedGroup.of representative ⟨524, [(true, false)], 614⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge613Inv : Holds level0Subgroup PresentedGroup.of representative ⟨614, [(true, true)], 524⟩ :=
  holds_reverse edge613

theorem edge614 : Holds level0Subgroup PresentedGroup.of representative ⟨525, [(true, true)], 615⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge614Inv : Holds level0Subgroup PresentedGroup.of representative ⟨615, [(true, false)], 525⟩ :=
  holds_reverse edge614

theorem edge615 : Holds level0Subgroup PresentedGroup.of representative ⟨525, [(true, false)], 616⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge615Inv : Holds level0Subgroup PresentedGroup.of representative ⟨616, [(true, true)], 525⟩ :=
  holds_reverse edge615

theorem edge616 : Holds level0Subgroup PresentedGroup.of representative ⟨527, [(true, true)], 617⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge616Inv : Holds level0Subgroup PresentedGroup.of representative ⟨617, [(true, false)], 527⟩ :=
  holds_reverse edge616

theorem edge617 : Holds level0Subgroup PresentedGroup.of representative ⟨527, [(true, false)], 618⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge617Inv : Holds level0Subgroup PresentedGroup.of representative ⟨618, [(true, true)], 527⟩ :=
  holds_reverse edge617

theorem edge618 : Holds level0Subgroup PresentedGroup.of representative ⟨529, [(true, true)], 619⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge618Inv : Holds level0Subgroup PresentedGroup.of representative ⟨619, [(true, false)], 529⟩ :=
  holds_reverse edge618

theorem edge619 : Holds level0Subgroup PresentedGroup.of representative ⟨529, [(true, false)], 620⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge619Inv : Holds level0Subgroup PresentedGroup.of representative ⟨620, [(true, true)], 529⟩ :=
  holds_reverse edge619

theorem edge620 : Holds level0Subgroup PresentedGroup.of representative ⟨530, [(true, true)], 621⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge620Inv : Holds level0Subgroup PresentedGroup.of representative ⟨621, [(true, false)], 530⟩ :=
  holds_reverse edge620

theorem edge621 : Holds level0Subgroup PresentedGroup.of representative ⟨530, [(true, false)], 622⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge621Inv : Holds level0Subgroup PresentedGroup.of representative ⟨622, [(true, true)], 530⟩ :=
  holds_reverse edge621

theorem edge622 : Holds level0Subgroup PresentedGroup.of representative ⟨531, [(true, true)], 623⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge622Inv : Holds level0Subgroup PresentedGroup.of representative ⟨623, [(true, false)], 531⟩ :=
  holds_reverse edge622

theorem edge623 : Holds level0Subgroup PresentedGroup.of representative ⟨531, [(true, false)], 624⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge623Inv : Holds level0Subgroup PresentedGroup.of representative ⟨624, [(true, true)], 531⟩ :=
  holds_reverse edge623

theorem edge624 : Holds level0Subgroup PresentedGroup.of representative ⟨538, [(false, true)], 625⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge624Inv : Holds level0Subgroup PresentedGroup.of representative ⟨625, [(false, false)], 538⟩ :=
  holds_reverse edge624

theorem edge625 : Holds level0Subgroup PresentedGroup.of representative ⟨545, [(false, true)], 626⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge625Inv : Holds level0Subgroup PresentedGroup.of representative ⟨626, [(false, false)], 545⟩ :=
  holds_reverse edge625

theorem edge626 : Holds level0Subgroup PresentedGroup.of representative ⟨547, [(false, true)], 627⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge626Inv : Holds level0Subgroup PresentedGroup.of representative ⟨627, [(false, false)], 547⟩ :=
  holds_reverse edge626

theorem edge627 : Holds level0Subgroup PresentedGroup.of representative ⟨548, [(false, true)], 628⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge627Inv : Holds level0Subgroup PresentedGroup.of representative ⟨628, [(false, false)], 548⟩ :=
  holds_reverse edge627

theorem edge628 : Holds level0Subgroup PresentedGroup.of representative ⟨549, [(false, true)], 629⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge628Inv : Holds level0Subgroup PresentedGroup.of representative ⟨629, [(false, false)], 549⟩ :=
  holds_reverse edge628

theorem edge629 : Holds level0Subgroup PresentedGroup.of representative ⟨551, [(false, true)], 630⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge629Inv : Holds level0Subgroup PresentedGroup.of representative ⟨630, [(false, false)], 551⟩ :=
  holds_reverse edge629

theorem edge630 : Holds level0Subgroup PresentedGroup.of representative ⟨555, [(false, true)], 631⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge630Inv : Holds level0Subgroup PresentedGroup.of representative ⟨631, [(false, false)], 555⟩ :=
  holds_reverse edge630

theorem edge631 : Holds level0Subgroup PresentedGroup.of representative ⟨556, [(false, true)], 632⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge631Inv : Holds level0Subgroup PresentedGroup.of representative ⟨632, [(false, false)], 556⟩ :=
  holds_reverse edge631

theorem edge632 : Holds level0Subgroup PresentedGroup.of representative ⟨557, [(false, true)], 633⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge632Inv : Holds level0Subgroup PresentedGroup.of representative ⟨633, [(false, false)], 557⟩ :=
  holds_reverse edge632

theorem edge633 : Holds level0Subgroup PresentedGroup.of representative ⟨559, [(false, true)], 634⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge633Inv : Holds level0Subgroup PresentedGroup.of representative ⟨634, [(false, false)], 559⟩ :=
  holds_reverse edge633

theorem edge634 : Holds level0Subgroup PresentedGroup.of representative ⟨563, [(false, true)], 635⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge634Inv : Holds level0Subgroup PresentedGroup.of representative ⟨635, [(false, false)], 563⟩ :=
  holds_reverse edge634

theorem edge635 : Holds level0Subgroup PresentedGroup.of representative ⟨564, [(false, true)], 636⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge635Inv : Holds level0Subgroup PresentedGroup.of representative ⟨636, [(false, false)], 564⟩ :=
  holds_reverse edge635

theorem edge636 : Holds level0Subgroup PresentedGroup.of representative ⟨565, [(false, true)], 637⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge636Inv : Holds level0Subgroup PresentedGroup.of representative ⟨637, [(false, false)], 565⟩ :=
  holds_reverse edge636

theorem edge637 : Holds level0Subgroup PresentedGroup.of representative ⟨566, [(false, true)], 638⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge637Inv : Holds level0Subgroup PresentedGroup.of representative ⟨638, [(false, false)], 566⟩ :=
  holds_reverse edge637

theorem edge638 : Holds level0Subgroup PresentedGroup.of representative ⟨567, [(false, true)], 639⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge638Inv : Holds level0Subgroup PresentedGroup.of representative ⟨639, [(false, false)], 567⟩ :=
  holds_reverse edge638

theorem edge639 : Holds level0Subgroup PresentedGroup.of representative ⟨569, [(false, true)], 640⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge639Inv : Holds level0Subgroup PresentedGroup.of representative ⟨640, [(false, false)], 569⟩ :=
  holds_reverse edge639


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
