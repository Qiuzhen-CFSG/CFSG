module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges09

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

theorem edge640 : Holds level0Subgroup PresentedGroup.of representative ⟨570, [(false, true)], 641⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge640Inv : Holds level0Subgroup PresentedGroup.of representative ⟨641, [(false, false)], 570⟩ :=
  holds_reverse edge640

theorem edge641 : Holds level0Subgroup PresentedGroup.of representative ⟨573, [(false, true)], 642⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge641Inv : Holds level0Subgroup PresentedGroup.of representative ⟨642, [(false, false)], 573⟩ :=
  holds_reverse edge641

theorem edge642 : Holds level0Subgroup PresentedGroup.of representative ⟨576, [(false, true)], 643⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge642Inv : Holds level0Subgroup PresentedGroup.of representative ⟨643, [(false, false)], 576⟩ :=
  holds_reverse edge642

theorem edge643 : Holds level0Subgroup PresentedGroup.of representative ⟨578, [(false, true)], 644⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge643Inv : Holds level0Subgroup PresentedGroup.of representative ⟨644, [(false, false)], 578⟩ :=
  holds_reverse edge643

theorem edge644 : Holds level0Subgroup PresentedGroup.of representative ⟨584, [(false, true)], 645⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge644Inv : Holds level0Subgroup PresentedGroup.of representative ⟨645, [(false, false)], 584⟩ :=
  holds_reverse edge644

theorem edge645 : Holds level0Subgroup PresentedGroup.of representative ⟨588, [(false, true)], 646⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge645Inv : Holds level0Subgroup PresentedGroup.of representative ⟨646, [(false, false)], 588⟩ :=
  holds_reverse edge645

theorem edge646 : Holds level0Subgroup PresentedGroup.of representative ⟨589, [(false, true)], 647⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge646Inv : Holds level0Subgroup PresentedGroup.of representative ⟨647, [(false, false)], 589⟩ :=
  holds_reverse edge646

theorem edge647 : Holds level0Subgroup PresentedGroup.of representative ⟨590, [(false, true)], 648⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge647Inv : Holds level0Subgroup PresentedGroup.of representative ⟨648, [(false, false)], 590⟩ :=
  holds_reverse edge647

theorem edge648 : Holds level0Subgroup PresentedGroup.of representative ⟨592, [(false, true)], 649⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge648Inv : Holds level0Subgroup PresentedGroup.of representative ⟨649, [(false, false)], 592⟩ :=
  holds_reverse edge648

theorem edge649 : Holds level0Subgroup PresentedGroup.of representative ⟨593, [(false, true)], 650⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge649Inv : Holds level0Subgroup PresentedGroup.of representative ⟨650, [(false, false)], 593⟩ :=
  holds_reverse edge649

theorem edge650 : Holds level0Subgroup PresentedGroup.of representative ⟨597, [(false, true)], 651⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge650Inv : Holds level0Subgroup PresentedGroup.of representative ⟨651, [(false, false)], 597⟩ :=
  holds_reverse edge650

theorem edge651 : Holds level0Subgroup PresentedGroup.of representative ⟨599, [(false, true)], 652⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge651Inv : Holds level0Subgroup PresentedGroup.of representative ⟨652, [(false, false)], 599⟩ :=
  holds_reverse edge651

theorem edge652 : Holds level0Subgroup PresentedGroup.of representative ⟨601, [(false, true)], 653⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge652Inv : Holds level0Subgroup PresentedGroup.of representative ⟨653, [(false, false)], 601⟩ :=
  holds_reverse edge652

theorem edge653 : Holds level0Subgroup PresentedGroup.of representative ⟨603, [(false, true)], 654⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge653Inv : Holds level0Subgroup PresentedGroup.of representative ⟨654, [(false, false)], 603⟩ :=
  holds_reverse edge653

theorem edge654 : Holds level0Subgroup PresentedGroup.of representative ⟨606, [(false, true)], 655⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge654Inv : Holds level0Subgroup PresentedGroup.of representative ⟨655, [(false, false)], 606⟩ :=
  holds_reverse edge654

theorem edge655 : Holds level0Subgroup PresentedGroup.of representative ⟨612, [(false, true)], 656⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge655Inv : Holds level0Subgroup PresentedGroup.of representative ⟨656, [(false, false)], 612⟩ :=
  holds_reverse edge655

theorem edge656 : Holds level0Subgroup PresentedGroup.of representative ⟨613, [(false, true)], 657⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge656Inv : Holds level0Subgroup PresentedGroup.of representative ⟨657, [(false, false)], 613⟩ :=
  holds_reverse edge656

theorem edge657 : Holds level0Subgroup PresentedGroup.of representative ⟨615, [(false, true)], 658⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge657Inv : Holds level0Subgroup PresentedGroup.of representative ⟨658, [(false, false)], 615⟩ :=
  holds_reverse edge657

theorem edge658 : Holds level0Subgroup PresentedGroup.of representative ⟨616, [(false, true)], 659⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge658Inv : Holds level0Subgroup PresentedGroup.of representative ⟨659, [(false, false)], 616⟩ :=
  holds_reverse edge658

theorem edge659 : Holds level0Subgroup PresentedGroup.of representative ⟨617, [(false, true)], 660⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge659Inv : Holds level0Subgroup PresentedGroup.of representative ⟨660, [(false, false)], 617⟩ :=
  holds_reverse edge659

theorem edge660 : Holds level0Subgroup PresentedGroup.of representative ⟨619, [(false, true)], 661⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge660Inv : Holds level0Subgroup PresentedGroup.of representative ⟨661, [(false, false)], 619⟩ :=
  holds_reverse edge660

theorem edge661 : Holds level0Subgroup PresentedGroup.of representative ⟨621, [(false, true)], 662⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge661Inv : Holds level0Subgroup PresentedGroup.of representative ⟨662, [(false, false)], 621⟩ :=
  holds_reverse edge661

theorem edge662 : Holds level0Subgroup PresentedGroup.of representative ⟨626, [(true, true)], 663⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge662Inv : Holds level0Subgroup PresentedGroup.of representative ⟨663, [(true, false)], 626⟩ :=
  holds_reverse edge662

theorem edge663 : Holds level0Subgroup PresentedGroup.of representative ⟨626, [(true, false)], 664⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge663Inv : Holds level0Subgroup PresentedGroup.of representative ⟨664, [(true, true)], 626⟩ :=
  holds_reverse edge663

theorem edge664 : Holds level0Subgroup PresentedGroup.of representative ⟨627, [(true, true)], 665⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge664Inv : Holds level0Subgroup PresentedGroup.of representative ⟨665, [(true, false)], 627⟩ :=
  holds_reverse edge664

theorem edge665 : Holds level0Subgroup PresentedGroup.of representative ⟨629, [(true, false)], 666⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge665Inv : Holds level0Subgroup PresentedGroup.of representative ⟨666, [(true, true)], 629⟩ :=
  holds_reverse edge665

theorem edge666 : Holds level0Subgroup PresentedGroup.of representative ⟨630, [(true, true)], 667⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge666Inv : Holds level0Subgroup PresentedGroup.of representative ⟨667, [(true, false)], 630⟩ :=
  holds_reverse edge666

theorem edge667 : Holds level0Subgroup PresentedGroup.of representative ⟨635, [(true, true)], 668⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge667Inv : Holds level0Subgroup PresentedGroup.of representative ⟨668, [(true, false)], 635⟩ :=
  holds_reverse edge667

theorem edge668 : Holds level0Subgroup PresentedGroup.of representative ⟨637, [(true, true)], 669⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge668Inv : Holds level0Subgroup PresentedGroup.of representative ⟨669, [(true, false)], 637⟩ :=
  holds_reverse edge668

theorem edge669 : Holds level0Subgroup PresentedGroup.of representative ⟨637, [(true, false)], 670⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge669Inv : Holds level0Subgroup PresentedGroup.of representative ⟨670, [(true, true)], 637⟩ :=
  holds_reverse edge669

theorem edge670 : Holds level0Subgroup PresentedGroup.of representative ⟨638, [(true, true)], 671⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge670Inv : Holds level0Subgroup PresentedGroup.of representative ⟨671, [(true, false)], 638⟩ :=
  holds_reverse edge670

theorem edge671 : Holds level0Subgroup PresentedGroup.of representative ⟨639, [(true, true)], 672⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge671Inv : Holds level0Subgroup PresentedGroup.of representative ⟨672, [(true, false)], 639⟩ :=
  holds_reverse edge671

theorem edge672 : Holds level0Subgroup PresentedGroup.of representative ⟨640, [(true, true)], 673⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge672Inv : Holds level0Subgroup PresentedGroup.of representative ⟨673, [(true, false)], 640⟩ :=
  holds_reverse edge672

theorem edge673 : Holds level0Subgroup PresentedGroup.of representative ⟨640, [(true, false)], 674⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge673Inv : Holds level0Subgroup PresentedGroup.of representative ⟨674, [(true, true)], 640⟩ :=
  holds_reverse edge673

theorem edge674 : Holds level0Subgroup PresentedGroup.of representative ⟨643, [(true, true)], 675⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge674Inv : Holds level0Subgroup PresentedGroup.of representative ⟨675, [(true, false)], 643⟩ :=
  holds_reverse edge674

theorem edge675 : Holds level0Subgroup PresentedGroup.of representative ⟨644, [(true, false)], 676⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge675Inv : Holds level0Subgroup PresentedGroup.of representative ⟨676, [(true, true)], 644⟩ :=
  holds_reverse edge675

theorem edge676 : Holds level0Subgroup PresentedGroup.of representative ⟨649, [(true, false)], 677⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge676Inv : Holds level0Subgroup PresentedGroup.of representative ⟨677, [(true, true)], 649⟩ :=
  holds_reverse edge676

theorem edge677 : Holds level0Subgroup PresentedGroup.of representative ⟨651, [(true, true)], 678⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge677Inv : Holds level0Subgroup PresentedGroup.of representative ⟨678, [(true, false)], 651⟩ :=
  holds_reverse edge677

theorem edge678 : Holds level0Subgroup PresentedGroup.of representative ⟨651, [(true, false)], 679⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge678Inv : Holds level0Subgroup PresentedGroup.of representative ⟨679, [(true, true)], 651⟩ :=
  holds_reverse edge678

theorem edge679 : Holds level0Subgroup PresentedGroup.of representative ⟨655, [(true, true)], 680⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge679Inv : Holds level0Subgroup PresentedGroup.of representative ⟨680, [(true, false)], 655⟩ :=
  holds_reverse edge679

theorem edge680 : Holds level0Subgroup PresentedGroup.of representative ⟨655, [(true, false)], 681⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge680Inv : Holds level0Subgroup PresentedGroup.of representative ⟨681, [(true, true)], 655⟩ :=
  holds_reverse edge680

theorem edge681 : Holds level0Subgroup PresentedGroup.of representative ⟨659, [(true, true)], 682⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge681Inv : Holds level0Subgroup PresentedGroup.of representative ⟨682, [(true, false)], 659⟩ :=
  holds_reverse edge681

theorem edge682 : Holds level0Subgroup PresentedGroup.of representative ⟨659, [(true, false)], 683⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge682Inv : Holds level0Subgroup PresentedGroup.of representative ⟨683, [(true, true)], 659⟩ :=
  holds_reverse edge682

theorem edge683 : Holds level0Subgroup PresentedGroup.of representative ⟨663, [(false, true)], 684⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge683Inv : Holds level0Subgroup PresentedGroup.of representative ⟨684, [(false, false)], 663⟩ :=
  holds_reverse edge683

theorem edge684 : Holds level0Subgroup PresentedGroup.of representative ⟨665, [(false, true)], 685⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge684Inv : Holds level0Subgroup PresentedGroup.of representative ⟨685, [(false, false)], 665⟩ :=
  holds_reverse edge684

theorem edge685 : Holds level0Subgroup PresentedGroup.of representative ⟨669, [(false, true)], 686⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge685Inv : Holds level0Subgroup PresentedGroup.of representative ⟨686, [(false, false)], 669⟩ :=
  holds_reverse edge685

theorem edge686 : Holds level0Subgroup PresentedGroup.of representative ⟨670, [(false, true)], 687⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge686Inv : Holds level0Subgroup PresentedGroup.of representative ⟨687, [(false, false)], 670⟩ :=
  holds_reverse edge686

theorem edge687 : Holds level0Subgroup PresentedGroup.of representative ⟨671, [(false, true)], 688⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge687Inv : Holds level0Subgroup PresentedGroup.of representative ⟨688, [(false, false)], 671⟩ :=
  holds_reverse edge687

theorem edge688 : Holds level0Subgroup PresentedGroup.of representative ⟨680, [(false, true)], 689⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge688Inv : Holds level0Subgroup PresentedGroup.of representative ⟨689, [(false, false)], 680⟩ :=
  holds_reverse edge688

theorem edge689 : Holds level0Subgroup PresentedGroup.of representative ⟨682, [(false, true)], 690⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge689Inv : Holds level0Subgroup PresentedGroup.of representative ⟨690, [(false, false)], 682⟩ :=
  holds_reverse edge689

theorem edge690 : Holds level0Subgroup PresentedGroup.of representative ⟨683, [(false, true)], 691⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge690Inv : Holds level0Subgroup PresentedGroup.of representative ⟨691, [(false, false)], 683⟩ :=
  holds_reverse edge690

theorem edge691 : Holds level0Subgroup PresentedGroup.of representative ⟨686, [(true, true)], 692⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge691Inv : Holds level0Subgroup PresentedGroup.of representative ⟨692, [(true, false)], 686⟩ :=
  holds_reverse edge691

theorem edge692 : Holds level0Subgroup PresentedGroup.of representative ⟨0, [(true, true)], 0⟩ :=
  special 0 0 (true, true) [(0, true)] LiftedRelations.word0
    false 0 (by decide +kernel) LiftedRelations.valid0

theorem edge692Inv : Holds level0Subgroup PresentedGroup.of representative ⟨0, [(true, false)], 0⟩ :=
  holds_reverse edge692

theorem edge693 : Holds level0Subgroup PresentedGroup.of representative ⟨14, [(false, true)], 21⟩ :=
  special 14 21 (false, true) [(0, true), (2, true)] LiftedRelations.word0
    false 0 (by decide +kernel) LiftedRelations.valid0

theorem edge693Inv : Holds level0Subgroup PresentedGroup.of representative ⟨21, [(false, false)], 14⟩ :=
  holds_reverse edge693

theorem edge694 : Holds level0Subgroup PresentedGroup.of representative ⟨54, [(false, true)], 54⟩ :=
  special 54 54 (false, true) [(6, true), (4, true), (0, false), (2, false), (0, true), (5, true)] LiftedRelations.word67
    false 106 (by decide +kernel) LiftedRelations.valid67

theorem edge694Inv : Holds level0Subgroup PresentedGroup.of representative ⟨54, [(false, false)], 54⟩ :=
  holds_reverse edge694

theorem edge695 : Holds level0Subgroup PresentedGroup.of representative ⟨65, [(false, true)], 65⟩ :=
  special 65 65 (false, true) [(4, true), (3, true), (3, true), (2, false), (0, true), (5, true), (6, true)] LiftedRelations.word98
    false 40 (by decide +kernel) LiftedRelations.valid98

theorem edge695Inv : Holds level0Subgroup PresentedGroup.of representative ⟨65, [(false, false)], 65⟩ :=
  holds_reverse edge695

theorem edge696 : Holds level0Subgroup PresentedGroup.of representative ⟨99, [(false, true)], 99⟩ :=
  special 99 99 (false, true) [(4, true), (2, true), (0, true)] LiftedRelations.word28
    false 78 (by decide +kernel) LiftedRelations.valid28

theorem edge696Inv : Holds level0Subgroup PresentedGroup.of representative ⟨99, [(false, false)], 99⟩ :=
  holds_reverse edge696

theorem edge697 : Holds level0Subgroup PresentedGroup.of representative ⟨111, [(false, true)], 111⟩ :=
  special 111 111 (false, true) [(3, false), (0, true)] LiftedRelations.word0
    false 0 (by decide +kernel) LiftedRelations.valid0

theorem edge697Inv : Holds level0Subgroup PresentedGroup.of representative ⟨111, [(false, false)], 111⟩ :=
  holds_reverse edge697

theorem edge698 : Holds level0Subgroup PresentedGroup.of representative ⟨152, [(true, true)], 169⟩ :=
  special 152 169 (true, true) [(5, true), (4, false), (2, true), (3, false), (0, true)] LiftedRelations.word57
    true 85 (by decide +kernel) LiftedRelations.valid57

theorem edge698Inv : Holds level0Subgroup PresentedGroup.of representative ⟨169, [(true, false)], 152⟩ :=
  holds_reverse edge698

theorem edge699 : Holds level0Subgroup PresentedGroup.of representative ⟨209, [(false, true)], 242⟩ :=
  special 209 242 (false, true) [(0, true), (4, true), (0, false), (2, false), (5, true)] LiftedRelations.word40
    true 93 (by decide +kernel) LiftedRelations.valid40

theorem edge699Inv : Holds level0Subgroup PresentedGroup.of representative ⟨242, [(false, false)], 209⟩ :=
  holds_reverse edge699

theorem edge700 : Holds level0Subgroup PresentedGroup.of representative ⟨221, [(false, true)], 223⟩ :=
  special 221 223 (false, true) [(6, true), (4, true), (2, true), (2, true), (2, true), (5, true)] LiftedRelations.word106
    false 114 (by decide +kernel) LiftedRelations.valid106

theorem edge700Inv : Holds level0Subgroup PresentedGroup.of representative ⟨223, [(false, false)], 221⟩ :=
  holds_reverse edge700

theorem edge701 : Holds level0Subgroup PresentedGroup.of representative ⟨234, [(false, true)], 247⟩ :=
  special 234 247 (false, true) [(3, false), (0, false), (4, false), (0, false), (6, true)] LiftedRelations.word52
    true 119 (by decide +kernel) LiftedRelations.valid52

theorem edge701Inv : Holds level0Subgroup PresentedGroup.of representative ⟨247, [(false, false)], 234⟩ :=
  holds_reverse edge701

theorem edge702 : Holds level0Subgroup PresentedGroup.of representative ⟨266, [(true, true)], 284⟩ :=
  special 266 284 (true, true) [(3, true), (5, true), (3, true), (0, true), (5, true)] LiftedRelations.word104
    false 308 (by decide +kernel) LiftedRelations.valid104

theorem edge702Inv : Holds level0Subgroup PresentedGroup.of representative ⟨284, [(true, false)], 266⟩ :=
  holds_reverse edge702

theorem edge703 : Holds level0Subgroup PresentedGroup.of representative ⟨267, [(true, false)], 324⟩ :=
  special 267 324 (true, false) [(5, false), (4, true), (2, true), (3, false), (2, false), (3, false)] LiftedRelations.word80
    true 49 (by decide +kernel) LiftedRelations.valid80

theorem edge703Inv : Holds level0Subgroup PresentedGroup.of representative ⟨324, [(true, true)], 267⟩ :=
  holds_reverse edge703


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
