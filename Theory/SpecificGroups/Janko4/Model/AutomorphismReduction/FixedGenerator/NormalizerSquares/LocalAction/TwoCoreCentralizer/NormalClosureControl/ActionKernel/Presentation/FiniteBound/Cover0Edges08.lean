module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges07

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

theorem edge512 : Holds level0Subgroup PresentedGroup.of representative ⟨424, [(false, true)], 513⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge512Inv : Holds level0Subgroup PresentedGroup.of representative ⟨513, [(false, false)], 424⟩ :=
  holds_reverse edge512

theorem edge513 : Holds level0Subgroup PresentedGroup.of representative ⟨425, [(false, true)], 514⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge513Inv : Holds level0Subgroup PresentedGroup.of representative ⟨514, [(false, false)], 425⟩ :=
  holds_reverse edge513

theorem edge514 : Holds level0Subgroup PresentedGroup.of representative ⟨427, [(false, true)], 515⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge514Inv : Holds level0Subgroup PresentedGroup.of representative ⟨515, [(false, false)], 427⟩ :=
  holds_reverse edge514

theorem edge515 : Holds level0Subgroup PresentedGroup.of representative ⟨428, [(false, true)], 516⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge515Inv : Holds level0Subgroup PresentedGroup.of representative ⟨516, [(false, false)], 428⟩ :=
  holds_reverse edge515

theorem edge516 : Holds level0Subgroup PresentedGroup.of representative ⟨429, [(false, true)], 517⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge516Inv : Holds level0Subgroup PresentedGroup.of representative ⟨517, [(false, false)], 429⟩ :=
  holds_reverse edge516

theorem edge517 : Holds level0Subgroup PresentedGroup.of representative ⟨430, [(false, true)], 518⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge517Inv : Holds level0Subgroup PresentedGroup.of representative ⟨518, [(false, false)], 430⟩ :=
  holds_reverse edge517

theorem edge518 : Holds level0Subgroup PresentedGroup.of representative ⟨431, [(false, true)], 519⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge518Inv : Holds level0Subgroup PresentedGroup.of representative ⟨519, [(false, false)], 431⟩ :=
  holds_reverse edge518

theorem edge519 : Holds level0Subgroup PresentedGroup.of representative ⟨435, [(false, true)], 520⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge519Inv : Holds level0Subgroup PresentedGroup.of representative ⟨520, [(false, false)], 435⟩ :=
  holds_reverse edge519

theorem edge520 : Holds level0Subgroup PresentedGroup.of representative ⟨436, [(false, true)], 521⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge520Inv : Holds level0Subgroup PresentedGroup.of representative ⟨521, [(false, false)], 436⟩ :=
  holds_reverse edge520

theorem edge521 : Holds level0Subgroup PresentedGroup.of representative ⟨438, [(false, true)], 522⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge521Inv : Holds level0Subgroup PresentedGroup.of representative ⟨522, [(false, false)], 438⟩ :=
  holds_reverse edge521

theorem edge522 : Holds level0Subgroup PresentedGroup.of representative ⟨441, [(false, true)], 523⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge522Inv : Holds level0Subgroup PresentedGroup.of representative ⟨523, [(false, false)], 441⟩ :=
  holds_reverse edge522

theorem edge523 : Holds level0Subgroup PresentedGroup.of representative ⟨443, [(false, true)], 524⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge523Inv : Holds level0Subgroup PresentedGroup.of representative ⟨524, [(false, false)], 443⟩ :=
  holds_reverse edge523

theorem edge524 : Holds level0Subgroup PresentedGroup.of representative ⟨444, [(false, true)], 525⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge524Inv : Holds level0Subgroup PresentedGroup.of representative ⟨525, [(false, false)], 444⟩ :=
  holds_reverse edge524

theorem edge525 : Holds level0Subgroup PresentedGroup.of representative ⟨445, [(false, true)], 526⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge525Inv : Holds level0Subgroup PresentedGroup.of representative ⟨526, [(false, false)], 445⟩ :=
  holds_reverse edge525

theorem edge526 : Holds level0Subgroup PresentedGroup.of representative ⟨446, [(false, true)], 527⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge526Inv : Holds level0Subgroup PresentedGroup.of representative ⟨527, [(false, false)], 446⟩ :=
  holds_reverse edge526

theorem edge527 : Holds level0Subgroup PresentedGroup.of representative ⟨448, [(false, true)], 528⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge527Inv : Holds level0Subgroup PresentedGroup.of representative ⟨528, [(false, false)], 448⟩ :=
  holds_reverse edge527

theorem edge528 : Holds level0Subgroup PresentedGroup.of representative ⟨449, [(false, true)], 529⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge528Inv : Holds level0Subgroup PresentedGroup.of representative ⟨529, [(false, false)], 449⟩ :=
  holds_reverse edge528

theorem edge529 : Holds level0Subgroup PresentedGroup.of representative ⟨450, [(false, true)], 530⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge529Inv : Holds level0Subgroup PresentedGroup.of representative ⟨530, [(false, false)], 450⟩ :=
  holds_reverse edge529

theorem edge530 : Holds level0Subgroup PresentedGroup.of representative ⟨451, [(false, true)], 531⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge530Inv : Holds level0Subgroup PresentedGroup.of representative ⟨531, [(false, false)], 451⟩ :=
  holds_reverse edge530

theorem edge531 : Holds level0Subgroup PresentedGroup.of representative ⟨452, [(true, true)], 532⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge531Inv : Holds level0Subgroup PresentedGroup.of representative ⟨532, [(true, false)], 452⟩ :=
  holds_reverse edge531

theorem edge532 : Holds level0Subgroup PresentedGroup.of representative ⟨453, [(true, true)], 533⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge532Inv : Holds level0Subgroup PresentedGroup.of representative ⟨533, [(true, false)], 453⟩ :=
  holds_reverse edge532

theorem edge533 : Holds level0Subgroup PresentedGroup.of representative ⟨453, [(true, false)], 534⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge533Inv : Holds level0Subgroup PresentedGroup.of representative ⟨534, [(true, true)], 453⟩ :=
  holds_reverse edge533

theorem edge534 : Holds level0Subgroup PresentedGroup.of representative ⟨454, [(true, true)], 535⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge534Inv : Holds level0Subgroup PresentedGroup.of representative ⟨535, [(true, false)], 454⟩ :=
  holds_reverse edge534

theorem edge535 : Holds level0Subgroup PresentedGroup.of representative ⟨454, [(true, false)], 536⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge535Inv : Holds level0Subgroup PresentedGroup.of representative ⟨536, [(true, true)], 454⟩ :=
  holds_reverse edge535

theorem edge536 : Holds level0Subgroup PresentedGroup.of representative ⟨455, [(true, true)], 537⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge536Inv : Holds level0Subgroup PresentedGroup.of representative ⟨537, [(true, false)], 455⟩ :=
  holds_reverse edge536

theorem edge537 : Holds level0Subgroup PresentedGroup.of representative ⟨455, [(true, false)], 538⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge537Inv : Holds level0Subgroup PresentedGroup.of representative ⟨538, [(true, true)], 455⟩ :=
  holds_reverse edge537

theorem edge538 : Holds level0Subgroup PresentedGroup.of representative ⟨457, [(true, true)], 539⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge538Inv : Holds level0Subgroup PresentedGroup.of representative ⟨539, [(true, false)], 457⟩ :=
  holds_reverse edge538

theorem edge539 : Holds level0Subgroup PresentedGroup.of representative ⟨458, [(true, false)], 540⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge539Inv : Holds level0Subgroup PresentedGroup.of representative ⟨540, [(true, true)], 458⟩ :=
  holds_reverse edge539

theorem edge540 : Holds level0Subgroup PresentedGroup.of representative ⟨459, [(true, false)], 541⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge540Inv : Holds level0Subgroup PresentedGroup.of representative ⟨541, [(true, true)], 459⟩ :=
  holds_reverse edge540

theorem edge541 : Holds level0Subgroup PresentedGroup.of representative ⟨460, [(true, true)], 542⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge541Inv : Holds level0Subgroup PresentedGroup.of representative ⟨542, [(true, false)], 460⟩ :=
  holds_reverse edge541

theorem edge542 : Holds level0Subgroup PresentedGroup.of representative ⟨461, [(true, true)], 543⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge542Inv : Holds level0Subgroup PresentedGroup.of representative ⟨543, [(true, false)], 461⟩ :=
  holds_reverse edge542

theorem edge543 : Holds level0Subgroup PresentedGroup.of representative ⟨463, [(true, true)], 544⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge543Inv : Holds level0Subgroup PresentedGroup.of representative ⟨544, [(true, false)], 463⟩ :=
  holds_reverse edge543

theorem edge544 : Holds level0Subgroup PresentedGroup.of representative ⟨465, [(true, false)], 545⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge544Inv : Holds level0Subgroup PresentedGroup.of representative ⟨545, [(true, true)], 465⟩ :=
  holds_reverse edge544

theorem edge545 : Holds level0Subgroup PresentedGroup.of representative ⟨466, [(true, true)], 546⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge545Inv : Holds level0Subgroup PresentedGroup.of representative ⟨546, [(true, false)], 466⟩ :=
  holds_reverse edge545

theorem edge546 : Holds level0Subgroup PresentedGroup.of representative ⟨466, [(true, false)], 547⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge546Inv : Holds level0Subgroup PresentedGroup.of representative ⟨547, [(true, true)], 466⟩ :=
  holds_reverse edge546

theorem edge547 : Holds level0Subgroup PresentedGroup.of representative ⟨467, [(true, false)], 548⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge547Inv : Holds level0Subgroup PresentedGroup.of representative ⟨548, [(true, true)], 467⟩ :=
  holds_reverse edge547

theorem edge548 : Holds level0Subgroup PresentedGroup.of representative ⟨469, [(true, true)], 549⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge548Inv : Holds level0Subgroup PresentedGroup.of representative ⟨549, [(true, false)], 469⟩ :=
  holds_reverse edge548

theorem edge549 : Holds level0Subgroup PresentedGroup.of representative ⟨469, [(true, false)], 550⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge549Inv : Holds level0Subgroup PresentedGroup.of representative ⟨550, [(true, true)], 469⟩ :=
  holds_reverse edge549

theorem edge550 : Holds level0Subgroup PresentedGroup.of representative ⟨470, [(true, true)], 551⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge550Inv : Holds level0Subgroup PresentedGroup.of representative ⟨551, [(true, false)], 470⟩ :=
  holds_reverse edge550

theorem edge551 : Holds level0Subgroup PresentedGroup.of representative ⟨471, [(true, false)], 552⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge551Inv : Holds level0Subgroup PresentedGroup.of representative ⟨552, [(true, true)], 471⟩ :=
  holds_reverse edge551

theorem edge552 : Holds level0Subgroup PresentedGroup.of representative ⟨472, [(true, true)], 553⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge552Inv : Holds level0Subgroup PresentedGroup.of representative ⟨553, [(true, false)], 472⟩ :=
  holds_reverse edge552

theorem edge553 : Holds level0Subgroup PresentedGroup.of representative ⟨472, [(true, false)], 554⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge553Inv : Holds level0Subgroup PresentedGroup.of representative ⟨554, [(true, true)], 472⟩ :=
  holds_reverse edge553

theorem edge554 : Holds level0Subgroup PresentedGroup.of representative ⟨473, [(true, true)], 555⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge554Inv : Holds level0Subgroup PresentedGroup.of representative ⟨555, [(true, false)], 473⟩ :=
  holds_reverse edge554

theorem edge555 : Holds level0Subgroup PresentedGroup.of representative ⟨473, [(true, false)], 556⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge555Inv : Holds level0Subgroup PresentedGroup.of representative ⟨556, [(true, true)], 473⟩ :=
  holds_reverse edge555

theorem edge556 : Holds level0Subgroup PresentedGroup.of representative ⟨474, [(true, true)], 557⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge556Inv : Holds level0Subgroup PresentedGroup.of representative ⟨557, [(true, false)], 474⟩ :=
  holds_reverse edge556

theorem edge557 : Holds level0Subgroup PresentedGroup.of representative ⟨474, [(true, false)], 558⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge557Inv : Holds level0Subgroup PresentedGroup.of representative ⟨558, [(true, true)], 474⟩ :=
  holds_reverse edge557

theorem edge558 : Holds level0Subgroup PresentedGroup.of representative ⟨475, [(true, true)], 559⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge558Inv : Holds level0Subgroup PresentedGroup.of representative ⟨559, [(true, false)], 475⟩ :=
  holds_reverse edge558

theorem edge559 : Holds level0Subgroup PresentedGroup.of representative ⟨475, [(true, false)], 560⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge559Inv : Holds level0Subgroup PresentedGroup.of representative ⟨560, [(true, true)], 475⟩ :=
  holds_reverse edge559

theorem edge560 : Holds level0Subgroup PresentedGroup.of representative ⟨476, [(true, true)], 561⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge560Inv : Holds level0Subgroup PresentedGroup.of representative ⟨561, [(true, false)], 476⟩ :=
  holds_reverse edge560

theorem edge561 : Holds level0Subgroup PresentedGroup.of representative ⟨477, [(true, true)], 562⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge561Inv : Holds level0Subgroup PresentedGroup.of representative ⟨562, [(true, false)], 477⟩ :=
  holds_reverse edge561

theorem edge562 : Holds level0Subgroup PresentedGroup.of representative ⟨477, [(true, false)], 563⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge562Inv : Holds level0Subgroup PresentedGroup.of representative ⟨563, [(true, true)], 477⟩ :=
  holds_reverse edge562

theorem edge563 : Holds level0Subgroup PresentedGroup.of representative ⟨479, [(true, true)], 564⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge563Inv : Holds level0Subgroup PresentedGroup.of representative ⟨564, [(true, false)], 479⟩ :=
  holds_reverse edge563

theorem edge564 : Holds level0Subgroup PresentedGroup.of representative ⟨479, [(true, false)], 565⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge564Inv : Holds level0Subgroup PresentedGroup.of representative ⟨565, [(true, true)], 479⟩ :=
  holds_reverse edge564

theorem edge565 : Holds level0Subgroup PresentedGroup.of representative ⟨480, [(true, true)], 566⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge565Inv : Holds level0Subgroup PresentedGroup.of representative ⟨566, [(true, false)], 480⟩ :=
  holds_reverse edge565

theorem edge566 : Holds level0Subgroup PresentedGroup.of representative ⟨480, [(true, false)], 567⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge566Inv : Holds level0Subgroup PresentedGroup.of representative ⟨567, [(true, true)], 480⟩ :=
  holds_reverse edge566

theorem edge567 : Holds level0Subgroup PresentedGroup.of representative ⟨481, [(true, true)], 568⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge567Inv : Holds level0Subgroup PresentedGroup.of representative ⟨568, [(true, false)], 481⟩ :=
  holds_reverse edge567

theorem edge568 : Holds level0Subgroup PresentedGroup.of representative ⟨481, [(true, false)], 569⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge568Inv : Holds level0Subgroup PresentedGroup.of representative ⟨569, [(true, true)], 481⟩ :=
  holds_reverse edge568

theorem edge569 : Holds level0Subgroup PresentedGroup.of representative ⟨484, [(true, true)], 570⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge569Inv : Holds level0Subgroup PresentedGroup.of representative ⟨570, [(true, false)], 484⟩ :=
  holds_reverse edge569

theorem edge570 : Holds level0Subgroup PresentedGroup.of representative ⟨484, [(true, false)], 571⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge570Inv : Holds level0Subgroup PresentedGroup.of representative ⟨571, [(true, true)], 484⟩ :=
  holds_reverse edge570

theorem edge571 : Holds level0Subgroup PresentedGroup.of representative ⟨485, [(true, false)], 572⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge571Inv : Holds level0Subgroup PresentedGroup.of representative ⟨572, [(true, true)], 485⟩ :=
  holds_reverse edge571

theorem edge572 : Holds level0Subgroup PresentedGroup.of representative ⟨486, [(true, false)], 573⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge572Inv : Holds level0Subgroup PresentedGroup.of representative ⟨573, [(true, true)], 486⟩ :=
  holds_reverse edge572

theorem edge573 : Holds level0Subgroup PresentedGroup.of representative ⟨489, [(true, true)], 574⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge573Inv : Holds level0Subgroup PresentedGroup.of representative ⟨574, [(true, false)], 489⟩ :=
  holds_reverse edge573

theorem edge574 : Holds level0Subgroup PresentedGroup.of representative ⟨489, [(true, false)], 575⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge574Inv : Holds level0Subgroup PresentedGroup.of representative ⟨575, [(true, true)], 489⟩ :=
  holds_reverse edge574

theorem edge575 : Holds level0Subgroup PresentedGroup.of representative ⟨490, [(true, true)], 576⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge575Inv : Holds level0Subgroup PresentedGroup.of representative ⟨576, [(true, false)], 490⟩ :=
  holds_reverse edge575


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
