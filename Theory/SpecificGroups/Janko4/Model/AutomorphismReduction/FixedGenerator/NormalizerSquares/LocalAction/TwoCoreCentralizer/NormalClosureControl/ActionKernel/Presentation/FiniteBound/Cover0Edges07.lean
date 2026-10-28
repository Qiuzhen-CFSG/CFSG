module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges06

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

theorem edge448 : Holds level0Subgroup PresentedGroup.of representative ⟨335, [(true, false)], 449⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge448Inv : Holds level0Subgroup PresentedGroup.of representative ⟨449, [(true, true)], 335⟩ :=
  holds_reverse edge448

theorem edge449 : Holds level0Subgroup PresentedGroup.of representative ⟨338, [(true, true)], 450⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge449Inv : Holds level0Subgroup PresentedGroup.of representative ⟨450, [(true, false)], 338⟩ :=
  holds_reverse edge449

theorem edge450 : Holds level0Subgroup PresentedGroup.of representative ⟨338, [(true, false)], 451⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge450Inv : Holds level0Subgroup PresentedGroup.of representative ⟨451, [(true, true)], 338⟩ :=
  holds_reverse edge450

theorem edge451 : Holds level0Subgroup PresentedGroup.of representative ⟨339, [(false, true)], 452⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge451Inv : Holds level0Subgroup PresentedGroup.of representative ⟨452, [(false, false)], 339⟩ :=
  holds_reverse edge451

theorem edge452 : Holds level0Subgroup PresentedGroup.of representative ⟨340, [(false, true)], 453⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge452Inv : Holds level0Subgroup PresentedGroup.of representative ⟨453, [(false, false)], 340⟩ :=
  holds_reverse edge452

theorem edge453 : Holds level0Subgroup PresentedGroup.of representative ⟨341, [(false, true)], 454⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge453Inv : Holds level0Subgroup PresentedGroup.of representative ⟨454, [(false, false)], 341⟩ :=
  holds_reverse edge453

theorem edge454 : Holds level0Subgroup PresentedGroup.of representative ⟨342, [(false, true)], 455⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge454Inv : Holds level0Subgroup PresentedGroup.of representative ⟨455, [(false, false)], 342⟩ :=
  holds_reverse edge454

theorem edge455 : Holds level0Subgroup PresentedGroup.of representative ⟨344, [(false, true)], 456⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge455Inv : Holds level0Subgroup PresentedGroup.of representative ⟨456, [(false, false)], 344⟩ :=
  holds_reverse edge455

theorem edge456 : Holds level0Subgroup PresentedGroup.of representative ⟨346, [(false, true)], 457⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge456Inv : Holds level0Subgroup PresentedGroup.of representative ⟨457, [(false, false)], 346⟩ :=
  holds_reverse edge456

theorem edge457 : Holds level0Subgroup PresentedGroup.of representative ⟨347, [(false, true)], 458⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge457Inv : Holds level0Subgroup PresentedGroup.of representative ⟨458, [(false, false)], 347⟩ :=
  holds_reverse edge457

theorem edge458 : Holds level0Subgroup PresentedGroup.of representative ⟨348, [(false, true)], 459⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge458Inv : Holds level0Subgroup PresentedGroup.of representative ⟨459, [(false, false)], 348⟩ :=
  holds_reverse edge458

theorem edge459 : Holds level0Subgroup PresentedGroup.of representative ⟨350, [(false, true)], 460⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge459Inv : Holds level0Subgroup PresentedGroup.of representative ⟨460, [(false, false)], 350⟩ :=
  holds_reverse edge459

theorem edge460 : Holds level0Subgroup PresentedGroup.of representative ⟨351, [(false, true)], 461⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge460Inv : Holds level0Subgroup PresentedGroup.of representative ⟨461, [(false, false)], 351⟩ :=
  holds_reverse edge460

theorem edge461 : Holds level0Subgroup PresentedGroup.of representative ⟨352, [(false, true)], 462⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge461Inv : Holds level0Subgroup PresentedGroup.of representative ⟨462, [(false, false)], 352⟩ :=
  holds_reverse edge461

theorem edge462 : Holds level0Subgroup PresentedGroup.of representative ⟨355, [(false, true)], 463⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge462Inv : Holds level0Subgroup PresentedGroup.of representative ⟨463, [(false, false)], 355⟩ :=
  holds_reverse edge462

theorem edge463 : Holds level0Subgroup PresentedGroup.of representative ⟨356, [(false, true)], 464⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge463Inv : Holds level0Subgroup PresentedGroup.of representative ⟨464, [(false, false)], 356⟩ :=
  holds_reverse edge463

theorem edge464 : Holds level0Subgroup PresentedGroup.of representative ⟨357, [(false, true)], 465⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge464Inv : Holds level0Subgroup PresentedGroup.of representative ⟨465, [(false, false)], 357⟩ :=
  holds_reverse edge464

theorem edge465 : Holds level0Subgroup PresentedGroup.of representative ⟨358, [(false, true)], 466⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge465Inv : Holds level0Subgroup PresentedGroup.of representative ⟨466, [(false, false)], 358⟩ :=
  holds_reverse edge465

theorem edge466 : Holds level0Subgroup PresentedGroup.of representative ⟨359, [(false, true)], 467⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge466Inv : Holds level0Subgroup PresentedGroup.of representative ⟨467, [(false, false)], 359⟩ :=
  holds_reverse edge466

theorem edge467 : Holds level0Subgroup PresentedGroup.of representative ⟨360, [(false, true)], 468⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge467Inv : Holds level0Subgroup PresentedGroup.of representative ⟨468, [(false, false)], 360⟩ :=
  holds_reverse edge467

theorem edge468 : Holds level0Subgroup PresentedGroup.of representative ⟨361, [(false, true)], 469⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge468Inv : Holds level0Subgroup PresentedGroup.of representative ⟨469, [(false, false)], 361⟩ :=
  holds_reverse edge468

theorem edge469 : Holds level0Subgroup PresentedGroup.of representative ⟨362, [(false, true)], 470⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge469Inv : Holds level0Subgroup PresentedGroup.of representative ⟨470, [(false, false)], 362⟩ :=
  holds_reverse edge469

theorem edge470 : Holds level0Subgroup PresentedGroup.of representative ⟨363, [(false, true)], 471⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge470Inv : Holds level0Subgroup PresentedGroup.of representative ⟨471, [(false, false)], 363⟩ :=
  holds_reverse edge470

theorem edge471 : Holds level0Subgroup PresentedGroup.of representative ⟨364, [(false, true)], 472⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge471Inv : Holds level0Subgroup PresentedGroup.of representative ⟨472, [(false, false)], 364⟩ :=
  holds_reverse edge471

theorem edge472 : Holds level0Subgroup PresentedGroup.of representative ⟨365, [(false, true)], 473⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge472Inv : Holds level0Subgroup PresentedGroup.of representative ⟨473, [(false, false)], 365⟩ :=
  holds_reverse edge472

theorem edge473 : Holds level0Subgroup PresentedGroup.of representative ⟨366, [(false, true)], 474⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge473Inv : Holds level0Subgroup PresentedGroup.of representative ⟨474, [(false, false)], 366⟩ :=
  holds_reverse edge473

theorem edge474 : Holds level0Subgroup PresentedGroup.of representative ⟨367, [(false, true)], 475⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge474Inv : Holds level0Subgroup PresentedGroup.of representative ⟨475, [(false, false)], 367⟩ :=
  holds_reverse edge474

theorem edge475 : Holds level0Subgroup PresentedGroup.of representative ⟨368, [(false, true)], 476⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge475Inv : Holds level0Subgroup PresentedGroup.of representative ⟨476, [(false, false)], 368⟩ :=
  holds_reverse edge475

theorem edge476 : Holds level0Subgroup PresentedGroup.of representative ⟨369, [(false, true)], 477⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge476Inv : Holds level0Subgroup PresentedGroup.of representative ⟨477, [(false, false)], 369⟩ :=
  holds_reverse edge476

theorem edge477 : Holds level0Subgroup PresentedGroup.of representative ⟨370, [(false, true)], 478⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge477Inv : Holds level0Subgroup PresentedGroup.of representative ⟨478, [(false, false)], 370⟩ :=
  holds_reverse edge477

theorem edge478 : Holds level0Subgroup PresentedGroup.of representative ⟨372, [(false, true)], 479⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge478Inv : Holds level0Subgroup PresentedGroup.of representative ⟨479, [(false, false)], 372⟩ :=
  holds_reverse edge478

theorem edge479 : Holds level0Subgroup PresentedGroup.of representative ⟨373, [(false, true)], 480⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge479Inv : Holds level0Subgroup PresentedGroup.of representative ⟨480, [(false, false)], 373⟩ :=
  holds_reverse edge479

theorem edge480 : Holds level0Subgroup PresentedGroup.of representative ⟨374, [(false, true)], 481⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge480Inv : Holds level0Subgroup PresentedGroup.of representative ⟨481, [(false, false)], 374⟩ :=
  holds_reverse edge480

theorem edge481 : Holds level0Subgroup PresentedGroup.of representative ⟨375, [(false, true)], 482⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge481Inv : Holds level0Subgroup PresentedGroup.of representative ⟨482, [(false, false)], 375⟩ :=
  holds_reverse edge481

theorem edge482 : Holds level0Subgroup PresentedGroup.of representative ⟨377, [(false, true)], 483⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge482Inv : Holds level0Subgroup PresentedGroup.of representative ⟨483, [(false, false)], 377⟩ :=
  holds_reverse edge482

theorem edge483 : Holds level0Subgroup PresentedGroup.of representative ⟨378, [(false, true)], 484⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge483Inv : Holds level0Subgroup PresentedGroup.of representative ⟨484, [(false, false)], 378⟩ :=
  holds_reverse edge483

theorem edge484 : Holds level0Subgroup PresentedGroup.of representative ⟨380, [(false, true)], 485⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge484Inv : Holds level0Subgroup PresentedGroup.of representative ⟨485, [(false, false)], 380⟩ :=
  holds_reverse edge484

theorem edge485 : Holds level0Subgroup PresentedGroup.of representative ⟨381, [(false, true)], 486⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge485Inv : Holds level0Subgroup PresentedGroup.of representative ⟨486, [(false, false)], 381⟩ :=
  holds_reverse edge485

theorem edge486 : Holds level0Subgroup PresentedGroup.of representative ⟨383, [(false, true)], 487⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge486Inv : Holds level0Subgroup PresentedGroup.of representative ⟨487, [(false, false)], 383⟩ :=
  holds_reverse edge486

theorem edge487 : Holds level0Subgroup PresentedGroup.of representative ⟨389, [(false, true)], 488⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge487Inv : Holds level0Subgroup PresentedGroup.of representative ⟨488, [(false, false)], 389⟩ :=
  holds_reverse edge487

theorem edge488 : Holds level0Subgroup PresentedGroup.of representative ⟨390, [(false, true)], 489⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge488Inv : Holds level0Subgroup PresentedGroup.of representative ⟨489, [(false, false)], 390⟩ :=
  holds_reverse edge488

theorem edge489 : Holds level0Subgroup PresentedGroup.of representative ⟨391, [(false, true)], 490⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge489Inv : Holds level0Subgroup PresentedGroup.of representative ⟨490, [(false, false)], 391⟩ :=
  holds_reverse edge489

theorem edge490 : Holds level0Subgroup PresentedGroup.of representative ⟨393, [(false, true)], 491⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge490Inv : Holds level0Subgroup PresentedGroup.of representative ⟨491, [(false, false)], 393⟩ :=
  holds_reverse edge490

theorem edge491 : Holds level0Subgroup PresentedGroup.of representative ⟨394, [(false, true)], 492⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge491Inv : Holds level0Subgroup PresentedGroup.of representative ⟨492, [(false, false)], 394⟩ :=
  holds_reverse edge491

theorem edge492 : Holds level0Subgroup PresentedGroup.of representative ⟨395, [(false, true)], 493⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge492Inv : Holds level0Subgroup PresentedGroup.of representative ⟨493, [(false, false)], 395⟩ :=
  holds_reverse edge492

theorem edge493 : Holds level0Subgroup PresentedGroup.of representative ⟨396, [(false, true)], 494⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge493Inv : Holds level0Subgroup PresentedGroup.of representative ⟨494, [(false, false)], 396⟩ :=
  holds_reverse edge493

theorem edge494 : Holds level0Subgroup PresentedGroup.of representative ⟨397, [(false, true)], 495⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge494Inv : Holds level0Subgroup PresentedGroup.of representative ⟨495, [(false, false)], 397⟩ :=
  holds_reverse edge494

theorem edge495 : Holds level0Subgroup PresentedGroup.of representative ⟨399, [(false, true)], 496⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge495Inv : Holds level0Subgroup PresentedGroup.of representative ⟨496, [(false, false)], 399⟩ :=
  holds_reverse edge495

theorem edge496 : Holds level0Subgroup PresentedGroup.of representative ⟨400, [(false, true)], 497⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge496Inv : Holds level0Subgroup PresentedGroup.of representative ⟨497, [(false, false)], 400⟩ :=
  holds_reverse edge496

theorem edge497 : Holds level0Subgroup PresentedGroup.of representative ⟨401, [(false, true)], 498⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge497Inv : Holds level0Subgroup PresentedGroup.of representative ⟨498, [(false, false)], 401⟩ :=
  holds_reverse edge497

theorem edge498 : Holds level0Subgroup PresentedGroup.of representative ⟨402, [(false, true)], 499⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge498Inv : Holds level0Subgroup PresentedGroup.of representative ⟨499, [(false, false)], 402⟩ :=
  holds_reverse edge498

theorem edge499 : Holds level0Subgroup PresentedGroup.of representative ⟨403, [(false, true)], 500⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge499Inv : Holds level0Subgroup PresentedGroup.of representative ⟨500, [(false, false)], 403⟩ :=
  holds_reverse edge499

theorem edge500 : Holds level0Subgroup PresentedGroup.of representative ⟨405, [(false, true)], 501⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge500Inv : Holds level0Subgroup PresentedGroup.of representative ⟨501, [(false, false)], 405⟩ :=
  holds_reverse edge500

theorem edge501 : Holds level0Subgroup PresentedGroup.of representative ⟨409, [(false, true)], 502⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge501Inv : Holds level0Subgroup PresentedGroup.of representative ⟨502, [(false, false)], 409⟩ :=
  holds_reverse edge501

theorem edge502 : Holds level0Subgroup PresentedGroup.of representative ⟨410, [(false, true)], 503⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge502Inv : Holds level0Subgroup PresentedGroup.of representative ⟨503, [(false, false)], 410⟩ :=
  holds_reverse edge502

theorem edge503 : Holds level0Subgroup PresentedGroup.of representative ⟨411, [(false, true)], 504⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge503Inv : Holds level0Subgroup PresentedGroup.of representative ⟨504, [(false, false)], 411⟩ :=
  holds_reverse edge503

theorem edge504 : Holds level0Subgroup PresentedGroup.of representative ⟨412, [(false, true)], 505⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge504Inv : Holds level0Subgroup PresentedGroup.of representative ⟨505, [(false, false)], 412⟩ :=
  holds_reverse edge504

theorem edge505 : Holds level0Subgroup PresentedGroup.of representative ⟨413, [(false, true)], 506⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge505Inv : Holds level0Subgroup PresentedGroup.of representative ⟨506, [(false, false)], 413⟩ :=
  holds_reverse edge505

theorem edge506 : Holds level0Subgroup PresentedGroup.of representative ⟨414, [(false, true)], 507⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge506Inv : Holds level0Subgroup PresentedGroup.of representative ⟨507, [(false, false)], 414⟩ :=
  holds_reverse edge506

theorem edge507 : Holds level0Subgroup PresentedGroup.of representative ⟨415, [(false, true)], 508⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge507Inv : Holds level0Subgroup PresentedGroup.of representative ⟨508, [(false, false)], 415⟩ :=
  holds_reverse edge507

theorem edge508 : Holds level0Subgroup PresentedGroup.of representative ⟨417, [(false, true)], 509⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge508Inv : Holds level0Subgroup PresentedGroup.of representative ⟨509, [(false, false)], 417⟩ :=
  holds_reverse edge508

theorem edge509 : Holds level0Subgroup PresentedGroup.of representative ⟨419, [(false, true)], 510⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge509Inv : Holds level0Subgroup PresentedGroup.of representative ⟨510, [(false, false)], 419⟩ :=
  holds_reverse edge509

theorem edge510 : Holds level0Subgroup PresentedGroup.of representative ⟨420, [(false, true)], 511⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge510Inv : Holds level0Subgroup PresentedGroup.of representative ⟨511, [(false, false)], 420⟩ :=
  holds_reverse edge510

theorem edge511 : Holds level0Subgroup PresentedGroup.of representative ⟨422, [(false, true)], 512⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge511Inv : Holds level0Subgroup PresentedGroup.of representative ⟨512, [(false, false)], 422⟩ :=
  holds_reverse edge511


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
