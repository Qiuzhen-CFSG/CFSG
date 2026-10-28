module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges05

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

theorem edge384 : Holds level0Subgroup PresentedGroup.of representative ⟨293, [(true, true)], 385⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge384Inv : Holds level0Subgroup PresentedGroup.of representative ⟨385, [(true, false)], 293⟩ :=
  holds_reverse edge384

theorem edge385 : Holds level0Subgroup PresentedGroup.of representative ⟨293, [(true, false)], 386⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge385Inv : Holds level0Subgroup PresentedGroup.of representative ⟨386, [(true, true)], 293⟩ :=
  holds_reverse edge385

theorem edge386 : Holds level0Subgroup PresentedGroup.of representative ⟨297, [(true, true)], 387⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge386Inv : Holds level0Subgroup PresentedGroup.of representative ⟨387, [(true, false)], 297⟩ :=
  holds_reverse edge386

theorem edge387 : Holds level0Subgroup PresentedGroup.of representative ⟨298, [(true, true)], 388⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge387Inv : Holds level0Subgroup PresentedGroup.of representative ⟨388, [(true, false)], 298⟩ :=
  holds_reverse edge387

theorem edge388 : Holds level0Subgroup PresentedGroup.of representative ⟨298, [(true, false)], 389⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge388Inv : Holds level0Subgroup PresentedGroup.of representative ⟨389, [(true, true)], 298⟩ :=
  holds_reverse edge388

theorem edge389 : Holds level0Subgroup PresentedGroup.of representative ⟨299, [(true, true)], 390⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge389Inv : Holds level0Subgroup PresentedGroup.of representative ⟨390, [(true, false)], 299⟩ :=
  holds_reverse edge389

theorem edge390 : Holds level0Subgroup PresentedGroup.of representative ⟨299, [(true, false)], 391⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge390Inv : Holds level0Subgroup PresentedGroup.of representative ⟨391, [(true, true)], 299⟩ :=
  holds_reverse edge390

theorem edge391 : Holds level0Subgroup PresentedGroup.of representative ⟨300, [(true, true)], 392⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge391Inv : Holds level0Subgroup PresentedGroup.of representative ⟨392, [(true, false)], 300⟩ :=
  holds_reverse edge391

theorem edge392 : Holds level0Subgroup PresentedGroup.of representative ⟨300, [(true, false)], 393⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge392Inv : Holds level0Subgroup PresentedGroup.of representative ⟨393, [(true, true)], 300⟩ :=
  holds_reverse edge392

theorem edge393 : Holds level0Subgroup PresentedGroup.of representative ⟨301, [(true, true)], 394⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge393Inv : Holds level0Subgroup PresentedGroup.of representative ⟨394, [(true, false)], 301⟩ :=
  holds_reverse edge393

theorem edge394 : Holds level0Subgroup PresentedGroup.of representative ⟨301, [(true, false)], 395⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge394Inv : Holds level0Subgroup PresentedGroup.of representative ⟨395, [(true, true)], 301⟩ :=
  holds_reverse edge394

theorem edge395 : Holds level0Subgroup PresentedGroup.of representative ⟨302, [(true, true)], 396⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge395Inv : Holds level0Subgroup PresentedGroup.of representative ⟨396, [(true, false)], 302⟩ :=
  holds_reverse edge395

theorem edge396 : Holds level0Subgroup PresentedGroup.of representative ⟨303, [(true, true)], 397⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge396Inv : Holds level0Subgroup PresentedGroup.of representative ⟨397, [(true, false)], 303⟩ :=
  holds_reverse edge396

theorem edge397 : Holds level0Subgroup PresentedGroup.of representative ⟨303, [(true, false)], 398⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge397Inv : Holds level0Subgroup PresentedGroup.of representative ⟨398, [(true, true)], 303⟩ :=
  holds_reverse edge397

theorem edge398 : Holds level0Subgroup PresentedGroup.of representative ⟨304, [(true, true)], 399⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge398Inv : Holds level0Subgroup PresentedGroup.of representative ⟨399, [(true, false)], 304⟩ :=
  holds_reverse edge398

theorem edge399 : Holds level0Subgroup PresentedGroup.of representative ⟨304, [(true, false)], 400⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge399Inv : Holds level0Subgroup PresentedGroup.of representative ⟨400, [(true, true)], 304⟩ :=
  holds_reverse edge399

theorem edge400 : Holds level0Subgroup PresentedGroup.of representative ⟨307, [(true, true)], 401⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge400Inv : Holds level0Subgroup PresentedGroup.of representative ⟨401, [(true, false)], 307⟩ :=
  holds_reverse edge400

theorem edge401 : Holds level0Subgroup PresentedGroup.of representative ⟨307, [(true, false)], 402⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge401Inv : Holds level0Subgroup PresentedGroup.of representative ⟨402, [(true, true)], 307⟩ :=
  holds_reverse edge401

theorem edge402 : Holds level0Subgroup PresentedGroup.of representative ⟨308, [(true, true)], 403⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge402Inv : Holds level0Subgroup PresentedGroup.of representative ⟨403, [(true, false)], 308⟩ :=
  holds_reverse edge402

theorem edge403 : Holds level0Subgroup PresentedGroup.of representative ⟨308, [(true, false)], 404⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge403Inv : Holds level0Subgroup PresentedGroup.of representative ⟨404, [(true, true)], 308⟩ :=
  holds_reverse edge403

theorem edge404 : Holds level0Subgroup PresentedGroup.of representative ⟨310, [(true, true)], 405⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge404Inv : Holds level0Subgroup PresentedGroup.of representative ⟨405, [(true, false)], 310⟩ :=
  holds_reverse edge404

theorem edge405 : Holds level0Subgroup PresentedGroup.of representative ⟨310, [(true, false)], 406⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge405Inv : Holds level0Subgroup PresentedGroup.of representative ⟨406, [(true, true)], 310⟩ :=
  holds_reverse edge405

theorem edge406 : Holds level0Subgroup PresentedGroup.of representative ⟨311, [(true, true)], 407⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge406Inv : Holds level0Subgroup PresentedGroup.of representative ⟨407, [(true, false)], 311⟩ :=
  holds_reverse edge406

theorem edge407 : Holds level0Subgroup PresentedGroup.of representative ⟨311, [(true, false)], 408⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge407Inv : Holds level0Subgroup PresentedGroup.of representative ⟨408, [(true, true)], 311⟩ :=
  holds_reverse edge407

theorem edge408 : Holds level0Subgroup PresentedGroup.of representative ⟨312, [(true, true)], 409⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge408Inv : Holds level0Subgroup PresentedGroup.of representative ⟨409, [(true, false)], 312⟩ :=
  holds_reverse edge408

theorem edge409 : Holds level0Subgroup PresentedGroup.of representative ⟨312, [(true, false)], 410⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge409Inv : Holds level0Subgroup PresentedGroup.of representative ⟨410, [(true, true)], 312⟩ :=
  holds_reverse edge409

theorem edge410 : Holds level0Subgroup PresentedGroup.of representative ⟨313, [(true, true)], 411⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge410Inv : Holds level0Subgroup PresentedGroup.of representative ⟨411, [(true, false)], 313⟩ :=
  holds_reverse edge410

theorem edge411 : Holds level0Subgroup PresentedGroup.of representative ⟨313, [(true, false)], 412⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge411Inv : Holds level0Subgroup PresentedGroup.of representative ⟨412, [(true, true)], 313⟩ :=
  holds_reverse edge411

theorem edge412 : Holds level0Subgroup PresentedGroup.of representative ⟨314, [(true, true)], 413⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge412Inv : Holds level0Subgroup PresentedGroup.of representative ⟨413, [(true, false)], 314⟩ :=
  holds_reverse edge412

theorem edge413 : Holds level0Subgroup PresentedGroup.of representative ⟨314, [(true, false)], 414⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge413Inv : Holds level0Subgroup PresentedGroup.of representative ⟨414, [(true, true)], 314⟩ :=
  holds_reverse edge413

theorem edge414 : Holds level0Subgroup PresentedGroup.of representative ⟨315, [(true, true)], 415⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge414Inv : Holds level0Subgroup PresentedGroup.of representative ⟨415, [(true, false)], 315⟩ :=
  holds_reverse edge414

theorem edge415 : Holds level0Subgroup PresentedGroup.of representative ⟨315, [(true, false)], 416⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge415Inv : Holds level0Subgroup PresentedGroup.of representative ⟨416, [(true, true)], 315⟩ :=
  holds_reverse edge415

theorem edge416 : Holds level0Subgroup PresentedGroup.of representative ⟨316, [(true, true)], 417⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge416Inv : Holds level0Subgroup PresentedGroup.of representative ⟨417, [(true, false)], 316⟩ :=
  holds_reverse edge416

theorem edge417 : Holds level0Subgroup PresentedGroup.of representative ⟨316, [(true, false)], 418⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge417Inv : Holds level0Subgroup PresentedGroup.of representative ⟨418, [(true, true)], 316⟩ :=
  holds_reverse edge417

theorem edge418 : Holds level0Subgroup PresentedGroup.of representative ⟨317, [(true, true)], 419⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge418Inv : Holds level0Subgroup PresentedGroup.of representative ⟨419, [(true, false)], 317⟩ :=
  holds_reverse edge418

theorem edge419 : Holds level0Subgroup PresentedGroup.of representative ⟨317, [(true, false)], 420⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge419Inv : Holds level0Subgroup PresentedGroup.of representative ⟨420, [(true, true)], 317⟩ :=
  holds_reverse edge419

theorem edge420 : Holds level0Subgroup PresentedGroup.of representative ⟨319, [(true, true)], 421⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge420Inv : Holds level0Subgroup PresentedGroup.of representative ⟨421, [(true, false)], 319⟩ :=
  holds_reverse edge420

theorem edge421 : Holds level0Subgroup PresentedGroup.of representative ⟨319, [(true, false)], 422⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge421Inv : Holds level0Subgroup PresentedGroup.of representative ⟨422, [(true, true)], 319⟩ :=
  holds_reverse edge421

theorem edge422 : Holds level0Subgroup PresentedGroup.of representative ⟨320, [(true, true)], 423⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge422Inv : Holds level0Subgroup PresentedGroup.of representative ⟨423, [(true, false)], 320⟩ :=
  holds_reverse edge422

theorem edge423 : Holds level0Subgroup PresentedGroup.of representative ⟨320, [(true, false)], 424⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge423Inv : Holds level0Subgroup PresentedGroup.of representative ⟨424, [(true, true)], 320⟩ :=
  holds_reverse edge423

theorem edge424 : Holds level0Subgroup PresentedGroup.of representative ⟨321, [(true, true)], 425⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge424Inv : Holds level0Subgroup PresentedGroup.of representative ⟨425, [(true, false)], 321⟩ :=
  holds_reverse edge424

theorem edge425 : Holds level0Subgroup PresentedGroup.of representative ⟨321, [(true, false)], 426⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge425Inv : Holds level0Subgroup PresentedGroup.of representative ⟨426, [(true, true)], 321⟩ :=
  holds_reverse edge425

theorem edge426 : Holds level0Subgroup PresentedGroup.of representative ⟨322, [(true, true)], 427⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge426Inv : Holds level0Subgroup PresentedGroup.of representative ⟨427, [(true, false)], 322⟩ :=
  holds_reverse edge426

theorem edge427 : Holds level0Subgroup PresentedGroup.of representative ⟨322, [(true, false)], 428⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge427Inv : Holds level0Subgroup PresentedGroup.of representative ⟨428, [(true, true)], 322⟩ :=
  holds_reverse edge427

theorem edge428 : Holds level0Subgroup PresentedGroup.of representative ⟨323, [(true, true)], 429⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge428Inv : Holds level0Subgroup PresentedGroup.of representative ⟨429, [(true, false)], 323⟩ :=
  holds_reverse edge428

theorem edge429 : Holds level0Subgroup PresentedGroup.of representative ⟨323, [(true, false)], 430⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge429Inv : Holds level0Subgroup PresentedGroup.of representative ⟨430, [(true, true)], 323⟩ :=
  holds_reverse edge429

theorem edge430 : Holds level0Subgroup PresentedGroup.of representative ⟨325, [(true, true)], 431⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge430Inv : Holds level0Subgroup PresentedGroup.of representative ⟨431, [(true, false)], 325⟩ :=
  holds_reverse edge430

theorem edge431 : Holds level0Subgroup PresentedGroup.of representative ⟨325, [(true, false)], 432⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge431Inv : Holds level0Subgroup PresentedGroup.of representative ⟨432, [(true, true)], 325⟩ :=
  holds_reverse edge431

theorem edge432 : Holds level0Subgroup PresentedGroup.of representative ⟨326, [(true, true)], 433⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge432Inv : Holds level0Subgroup PresentedGroup.of representative ⟨433, [(true, false)], 326⟩ :=
  holds_reverse edge432

theorem edge433 : Holds level0Subgroup PresentedGroup.of representative ⟨326, [(true, false)], 434⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge433Inv : Holds level0Subgroup PresentedGroup.of representative ⟨434, [(true, true)], 326⟩ :=
  holds_reverse edge433

theorem edge434 : Holds level0Subgroup PresentedGroup.of representative ⟨327, [(true, true)], 435⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge434Inv : Holds level0Subgroup PresentedGroup.of representative ⟨435, [(true, false)], 327⟩ :=
  holds_reverse edge434

theorem edge435 : Holds level0Subgroup PresentedGroup.of representative ⟨328, [(true, true)], 436⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge435Inv : Holds level0Subgroup PresentedGroup.of representative ⟨436, [(true, false)], 328⟩ :=
  holds_reverse edge435

theorem edge436 : Holds level0Subgroup PresentedGroup.of representative ⟨328, [(true, false)], 437⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge436Inv : Holds level0Subgroup PresentedGroup.of representative ⟨437, [(true, true)], 328⟩ :=
  holds_reverse edge436

theorem edge437 : Holds level0Subgroup PresentedGroup.of representative ⟨329, [(true, true)], 438⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge437Inv : Holds level0Subgroup PresentedGroup.of representative ⟨438, [(true, false)], 329⟩ :=
  holds_reverse edge437

theorem edge438 : Holds level0Subgroup PresentedGroup.of representative ⟨329, [(true, false)], 439⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge438Inv : Holds level0Subgroup PresentedGroup.of representative ⟨439, [(true, true)], 329⟩ :=
  holds_reverse edge438

theorem edge439 : Holds level0Subgroup PresentedGroup.of representative ⟨330, [(true, true)], 440⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge439Inv : Holds level0Subgroup PresentedGroup.of representative ⟨440, [(true, false)], 330⟩ :=
  holds_reverse edge439

theorem edge440 : Holds level0Subgroup PresentedGroup.of representative ⟨330, [(true, false)], 441⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge440Inv : Holds level0Subgroup PresentedGroup.of representative ⟨441, [(true, true)], 330⟩ :=
  holds_reverse edge440

theorem edge441 : Holds level0Subgroup PresentedGroup.of representative ⟨331, [(true, true)], 442⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge441Inv : Holds level0Subgroup PresentedGroup.of representative ⟨442, [(true, false)], 331⟩ :=
  holds_reverse edge441

theorem edge442 : Holds level0Subgroup PresentedGroup.of representative ⟨331, [(true, false)], 443⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge442Inv : Holds level0Subgroup PresentedGroup.of representative ⟨443, [(true, true)], 331⟩ :=
  holds_reverse edge442

theorem edge443 : Holds level0Subgroup PresentedGroup.of representative ⟨332, [(true, true)], 444⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge443Inv : Holds level0Subgroup PresentedGroup.of representative ⟨444, [(true, false)], 332⟩ :=
  holds_reverse edge443

theorem edge444 : Holds level0Subgroup PresentedGroup.of representative ⟨332, [(true, false)], 445⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge444Inv : Holds level0Subgroup PresentedGroup.of representative ⟨445, [(true, true)], 332⟩ :=
  holds_reverse edge444

theorem edge445 : Holds level0Subgroup PresentedGroup.of representative ⟨333, [(true, true)], 446⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge445Inv : Holds level0Subgroup PresentedGroup.of representative ⟨446, [(true, false)], 333⟩ :=
  holds_reverse edge445

theorem edge446 : Holds level0Subgroup PresentedGroup.of representative ⟨333, [(true, false)], 447⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge446Inv : Holds level0Subgroup PresentedGroup.of representative ⟨447, [(true, true)], 333⟩ :=
  holds_reverse edge446

theorem edge447 : Holds level0Subgroup PresentedGroup.of representative ⟨335, [(true, true)], 448⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge447Inv : Holds level0Subgroup PresentedGroup.of representative ⟨448, [(true, false)], 335⟩ :=
  holds_reverse edge447


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
