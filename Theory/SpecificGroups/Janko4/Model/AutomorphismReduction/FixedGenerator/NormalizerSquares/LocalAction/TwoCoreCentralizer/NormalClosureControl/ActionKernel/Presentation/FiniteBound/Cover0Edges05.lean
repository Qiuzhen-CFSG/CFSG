module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges04

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

theorem edge320 : Holds level0Subgroup PresentedGroup.of representative ⟨246, [(false, true)], 321⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge320Inv : Holds level0Subgroup PresentedGroup.of representative ⟨321, [(false, false)], 246⟩ :=
  holds_reverse edge320

theorem edge321 : Holds level0Subgroup PresentedGroup.of representative ⟨248, [(false, true)], 322⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge321Inv : Holds level0Subgroup PresentedGroup.of representative ⟨322, [(false, false)], 248⟩ :=
  holds_reverse edge321

theorem edge322 : Holds level0Subgroup PresentedGroup.of representative ⟨249, [(false, true)], 323⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge322Inv : Holds level0Subgroup PresentedGroup.of representative ⟨323, [(false, false)], 249⟩ :=
  holds_reverse edge322

theorem edge323 : Holds level0Subgroup PresentedGroup.of representative ⟨250, [(false, true)], 324⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge323Inv : Holds level0Subgroup PresentedGroup.of representative ⟨324, [(false, false)], 250⟩ :=
  holds_reverse edge323

theorem edge324 : Holds level0Subgroup PresentedGroup.of representative ⟨251, [(false, true)], 325⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge324Inv : Holds level0Subgroup PresentedGroup.of representative ⟨325, [(false, false)], 251⟩ :=
  holds_reverse edge324

theorem edge325 : Holds level0Subgroup PresentedGroup.of representative ⟨252, [(false, true)], 326⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge325Inv : Holds level0Subgroup PresentedGroup.of representative ⟨326, [(false, false)], 252⟩ :=
  holds_reverse edge325

theorem edge326 : Holds level0Subgroup PresentedGroup.of representative ⟨253, [(false, true)], 327⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge326Inv : Holds level0Subgroup PresentedGroup.of representative ⟨327, [(false, false)], 253⟩ :=
  holds_reverse edge326

theorem edge327 : Holds level0Subgroup PresentedGroup.of representative ⟨254, [(false, true)], 328⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge327Inv : Holds level0Subgroup PresentedGroup.of representative ⟨328, [(false, false)], 254⟩ :=
  holds_reverse edge327

theorem edge328 : Holds level0Subgroup PresentedGroup.of representative ⟨255, [(false, true)], 329⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge328Inv : Holds level0Subgroup PresentedGroup.of representative ⟨329, [(false, false)], 255⟩ :=
  holds_reverse edge328

theorem edge329 : Holds level0Subgroup PresentedGroup.of representative ⟨256, [(false, true)], 330⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge329Inv : Holds level0Subgroup PresentedGroup.of representative ⟨330, [(false, false)], 256⟩ :=
  holds_reverse edge329

theorem edge330 : Holds level0Subgroup PresentedGroup.of representative ⟨257, [(false, true)], 331⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge330Inv : Holds level0Subgroup PresentedGroup.of representative ⟨331, [(false, false)], 257⟩ :=
  holds_reverse edge330

theorem edge331 : Holds level0Subgroup PresentedGroup.of representative ⟨258, [(false, true)], 332⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge331Inv : Holds level0Subgroup PresentedGroup.of representative ⟨332, [(false, false)], 258⟩ :=
  holds_reverse edge331

theorem edge332 : Holds level0Subgroup PresentedGroup.of representative ⟨259, [(false, true)], 333⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge332Inv : Holds level0Subgroup PresentedGroup.of representative ⟨333, [(false, false)], 259⟩ :=
  holds_reverse edge332

theorem edge333 : Holds level0Subgroup PresentedGroup.of representative ⟨260, [(false, true)], 334⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge333Inv : Holds level0Subgroup PresentedGroup.of representative ⟨334, [(false, false)], 260⟩ :=
  holds_reverse edge333

theorem edge334 : Holds level0Subgroup PresentedGroup.of representative ⟨261, [(false, true)], 335⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge334Inv : Holds level0Subgroup PresentedGroup.of representative ⟨335, [(false, false)], 261⟩ :=
  holds_reverse edge334

theorem edge335 : Holds level0Subgroup PresentedGroup.of representative ⟨262, [(false, true)], 336⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge335Inv : Holds level0Subgroup PresentedGroup.of representative ⟨336, [(false, false)], 262⟩ :=
  holds_reverse edge335

theorem edge336 : Holds level0Subgroup PresentedGroup.of representative ⟨263, [(false, true)], 337⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge336Inv : Holds level0Subgroup PresentedGroup.of representative ⟨337, [(false, false)], 263⟩ :=
  holds_reverse edge336

theorem edge337 : Holds level0Subgroup PresentedGroup.of representative ⟨264, [(false, true)], 338⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge337Inv : Holds level0Subgroup PresentedGroup.of representative ⟨338, [(false, false)], 264⟩ :=
  holds_reverse edge337

theorem edge338 : Holds level0Subgroup PresentedGroup.of representative ⟨265, [(true, true)], 339⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge338Inv : Holds level0Subgroup PresentedGroup.of representative ⟨339, [(true, false)], 265⟩ :=
  holds_reverse edge338

theorem edge339 : Holds level0Subgroup PresentedGroup.of representative ⟨265, [(true, false)], 340⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge339Inv : Holds level0Subgroup PresentedGroup.of representative ⟨340, [(true, true)], 265⟩ :=
  holds_reverse edge339

theorem edge340 : Holds level0Subgroup PresentedGroup.of representative ⟨266, [(true, false)], 341⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge340Inv : Holds level0Subgroup PresentedGroup.of representative ⟨341, [(true, true)], 266⟩ :=
  holds_reverse edge340

theorem edge341 : Holds level0Subgroup PresentedGroup.of representative ⟨267, [(true, true)], 342⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge341Inv : Holds level0Subgroup PresentedGroup.of representative ⟨342, [(true, false)], 267⟩ :=
  holds_reverse edge341

theorem edge342 : Holds level0Subgroup PresentedGroup.of representative ⟨268, [(true, true)], 343⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge342Inv : Holds level0Subgroup PresentedGroup.of representative ⟨343, [(true, false)], 268⟩ :=
  holds_reverse edge342

theorem edge343 : Holds level0Subgroup PresentedGroup.of representative ⟨269, [(true, true)], 344⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge343Inv : Holds level0Subgroup PresentedGroup.of representative ⟨344, [(true, false)], 269⟩ :=
  holds_reverse edge343

theorem edge344 : Holds level0Subgroup PresentedGroup.of representative ⟨269, [(true, false)], 345⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge344Inv : Holds level0Subgroup PresentedGroup.of representative ⟨345, [(true, true)], 269⟩ :=
  holds_reverse edge344

theorem edge345 : Holds level0Subgroup PresentedGroup.of representative ⟨270, [(true, true)], 346⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge345Inv : Holds level0Subgroup PresentedGroup.of representative ⟨346, [(true, false)], 270⟩ :=
  holds_reverse edge345

theorem edge346 : Holds level0Subgroup PresentedGroup.of representative ⟨270, [(true, false)], 347⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge346Inv : Holds level0Subgroup PresentedGroup.of representative ⟨347, [(true, true)], 270⟩ :=
  holds_reverse edge346

theorem edge347 : Holds level0Subgroup PresentedGroup.of representative ⟨271, [(true, true)], 348⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge347Inv : Holds level0Subgroup PresentedGroup.of representative ⟨348, [(true, false)], 271⟩ :=
  holds_reverse edge347

theorem edge348 : Holds level0Subgroup PresentedGroup.of representative ⟨271, [(true, false)], 349⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge348Inv : Holds level0Subgroup PresentedGroup.of representative ⟨349, [(true, true)], 271⟩ :=
  holds_reverse edge348

theorem edge349 : Holds level0Subgroup PresentedGroup.of representative ⟨272, [(true, true)], 350⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge349Inv : Holds level0Subgroup PresentedGroup.of representative ⟨350, [(true, false)], 272⟩ :=
  holds_reverse edge349

theorem edge350 : Holds level0Subgroup PresentedGroup.of representative ⟨272, [(true, false)], 351⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge350Inv : Holds level0Subgroup PresentedGroup.of representative ⟨351, [(true, true)], 272⟩ :=
  holds_reverse edge350

theorem edge351 : Holds level0Subgroup PresentedGroup.of representative ⟨273, [(true, true)], 352⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge351Inv : Holds level0Subgroup PresentedGroup.of representative ⟨352, [(true, false)], 273⟩ :=
  holds_reverse edge351

theorem edge352 : Holds level0Subgroup PresentedGroup.of representative ⟨273, [(true, false)], 353⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge352Inv : Holds level0Subgroup PresentedGroup.of representative ⟨353, [(true, true)], 273⟩ :=
  holds_reverse edge352

theorem edge353 : Holds level0Subgroup PresentedGroup.of representative ⟨274, [(true, true)], 354⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge353Inv : Holds level0Subgroup PresentedGroup.of representative ⟨354, [(true, false)], 274⟩ :=
  holds_reverse edge353

theorem edge354 : Holds level0Subgroup PresentedGroup.of representative ⟨274, [(true, false)], 355⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge354Inv : Holds level0Subgroup PresentedGroup.of representative ⟨355, [(true, true)], 274⟩ :=
  holds_reverse edge354

theorem edge355 : Holds level0Subgroup PresentedGroup.of representative ⟨275, [(true, true)], 356⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge355Inv : Holds level0Subgroup PresentedGroup.of representative ⟨356, [(true, false)], 275⟩ :=
  holds_reverse edge355

theorem edge356 : Holds level0Subgroup PresentedGroup.of representative ⟨275, [(true, false)], 357⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge356Inv : Holds level0Subgroup PresentedGroup.of representative ⟨357, [(true, true)], 275⟩ :=
  holds_reverse edge356

theorem edge357 : Holds level0Subgroup PresentedGroup.of representative ⟨276, [(true, true)], 358⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge357Inv : Holds level0Subgroup PresentedGroup.of representative ⟨358, [(true, false)], 276⟩ :=
  holds_reverse edge357

theorem edge358 : Holds level0Subgroup PresentedGroup.of representative ⟨277, [(true, true)], 359⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge358Inv : Holds level0Subgroup PresentedGroup.of representative ⟨359, [(true, false)], 277⟩ :=
  holds_reverse edge358

theorem edge359 : Holds level0Subgroup PresentedGroup.of representative ⟨277, [(true, false)], 360⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge359Inv : Holds level0Subgroup PresentedGroup.of representative ⟨360, [(true, true)], 277⟩ :=
  holds_reverse edge359

theorem edge360 : Holds level0Subgroup PresentedGroup.of representative ⟨278, [(true, true)], 361⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge360Inv : Holds level0Subgroup PresentedGroup.of representative ⟨361, [(true, false)], 278⟩ :=
  holds_reverse edge360

theorem edge361 : Holds level0Subgroup PresentedGroup.of representative ⟨278, [(true, false)], 362⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge361Inv : Holds level0Subgroup PresentedGroup.of representative ⟨362, [(true, true)], 278⟩ :=
  holds_reverse edge361

theorem edge362 : Holds level0Subgroup PresentedGroup.of representative ⟨279, [(true, true)], 363⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge362Inv : Holds level0Subgroup PresentedGroup.of representative ⟨363, [(true, false)], 279⟩ :=
  holds_reverse edge362

theorem edge363 : Holds level0Subgroup PresentedGroup.of representative ⟨279, [(true, false)], 364⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge363Inv : Holds level0Subgroup PresentedGroup.of representative ⟨364, [(true, true)], 279⟩ :=
  holds_reverse edge363

theorem edge364 : Holds level0Subgroup PresentedGroup.of representative ⟨280, [(true, true)], 365⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge364Inv : Holds level0Subgroup PresentedGroup.of representative ⟨365, [(true, false)], 280⟩ :=
  holds_reverse edge364

theorem edge365 : Holds level0Subgroup PresentedGroup.of representative ⟨280, [(true, false)], 366⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge365Inv : Holds level0Subgroup PresentedGroup.of representative ⟨366, [(true, true)], 280⟩ :=
  holds_reverse edge365

theorem edge366 : Holds level0Subgroup PresentedGroup.of representative ⟨281, [(true, false)], 367⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge366Inv : Holds level0Subgroup PresentedGroup.of representative ⟨367, [(true, true)], 281⟩ :=
  holds_reverse edge366

theorem edge367 : Holds level0Subgroup PresentedGroup.of representative ⟨282, [(true, true)], 368⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge367Inv : Holds level0Subgroup PresentedGroup.of representative ⟨368, [(true, false)], 282⟩ :=
  holds_reverse edge367

theorem edge368 : Holds level0Subgroup PresentedGroup.of representative ⟨282, [(true, false)], 369⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge368Inv : Holds level0Subgroup PresentedGroup.of representative ⟨369, [(true, true)], 282⟩ :=
  holds_reverse edge368

theorem edge369 : Holds level0Subgroup PresentedGroup.of representative ⟨283, [(true, true)], 370⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge369Inv : Holds level0Subgroup PresentedGroup.of representative ⟨370, [(true, false)], 283⟩ :=
  holds_reverse edge369

theorem edge370 : Holds level0Subgroup PresentedGroup.of representative ⟨285, [(true, true)], 371⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge370Inv : Holds level0Subgroup PresentedGroup.of representative ⟨371, [(true, false)], 285⟩ :=
  holds_reverse edge370

theorem edge371 : Holds level0Subgroup PresentedGroup.of representative ⟨285, [(true, false)], 372⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge371Inv : Holds level0Subgroup PresentedGroup.of representative ⟨372, [(true, true)], 285⟩ :=
  holds_reverse edge371

theorem edge372 : Holds level0Subgroup PresentedGroup.of representative ⟨286, [(true, true)], 373⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge372Inv : Holds level0Subgroup PresentedGroup.of representative ⟨373, [(true, false)], 286⟩ :=
  holds_reverse edge372

theorem edge373 : Holds level0Subgroup PresentedGroup.of representative ⟨286, [(true, false)], 374⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge373Inv : Holds level0Subgroup PresentedGroup.of representative ⟨374, [(true, true)], 286⟩ :=
  holds_reverse edge373

theorem edge374 : Holds level0Subgroup PresentedGroup.of representative ⟨287, [(true, true)], 375⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge374Inv : Holds level0Subgroup PresentedGroup.of representative ⟨375, [(true, false)], 287⟩ :=
  holds_reverse edge374

theorem edge375 : Holds level0Subgroup PresentedGroup.of representative ⟨288, [(true, true)], 376⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge375Inv : Holds level0Subgroup PresentedGroup.of representative ⟨376, [(true, false)], 288⟩ :=
  holds_reverse edge375

theorem edge376 : Holds level0Subgroup PresentedGroup.of representative ⟨288, [(true, false)], 377⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge376Inv : Holds level0Subgroup PresentedGroup.of representative ⟨377, [(true, true)], 288⟩ :=
  holds_reverse edge376

theorem edge377 : Holds level0Subgroup PresentedGroup.of representative ⟨289, [(true, true)], 378⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge377Inv : Holds level0Subgroup PresentedGroup.of representative ⟨378, [(true, false)], 289⟩ :=
  holds_reverse edge377

theorem edge378 : Holds level0Subgroup PresentedGroup.of representative ⟨290, [(true, true)], 379⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge378Inv : Holds level0Subgroup PresentedGroup.of representative ⟨379, [(true, false)], 290⟩ :=
  holds_reverse edge378

theorem edge379 : Holds level0Subgroup PresentedGroup.of representative ⟨290, [(true, false)], 380⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge379Inv : Holds level0Subgroup PresentedGroup.of representative ⟨380, [(true, true)], 290⟩ :=
  holds_reverse edge379

theorem edge380 : Holds level0Subgroup PresentedGroup.of representative ⟨291, [(true, true)], 381⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge380Inv : Holds level0Subgroup PresentedGroup.of representative ⟨381, [(true, false)], 291⟩ :=
  holds_reverse edge380

theorem edge381 : Holds level0Subgroup PresentedGroup.of representative ⟨291, [(true, false)], 382⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge381Inv : Holds level0Subgroup PresentedGroup.of representative ⟨382, [(true, true)], 291⟩ :=
  holds_reverse edge381

theorem edge382 : Holds level0Subgroup PresentedGroup.of representative ⟨292, [(true, true)], 383⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge382Inv : Holds level0Subgroup PresentedGroup.of representative ⟨383, [(true, false)], 292⟩ :=
  holds_reverse edge382

theorem edge383 : Holds level0Subgroup PresentedGroup.of representative ⟨292, [(true, false)], 384⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge383Inv : Holds level0Subgroup PresentedGroup.of representative ⟨384, [(true, true)], 292⟩ :=
  holds_reverse edge383


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
