module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges14

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

theorem edge960 : Holds level0Subgroup PresentedGroup.of representative ⟨333, [(false, true)], 259⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨259, [(false, true)], 333⟩ :=
    edge332
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨259, [], 259⟩ :=
    (holds_refl 259)
  exact scanFacts hp hs (holds_relator 259 (level0Relator 0) (level0_relator 0))

theorem edge960Inv : Holds level0Subgroup PresentedGroup.of representative ⟨259, [(false, false)], 333⟩ :=
  holds_reverse edge960

theorem edge961 : Holds level0Subgroup PresentedGroup.of representative ⟨334, [(false, true)], 260⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨260, [(false, true)], 334⟩ :=
    edge333
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨260, [], 260⟩ :=
    (holds_refl 260)
  exact scanFacts hp hs (holds_relator 260 (level0Relator 0) (level0_relator 0))

theorem edge961Inv : Holds level0Subgroup PresentedGroup.of representative ⟨260, [(false, false)], 334⟩ :=
  holds_reverse edge961

theorem edge962 : Holds level0Subgroup PresentedGroup.of representative ⟨335, [(false, true)], 261⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨261, [(false, true)], 335⟩ :=
    edge334
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨261, [], 261⟩ :=
    (holds_refl 261)
  exact scanFacts hp hs (holds_relator 261 (level0Relator 0) (level0_relator 0))

theorem edge962Inv : Holds level0Subgroup PresentedGroup.of representative ⟨261, [(false, false)], 335⟩ :=
  holds_reverse edge962

theorem edge963 : Holds level0Subgroup PresentedGroup.of representative ⟨336, [(false, true)], 262⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨262, [(false, true)], 336⟩ :=
    edge335
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨262, [], 262⟩ :=
    (holds_refl 262)
  exact scanFacts hp hs (holds_relator 262 (level0Relator 0) (level0_relator 0))

theorem edge963Inv : Holds level0Subgroup PresentedGroup.of representative ⟨262, [(false, false)], 336⟩ :=
  holds_reverse edge963

theorem edge964 : Holds level0Subgroup PresentedGroup.of representative ⟨337, [(false, true)], 263⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨263, [(false, true)], 337⟩ :=
    edge336
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨263, [], 263⟩ :=
    (holds_refl 263)
  exact scanFacts hp hs (holds_relator 263 (level0Relator 0) (level0_relator 0))

theorem edge964Inv : Holds level0Subgroup PresentedGroup.of representative ⟨263, [(false, false)], 337⟩ :=
  holds_reverse edge964

theorem edge965 : Holds level0Subgroup PresentedGroup.of representative ⟨338, [(false, true)], 264⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨264, [(false, true)], 338⟩ :=
    edge337
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨264, [], 264⟩ :=
    (holds_refl 264)
  exact scanFacts hp hs (holds_relator 264 (level0Relator 0) (level0_relator 0))

theorem edge965Inv : Holds level0Subgroup PresentedGroup.of representative ⟨264, [(false, false)], 338⟩ :=
  holds_reverse edge965

theorem edge966 : Holds level0Subgroup PresentedGroup.of representative ⟨339, [(true, true)], 340⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨265, [(true, true)], 339⟩ :=
    edge338
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨340, [(true, true)], 265⟩ :=
    edge339Inv
  exact scanFacts hp hs (holds_relator 265 (level0Relator 1) (level0_relator 1))

theorem edge966Inv : Holds level0Subgroup PresentedGroup.of representative ⟨340, [(true, false)], 339⟩ :=
  holds_reverse edge966

theorem edge967 : Holds level0Subgroup PresentedGroup.of representative ⟨284, [(true, true)], 341⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨266, [(true, true)], 284⟩ :=
    edge702
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨341, [(true, true)], 266⟩ :=
    edge340Inv
  exact scanFacts hp hs (holds_relator 266 (level0Relator 1) (level0_relator 1))

theorem edge967Inv : Holds level0Subgroup PresentedGroup.of representative ⟨341, [(true, false)], 284⟩ :=
  holds_reverse edge967

theorem edge968 : Holds level0Subgroup PresentedGroup.of representative ⟨342, [(true, true)], 324⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨267, [(true, true)], 342⟩ :=
    edge341
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨324, [(true, true)], 267⟩ :=
    edge703Inv
  exact scanFacts hp hs (holds_relator 267 (level0Relator 1) (level0_relator 1))

theorem edge968Inv : Holds level0Subgroup PresentedGroup.of representative ⟨324, [(true, false)], 342⟩ :=
  holds_reverse edge968

theorem edge969 : Holds level0Subgroup PresentedGroup.of representative ⟨343, [(true, true)], 296⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨268, [(true, true)], 343⟩ :=
    edge342
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨296, [(true, true)], 268⟩ :=
    edge704Inv
  exact scanFacts hp hs (holds_relator 268 (level0Relator 1) (level0_relator 1))

theorem edge969Inv : Holds level0Subgroup PresentedGroup.of representative ⟨296, [(true, false)], 343⟩ :=
  holds_reverse edge969

theorem edge970 : Holds level0Subgroup PresentedGroup.of representative ⟨344, [(true, true)], 345⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨269, [(true, true)], 344⟩ :=
    edge343
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨345, [(true, true)], 269⟩ :=
    edge344Inv
  exact scanFacts hp hs (holds_relator 269 (level0Relator 1) (level0_relator 1))

theorem edge970Inv : Holds level0Subgroup PresentedGroup.of representative ⟨345, [(true, false)], 344⟩ :=
  holds_reverse edge970

theorem edge971 : Holds level0Subgroup PresentedGroup.of representative ⟨346, [(true, true)], 347⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨270, [(true, true)], 346⟩ :=
    edge345
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨347, [(true, true)], 270⟩ :=
    edge346Inv
  exact scanFacts hp hs (holds_relator 270 (level0Relator 1) (level0_relator 1))

theorem edge971Inv : Holds level0Subgroup PresentedGroup.of representative ⟨347, [(true, false)], 346⟩ :=
  holds_reverse edge971

theorem edge972 : Holds level0Subgroup PresentedGroup.of representative ⟨348, [(true, true)], 349⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨271, [(true, true)], 348⟩ :=
    edge347
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨349, [(true, true)], 271⟩ :=
    edge348Inv
  exact scanFacts hp hs (holds_relator 271 (level0Relator 1) (level0_relator 1))

theorem edge972Inv : Holds level0Subgroup PresentedGroup.of representative ⟨349, [(true, false)], 348⟩ :=
  holds_reverse edge972

theorem edge973 : Holds level0Subgroup PresentedGroup.of representative ⟨350, [(true, true)], 351⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨272, [(true, true)], 350⟩ :=
    edge349
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨351, [(true, true)], 272⟩ :=
    edge350Inv
  exact scanFacts hp hs (holds_relator 272 (level0Relator 1) (level0_relator 1))

theorem edge973Inv : Holds level0Subgroup PresentedGroup.of representative ⟨351, [(true, false)], 350⟩ :=
  holds_reverse edge973

theorem edge974 : Holds level0Subgroup PresentedGroup.of representative ⟨352, [(true, true)], 353⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨273, [(true, true)], 352⟩ :=
    edge351
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨353, [(true, true)], 273⟩ :=
    edge352Inv
  exact scanFacts hp hs (holds_relator 273 (level0Relator 1) (level0_relator 1))

theorem edge974Inv : Holds level0Subgroup PresentedGroup.of representative ⟨353, [(true, false)], 352⟩ :=
  holds_reverse edge974

theorem edge975 : Holds level0Subgroup PresentedGroup.of representative ⟨354, [(true, true)], 355⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨274, [(true, true)], 354⟩ :=
    edge353
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨355, [(true, true)], 274⟩ :=
    edge354Inv
  exact scanFacts hp hs (holds_relator 274 (level0Relator 1) (level0_relator 1))

theorem edge975Inv : Holds level0Subgroup PresentedGroup.of representative ⟨355, [(true, false)], 354⟩ :=
  holds_reverse edge975

theorem edge976 : Holds level0Subgroup PresentedGroup.of representative ⟨356, [(true, true)], 357⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨275, [(true, true)], 356⟩ :=
    edge355
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨357, [(true, true)], 275⟩ :=
    edge356Inv
  exact scanFacts hp hs (holds_relator 275 (level0Relator 1) (level0_relator 1))

theorem edge976Inv : Holds level0Subgroup PresentedGroup.of representative ⟨357, [(true, false)], 356⟩ :=
  holds_reverse edge976

theorem edge977 : Holds level0Subgroup PresentedGroup.of representative ⟨358, [(true, true)], 295⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨276, [(true, true)], 358⟩ :=
    edge357
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨295, [(true, true)], 276⟩ :=
    edge705Inv
  exact scanFacts hp hs (holds_relator 276 (level0Relator 1) (level0_relator 1))

theorem edge977Inv : Holds level0Subgroup PresentedGroup.of representative ⟨295, [(true, false)], 358⟩ :=
  holds_reverse edge977

theorem edge978 : Holds level0Subgroup PresentedGroup.of representative ⟨359, [(true, true)], 360⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨277, [(true, true)], 359⟩ :=
    edge358
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨360, [(true, true)], 277⟩ :=
    edge359Inv
  exact scanFacts hp hs (holds_relator 277 (level0Relator 1) (level0_relator 1))

theorem edge978Inv : Holds level0Subgroup PresentedGroup.of representative ⟨360, [(true, false)], 359⟩ :=
  holds_reverse edge978

theorem edge979 : Holds level0Subgroup PresentedGroup.of representative ⟨361, [(true, true)], 362⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨278, [(true, true)], 361⟩ :=
    edge360
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨362, [(true, true)], 278⟩ :=
    edge361Inv
  exact scanFacts hp hs (holds_relator 278 (level0Relator 1) (level0_relator 1))

theorem edge979Inv : Holds level0Subgroup PresentedGroup.of representative ⟨362, [(true, false)], 361⟩ :=
  holds_reverse edge979

theorem edge980 : Holds level0Subgroup PresentedGroup.of representative ⟨363, [(true, true)], 364⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨279, [(true, true)], 363⟩ :=
    edge362
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨364, [(true, true)], 279⟩ :=
    edge363Inv
  exact scanFacts hp hs (holds_relator 279 (level0Relator 1) (level0_relator 1))

theorem edge980Inv : Holds level0Subgroup PresentedGroup.of representative ⟨364, [(true, false)], 363⟩ :=
  holds_reverse edge980

theorem edge981 : Holds level0Subgroup PresentedGroup.of representative ⟨365, [(true, true)], 366⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨280, [(true, true)], 365⟩ :=
    edge364
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨366, [(true, true)], 280⟩ :=
    edge365Inv
  exact scanFacts hp hs (holds_relator 280 (level0Relator 1) (level0_relator 1))

theorem edge981Inv : Holds level0Subgroup PresentedGroup.of representative ⟨366, [(true, false)], 365⟩ :=
  holds_reverse edge981

theorem edge982 : Holds level0Subgroup PresentedGroup.of representative ⟨305, [(true, true)], 367⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨281, [(true, true)], 305⟩ :=
    edge706
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨367, [(true, true)], 281⟩ :=
    edge366Inv
  exact scanFacts hp hs (holds_relator 281 (level0Relator 1) (level0_relator 1))

theorem edge982Inv : Holds level0Subgroup PresentedGroup.of representative ⟨367, [(true, false)], 305⟩ :=
  holds_reverse edge982

theorem edge983 : Holds level0Subgroup PresentedGroup.of representative ⟨368, [(true, true)], 369⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨282, [(true, true)], 368⟩ :=
    edge367
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨369, [(true, true)], 282⟩ :=
    edge368Inv
  exact scanFacts hp hs (holds_relator 282 (level0Relator 1) (level0_relator 1))

theorem edge983Inv : Holds level0Subgroup PresentedGroup.of representative ⟨369, [(true, false)], 368⟩ :=
  holds_reverse edge983

theorem edge984 : Holds level0Subgroup PresentedGroup.of representative ⟨370, [(true, true)], 294⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨283, [(true, true)], 370⟩ :=
    edge369
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨294, [(true, true)], 283⟩ :=
    edge707Inv
  exact scanFacts hp hs (holds_relator 283 (level0Relator 1) (level0_relator 1))

theorem edge984Inv : Holds level0Subgroup PresentedGroup.of representative ⟨294, [(true, false)], 370⟩ :=
  holds_reverse edge984

theorem edge985 : Holds level0Subgroup PresentedGroup.of representative ⟨371, [(true, true)], 372⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨285, [(true, true)], 371⟩ :=
    edge370
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨372, [(true, true)], 285⟩ :=
    edge371Inv
  exact scanFacts hp hs (holds_relator 285 (level0Relator 1) (level0_relator 1))

theorem edge985Inv : Holds level0Subgroup PresentedGroup.of representative ⟨372, [(true, false)], 371⟩ :=
  holds_reverse edge985

theorem edge986 : Holds level0Subgroup PresentedGroup.of representative ⟨373, [(true, true)], 374⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨286, [(true, true)], 373⟩ :=
    edge372
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨374, [(true, true)], 286⟩ :=
    edge373Inv
  exact scanFacts hp hs (holds_relator 286 (level0Relator 1) (level0_relator 1))

theorem edge986Inv : Holds level0Subgroup PresentedGroup.of representative ⟨374, [(true, false)], 373⟩ :=
  holds_reverse edge986

theorem edge987 : Holds level0Subgroup PresentedGroup.of representative ⟨375, [(true, true)], 334⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨287, [(true, true)], 375⟩ :=
    edge374
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨334, [(true, true)], 287⟩ :=
    edge708Inv
  exact scanFacts hp hs (holds_relator 287 (level0Relator 1) (level0_relator 1))

theorem edge987Inv : Holds level0Subgroup PresentedGroup.of representative ⟨334, [(true, false)], 375⟩ :=
  holds_reverse edge987

theorem edge988 : Holds level0Subgroup PresentedGroup.of representative ⟨376, [(true, true)], 377⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨288, [(true, true)], 376⟩ :=
    edge375
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨377, [(true, true)], 288⟩ :=
    edge376Inv
  exact scanFacts hp hs (holds_relator 288 (level0Relator 1) (level0_relator 1))

theorem edge988Inv : Holds level0Subgroup PresentedGroup.of representative ⟨377, [(true, false)], 376⟩ :=
  holds_reverse edge988

theorem edge989 : Holds level0Subgroup PresentedGroup.of representative ⟨447, [(false, true)], 376⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨288, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 447⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge911 (appendFacts edge206Inv edge816)) (appendFacts edge111Inv (appendFacts edge767 edge59Inv))) (appendFacts (appendFacts edge740 (appendFacts edge31Inv edge726)) (appendFacts (appendFacts edge720Inv edge22) (appendFacts edge30 edge42)))) (appendFacts (appendFacts (appendFacts edge58 (appendFacts edge81 edge110)) (appendFacts edge697 (appendFacts edge788Inv edge152))) (appendFacts (appendFacts edge205 (appendFacts edge286 edge708)) (appendFacts (appendFacts edge961 edge885Inv) (appendFacts edge332 edge446)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨376, [(true, false)], 288⟩ :=
    edge375Inv
  exact scanFacts hp hs (holds_relator 288 (level0Relator 2) (level0_relator 2))

theorem edge989Inv : Holds level0Subgroup PresentedGroup.of representative ⟨376, [(false, false)], 447⟩ :=
  holds_reverse edge989

theorem edge990 : Holds level0Subgroup PresentedGroup.of representative ⟨379, [(true, true)], 380⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨290, [(true, true)], 379⟩ :=
    edge378
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨380, [(true, true)], 290⟩ :=
    edge379Inv
  exact scanFacts hp hs (holds_relator 290 (level0Relator 1) (level0_relator 1))

theorem edge990Inv : Holds level0Subgroup PresentedGroup.of representative ⟨380, [(true, false)], 379⟩ :=
  holds_reverse edge990

theorem edge991 : Holds level0Subgroup PresentedGroup.of representative ⟨381, [(true, true)], 382⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨291, [(true, true)], 381⟩ :=
    edge380
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨382, [(true, true)], 291⟩ :=
    edge381Inv
  exact scanFacts hp hs (holds_relator 291 (level0Relator 1) (level0_relator 1))

theorem edge991Inv : Holds level0Subgroup PresentedGroup.of representative ⟨382, [(true, false)], 381⟩ :=
  holds_reverse edge991

theorem edge992 : Holds level0Subgroup PresentedGroup.of representative ⟨383, [(true, true)], 384⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨292, [(true, true)], 383⟩ :=
    edge382
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨384, [(true, true)], 292⟩ :=
    edge383Inv
  exact scanFacts hp hs (holds_relator 292 (level0Relator 1) (level0_relator 1))

theorem edge992Inv : Holds level0Subgroup PresentedGroup.of representative ⟨384, [(true, false)], 383⟩ :=
  holds_reverse edge992

theorem edge993 : Holds level0Subgroup PresentedGroup.of representative ⟨385, [(true, true)], 386⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨293, [(true, true)], 385⟩ :=
    edge384
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨386, [(true, true)], 293⟩ :=
    edge385Inv
  exact scanFacts hp hs (holds_relator 293 (level0Relator 1) (level0_relator 1))

theorem edge993Inv : Holds level0Subgroup PresentedGroup.of representative ⟨386, [(true, false)], 385⟩ :=
  holds_reverse edge993

theorem edge994 : Holds level0Subgroup PresentedGroup.of representative ⟨388, [(true, true)], 389⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨298, [(true, true)], 388⟩ :=
    edge387
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨389, [(true, true)], 298⟩ :=
    edge388Inv
  exact scanFacts hp hs (holds_relator 298 (level0Relator 1) (level0_relator 1))

theorem edge994Inv : Holds level0Subgroup PresentedGroup.of representative ⟨389, [(true, false)], 388⟩ :=
  holds_reverse edge994

theorem edge995 : Holds level0Subgroup PresentedGroup.of representative ⟨390, [(true, true)], 391⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨299, [(true, true)], 390⟩ :=
    edge389
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨391, [(true, true)], 299⟩ :=
    edge390Inv
  exact scanFacts hp hs (holds_relator 299 (level0Relator 1) (level0_relator 1))

theorem edge995Inv : Holds level0Subgroup PresentedGroup.of representative ⟨391, [(true, false)], 390⟩ :=
  holds_reverse edge995

theorem edge996 : Holds level0Subgroup PresentedGroup.of representative ⟨392, [(true, true)], 393⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨300, [(true, true)], 392⟩ :=
    edge391
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨393, [(true, true)], 300⟩ :=
    edge392Inv
  exact scanFacts hp hs (holds_relator 300 (level0Relator 1) (level0_relator 1))

theorem edge996Inv : Holds level0Subgroup PresentedGroup.of representative ⟨393, [(true, false)], 392⟩ :=
  holds_reverse edge996

theorem edge997 : Holds level0Subgroup PresentedGroup.of representative ⟨394, [(true, true)], 395⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨301, [(true, true)], 394⟩ :=
    edge393
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨395, [(true, true)], 301⟩ :=
    edge394Inv
  exact scanFacts hp hs (holds_relator 301 (level0Relator 1) (level0_relator 1))

theorem edge997Inv : Holds level0Subgroup PresentedGroup.of representative ⟨395, [(true, false)], 394⟩ :=
  holds_reverse edge997

theorem edge998 : Holds level0Subgroup PresentedGroup.of representative ⟨397, [(true, true)], 398⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨303, [(true, true)], 397⟩ :=
    edge396
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨398, [(true, true)], 303⟩ :=
    edge397Inv
  exact scanFacts hp hs (holds_relator 303 (level0Relator 1) (level0_relator 1))

theorem edge998Inv : Holds level0Subgroup PresentedGroup.of representative ⟨398, [(true, false)], 397⟩ :=
  holds_reverse edge998

theorem edge999 : Holds level0Subgroup PresentedGroup.of representative ⟨399, [(true, true)], 400⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨304, [(true, true)], 399⟩ :=
    edge398
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨400, [(true, true)], 304⟩ :=
    edge399Inv
  exact scanFacts hp hs (holds_relator 304 (level0Relator 1) (level0_relator 1))

theorem edge999Inv : Holds level0Subgroup PresentedGroup.of representative ⟨400, [(true, false)], 399⟩ :=
  holds_reverse edge999

theorem edge1000 : Holds level0Subgroup PresentedGroup.of representative ⟨401, [(true, true)], 402⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨307, [(true, true)], 401⟩ :=
    edge400
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨402, [(true, true)], 307⟩ :=
    edge401Inv
  exact scanFacts hp hs (holds_relator 307 (level0Relator 1) (level0_relator 1))

theorem edge1000Inv : Holds level0Subgroup PresentedGroup.of representative ⟨402, [(true, false)], 401⟩ :=
  holds_reverse edge1000

theorem edge1001 : Holds level0Subgroup PresentedGroup.of representative ⟨403, [(true, true)], 404⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨308, [(true, true)], 403⟩ :=
    edge402
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨404, [(true, true)], 308⟩ :=
    edge403Inv
  exact scanFacts hp hs (holds_relator 308 (level0Relator 1) (level0_relator 1))

theorem edge1001Inv : Holds level0Subgroup PresentedGroup.of representative ⟨404, [(true, false)], 403⟩ :=
  holds_reverse edge1001

theorem edge1002 : Holds level0Subgroup PresentedGroup.of representative ⟨405, [(true, true)], 406⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨310, [(true, true)], 405⟩ :=
    edge404
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨406, [(true, true)], 310⟩ :=
    edge405Inv
  exact scanFacts hp hs (holds_relator 310 (level0Relator 1) (level0_relator 1))

theorem edge1002Inv : Holds level0Subgroup PresentedGroup.of representative ⟨406, [(true, false)], 405⟩ :=
  holds_reverse edge1002

theorem edge1003 : Holds level0Subgroup PresentedGroup.of representative ⟨407, [(true, true)], 408⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨311, [(true, true)], 407⟩ :=
    edge406
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨408, [(true, true)], 311⟩ :=
    edge407Inv
  exact scanFacts hp hs (holds_relator 311 (level0Relator 1) (level0_relator 1))

theorem edge1003Inv : Holds level0Subgroup PresentedGroup.of representative ⟨408, [(true, false)], 407⟩ :=
  holds_reverse edge1003

theorem edge1004 : Holds level0Subgroup PresentedGroup.of representative ⟨409, [(true, true)], 410⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨312, [(true, true)], 409⟩ :=
    edge408
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨410, [(true, true)], 312⟩ :=
    edge409Inv
  exact scanFacts hp hs (holds_relator 312 (level0Relator 1) (level0_relator 1))

theorem edge1004Inv : Holds level0Subgroup PresentedGroup.of representative ⟨410, [(true, false)], 409⟩ :=
  holds_reverse edge1004

theorem edge1005 : Holds level0Subgroup PresentedGroup.of representative ⟨411, [(true, true)], 412⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨313, [(true, true)], 411⟩ :=
    edge410
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨412, [(true, true)], 313⟩ :=
    edge411Inv
  exact scanFacts hp hs (holds_relator 313 (level0Relator 1) (level0_relator 1))

theorem edge1005Inv : Holds level0Subgroup PresentedGroup.of representative ⟨412, [(true, false)], 411⟩ :=
  holds_reverse edge1005

theorem edge1006 : Holds level0Subgroup PresentedGroup.of representative ⟨413, [(true, true)], 414⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨314, [(true, true)], 413⟩ :=
    edge412
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨414, [(true, true)], 314⟩ :=
    edge413Inv
  exact scanFacts hp hs (holds_relator 314 (level0Relator 1) (level0_relator 1))

theorem edge1006Inv : Holds level0Subgroup PresentedGroup.of representative ⟨414, [(true, false)], 413⟩ :=
  holds_reverse edge1006

theorem edge1007 : Holds level0Subgroup PresentedGroup.of representative ⟨415, [(true, true)], 416⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨315, [(true, true)], 415⟩ :=
    edge414
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨416, [(true, true)], 315⟩ :=
    edge415Inv
  exact scanFacts hp hs (holds_relator 315 (level0Relator 1) (level0_relator 1))

theorem edge1007Inv : Holds level0Subgroup PresentedGroup.of representative ⟨416, [(true, false)], 415⟩ :=
  holds_reverse edge1007

theorem edge1008 : Holds level0Subgroup PresentedGroup.of representative ⟨417, [(true, true)], 418⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨316, [(true, true)], 417⟩ :=
    edge416
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨418, [(true, true)], 316⟩ :=
    edge417Inv
  exact scanFacts hp hs (holds_relator 316 (level0Relator 1) (level0_relator 1))

theorem edge1008Inv : Holds level0Subgroup PresentedGroup.of representative ⟨418, [(true, false)], 417⟩ :=
  holds_reverse edge1008

theorem edge1009 : Holds level0Subgroup PresentedGroup.of representative ⟨419, [(true, true)], 420⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨317, [(true, true)], 419⟩ :=
    edge418
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨420, [(true, true)], 317⟩ :=
    edge419Inv
  exact scanFacts hp hs (holds_relator 317 (level0Relator 1) (level0_relator 1))

theorem edge1009Inv : Holds level0Subgroup PresentedGroup.of representative ⟨420, [(true, false)], 419⟩ :=
  holds_reverse edge1009

theorem edge1010 : Holds level0Subgroup PresentedGroup.of representative ⟨421, [(true, true)], 422⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨319, [(true, true)], 421⟩ :=
    edge420
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨422, [(true, true)], 319⟩ :=
    edge421Inv
  exact scanFacts hp hs (holds_relator 319 (level0Relator 1) (level0_relator 1))

theorem edge1010Inv : Holds level0Subgroup PresentedGroup.of representative ⟨422, [(true, false)], 421⟩ :=
  holds_reverse edge1010

theorem edge1011 : Holds level0Subgroup PresentedGroup.of representative ⟨423, [(true, true)], 424⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨320, [(true, true)], 423⟩ :=
    edge422
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨424, [(true, true)], 320⟩ :=
    edge423Inv
  exact scanFacts hp hs (holds_relator 320 (level0Relator 1) (level0_relator 1))

theorem edge1011Inv : Holds level0Subgroup PresentedGroup.of representative ⟨424, [(true, false)], 423⟩ :=
  holds_reverse edge1011

theorem edge1012 : Holds level0Subgroup PresentedGroup.of representative ⟨425, [(true, true)], 426⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨321, [(true, true)], 425⟩ :=
    edge424
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨426, [(true, true)], 321⟩ :=
    edge425Inv
  exact scanFacts hp hs (holds_relator 321 (level0Relator 1) (level0_relator 1))

theorem edge1012Inv : Holds level0Subgroup PresentedGroup.of representative ⟨426, [(true, false)], 425⟩ :=
  holds_reverse edge1012

theorem edge1013 : Holds level0Subgroup PresentedGroup.of representative ⟨427, [(true, true)], 428⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨322, [(true, true)], 427⟩ :=
    edge426
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨428, [(true, true)], 322⟩ :=
    edge427Inv
  exact scanFacts hp hs (holds_relator 322 (level0Relator 1) (level0_relator 1))

theorem edge1013Inv : Holds level0Subgroup PresentedGroup.of representative ⟨428, [(true, false)], 427⟩ :=
  holds_reverse edge1013

theorem edge1014 : Holds level0Subgroup PresentedGroup.of representative ⟨429, [(true, true)], 430⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨323, [(true, true)], 429⟩ :=
    edge428
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨430, [(true, true)], 323⟩ :=
    edge429Inv
  exact scanFacts hp hs (holds_relator 323 (level0Relator 1) (level0_relator 1))

theorem edge1014Inv : Holds level0Subgroup PresentedGroup.of representative ⟨430, [(true, false)], 429⟩ :=
  holds_reverse edge1014

theorem edge1015 : Holds level0Subgroup PresentedGroup.of representative ⟨431, [(true, true)], 432⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨325, [(true, true)], 431⟩ :=
    edge430
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨432, [(true, true)], 325⟩ :=
    edge431Inv
  exact scanFacts hp hs (holds_relator 325 (level0Relator 1) (level0_relator 1))

theorem edge1015Inv : Holds level0Subgroup PresentedGroup.of representative ⟨432, [(true, false)], 431⟩ :=
  holds_reverse edge1015

theorem edge1016 : Holds level0Subgroup PresentedGroup.of representative ⟨433, [(true, true)], 434⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨326, [(true, true)], 433⟩ :=
    edge432
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨434, [(true, true)], 326⟩ :=
    edge433Inv
  exact scanFacts hp hs (holds_relator 326 (level0Relator 1) (level0_relator 1))

theorem edge1016Inv : Holds level0Subgroup PresentedGroup.of representative ⟨434, [(true, false)], 433⟩ :=
  holds_reverse edge1016

theorem edge1017 : Holds level0Subgroup PresentedGroup.of representative ⟨436, [(true, true)], 437⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨328, [(true, true)], 436⟩ :=
    edge435
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨437, [(true, true)], 328⟩ :=
    edge436Inv
  exact scanFacts hp hs (holds_relator 328 (level0Relator 1) (level0_relator 1))

theorem edge1017Inv : Holds level0Subgroup PresentedGroup.of representative ⟨437, [(true, false)], 436⟩ :=
  holds_reverse edge1017

theorem edge1018 : Holds level0Subgroup PresentedGroup.of representative ⟨438, [(true, true)], 439⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨329, [(true, true)], 438⟩ :=
    edge437
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨439, [(true, true)], 329⟩ :=
    edge438Inv
  exact scanFacts hp hs (holds_relator 329 (level0Relator 1) (level0_relator 1))

theorem edge1018Inv : Holds level0Subgroup PresentedGroup.of representative ⟨439, [(true, false)], 438⟩ :=
  holds_reverse edge1018

theorem edge1019 : Holds level0Subgroup PresentedGroup.of representative ⟨440, [(true, true)], 441⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨330, [(true, true)], 440⟩ :=
    edge439
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨441, [(true, true)], 330⟩ :=
    edge440Inv
  exact scanFacts hp hs (holds_relator 330 (level0Relator 1) (level0_relator 1))

theorem edge1019Inv : Holds level0Subgroup PresentedGroup.of representative ⟨441, [(true, false)], 440⟩ :=
  holds_reverse edge1019

theorem edge1020 : Holds level0Subgroup PresentedGroup.of representative ⟨442, [(true, true)], 443⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨331, [(true, true)], 442⟩ :=
    edge441
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨443, [(true, true)], 331⟩ :=
    edge442Inv
  exact scanFacts hp hs (holds_relator 331 (level0Relator 1) (level0_relator 1))

theorem edge1020Inv : Holds level0Subgroup PresentedGroup.of representative ⟨443, [(true, false)], 442⟩ :=
  holds_reverse edge1020

theorem edge1021 : Holds level0Subgroup PresentedGroup.of representative ⟨444, [(true, true)], 445⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨332, [(true, true)], 444⟩ :=
    edge443
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨445, [(true, true)], 332⟩ :=
    edge444Inv
  exact scanFacts hp hs (holds_relator 332 (level0Relator 1) (level0_relator 1))

theorem edge1021Inv : Holds level0Subgroup PresentedGroup.of representative ⟨445, [(true, false)], 444⟩ :=
  holds_reverse edge1021

theorem edge1022 : Holds level0Subgroup PresentedGroup.of representative ⟨446, [(true, true)], 447⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨333, [(true, true)], 446⟩ :=
    edge445
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨447, [(true, true)], 333⟩ :=
    edge446Inv
  exact scanFacts hp hs (holds_relator 333 (level0Relator 1) (level0_relator 1))

theorem edge1022Inv : Holds level0Subgroup PresentedGroup.of representative ⟨447, [(true, false)], 446⟩ :=
  holds_reverse edge1022

theorem edge1023 : Holds level0Subgroup PresentedGroup.of representative ⟨448, [(true, true)], 449⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨335, [(true, true)], 448⟩ :=
    edge447
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨449, [(true, true)], 335⟩ :=
    edge448Inv
  exact scanFacts hp hs (holds_relator 335 (level0Relator 1) (level0_relator 1))

theorem edge1023Inv : Holds level0Subgroup PresentedGroup.of representative ⟨449, [(true, false)], 448⟩ :=
  holds_reverse edge1023


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
