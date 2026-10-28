module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges15

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

theorem edge1024 : Holds level0Subgroup PresentedGroup.of representative ⟨450, [(true, true)], 451⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨338, [(true, true)], 450⟩ :=
    edge449
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨451, [(true, true)], 338⟩ :=
    edge450Inv
  exact scanFacts hp hs (holds_relator 338 (level0Relator 1) (level0_relator 1))

theorem edge1024Inv : Holds level0Subgroup PresentedGroup.of representative ⟨451, [(true, false)], 450⟩ :=
  holds_reverse edge1024

theorem edge1025 : Holds level0Subgroup PresentedGroup.of representative ⟨452, [(false, true)], 339⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨339, [(false, true)], 452⟩ :=
    edge451
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨339, [], 339⟩ :=
    (holds_refl 339)
  exact scanFacts hp hs (holds_relator 339 (level0Relator 0) (level0_relator 0))

theorem edge1025Inv : Holds level0Subgroup PresentedGroup.of representative ⟨339, [(false, false)], 452⟩ :=
  holds_reverse edge1025

theorem edge1026 : Holds level0Subgroup PresentedGroup.of representative ⟨453, [(false, true)], 340⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨340, [(false, true)], 453⟩ :=
    edge452
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨340, [], 340⟩ :=
    (holds_refl 340)
  exact scanFacts hp hs (holds_relator 340 (level0Relator 0) (level0_relator 0))

theorem edge1026Inv : Holds level0Subgroup PresentedGroup.of representative ⟨340, [(false, false)], 453⟩ :=
  holds_reverse edge1026

theorem edge1027 : Holds level0Subgroup PresentedGroup.of representative ⟨454, [(false, true)], 341⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨341, [(false, true)], 454⟩ :=
    edge453
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨341, [], 341⟩ :=
    (holds_refl 341)
  exact scanFacts hp hs (holds_relator 341 (level0Relator 0) (level0_relator 0))

theorem edge1027Inv : Holds level0Subgroup PresentedGroup.of representative ⟨341, [(false, false)], 454⟩ :=
  holds_reverse edge1027

theorem edge1028 : Holds level0Subgroup PresentedGroup.of representative ⟨455, [(false, true)], 342⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨342, [(false, true)], 455⟩ :=
    edge454
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨342, [], 342⟩ :=
    (holds_refl 342)
  exact scanFacts hp hs (holds_relator 342 (level0Relator 0) (level0_relator 0))

theorem edge1028Inv : Holds level0Subgroup PresentedGroup.of representative ⟨342, [(false, false)], 455⟩ :=
  holds_reverse edge1028

theorem edge1029 : Holds level0Subgroup PresentedGroup.of representative ⟨456, [(false, true)], 344⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨344, [(false, true)], 456⟩ :=
    edge455
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨344, [], 344⟩ :=
    (holds_refl 344)
  exact scanFacts hp hs (holds_relator 344 (level0Relator 0) (level0_relator 0))

theorem edge1029Inv : Holds level0Subgroup PresentedGroup.of representative ⟨344, [(false, false)], 456⟩ :=
  holds_reverse edge1029

theorem edge1030 : Holds level0Subgroup PresentedGroup.of representative ⟨457, [(false, true)], 346⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨346, [(false, true)], 457⟩ :=
    edge456
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨346, [], 346⟩ :=
    (holds_refl 346)
  exact scanFacts hp hs (holds_relator 346 (level0Relator 0) (level0_relator 0))

theorem edge1030Inv : Holds level0Subgroup PresentedGroup.of representative ⟨346, [(false, false)], 457⟩ :=
  holds_reverse edge1030

theorem edge1031 : Holds level0Subgroup PresentedGroup.of representative ⟨458, [(false, true)], 347⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨347, [(false, true)], 458⟩ :=
    edge457
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨347, [], 347⟩ :=
    (holds_refl 347)
  exact scanFacts hp hs (holds_relator 347 (level0Relator 0) (level0_relator 0))

theorem edge1031Inv : Holds level0Subgroup PresentedGroup.of representative ⟨347, [(false, false)], 458⟩ :=
  holds_reverse edge1031

theorem edge1032 : Holds level0Subgroup PresentedGroup.of representative ⟨459, [(false, true)], 348⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨348, [(false, true)], 459⟩ :=
    edge458
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨348, [], 348⟩ :=
    (holds_refl 348)
  exact scanFacts hp hs (holds_relator 348 (level0Relator 0) (level0_relator 0))

theorem edge1032Inv : Holds level0Subgroup PresentedGroup.of representative ⟨348, [(false, false)], 459⟩ :=
  holds_reverse edge1032

theorem edge1033 : Holds level0Subgroup PresentedGroup.of representative ⟨460, [(false, true)], 350⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨350, [(false, true)], 460⟩ :=
    edge459
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨350, [], 350⟩ :=
    (holds_refl 350)
  exact scanFacts hp hs (holds_relator 350 (level0Relator 0) (level0_relator 0))

theorem edge1033Inv : Holds level0Subgroup PresentedGroup.of representative ⟨350, [(false, false)], 460⟩ :=
  holds_reverse edge1033

theorem edge1034 : Holds level0Subgroup PresentedGroup.of representative ⟨461, [(false, true)], 351⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨351, [(false, true)], 461⟩ :=
    edge460
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨351, [], 351⟩ :=
    (holds_refl 351)
  exact scanFacts hp hs (holds_relator 351 (level0Relator 0) (level0_relator 0))

theorem edge1034Inv : Holds level0Subgroup PresentedGroup.of representative ⟨351, [(false, false)], 461⟩ :=
  holds_reverse edge1034

theorem edge1035 : Holds level0Subgroup PresentedGroup.of representative ⟨462, [(false, true)], 352⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨352, [(false, true)], 462⟩ :=
    edge461
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨352, [], 352⟩ :=
    (holds_refl 352)
  exact scanFacts hp hs (holds_relator 352 (level0Relator 0) (level0_relator 0))

theorem edge1035Inv : Holds level0Subgroup PresentedGroup.of representative ⟨352, [(false, false)], 462⟩ :=
  holds_reverse edge1035

theorem edge1036 : Holds level0Subgroup PresentedGroup.of representative ⟨463, [(false, true)], 355⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨355, [(false, true)], 463⟩ :=
    edge462
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨355, [], 355⟩ :=
    (holds_refl 355)
  exact scanFacts hp hs (holds_relator 355 (level0Relator 0) (level0_relator 0))

theorem edge1036Inv : Holds level0Subgroup PresentedGroup.of representative ⟨355, [(false, false)], 463⟩ :=
  holds_reverse edge1036

theorem edge1037 : Holds level0Subgroup PresentedGroup.of representative ⟨464, [(false, true)], 356⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨356, [(false, true)], 464⟩ :=
    edge463
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨356, [], 356⟩ :=
    (holds_refl 356)
  exact scanFacts hp hs (holds_relator 356 (level0Relator 0) (level0_relator 0))

theorem edge1037Inv : Holds level0Subgroup PresentedGroup.of representative ⟨356, [(false, false)], 464⟩ :=
  holds_reverse edge1037

theorem edge1038 : Holds level0Subgroup PresentedGroup.of representative ⟨465, [(false, true)], 357⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨357, [(false, true)], 465⟩ :=
    edge464
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨357, [], 357⟩ :=
    (holds_refl 357)
  exact scanFacts hp hs (holds_relator 357 (level0Relator 0) (level0_relator 0))

theorem edge1038Inv : Holds level0Subgroup PresentedGroup.of representative ⟨357, [(false, false)], 465⟩ :=
  holds_reverse edge1038

theorem edge1039 : Holds level0Subgroup PresentedGroup.of representative ⟨466, [(false, true)], 358⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨358, [(false, true)], 466⟩ :=
    edge465
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨358, [], 358⟩ :=
    (holds_refl 358)
  exact scanFacts hp hs (holds_relator 358 (level0Relator 0) (level0_relator 0))

theorem edge1039Inv : Holds level0Subgroup PresentedGroup.of representative ⟨358, [(false, false)], 466⟩ :=
  holds_reverse edge1039

theorem edge1040 : Holds level0Subgroup PresentedGroup.of representative ⟨467, [(false, true)], 359⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨359, [(false, true)], 467⟩ :=
    edge466
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨359, [], 359⟩ :=
    (holds_refl 359)
  exact scanFacts hp hs (holds_relator 359 (level0Relator 0) (level0_relator 0))

theorem edge1040Inv : Holds level0Subgroup PresentedGroup.of representative ⟨359, [(false, false)], 467⟩ :=
  holds_reverse edge1040

theorem edge1041 : Holds level0Subgroup PresentedGroup.of representative ⟨468, [(false, true)], 360⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨360, [(false, true)], 468⟩ :=
    edge467
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨360, [], 360⟩ :=
    (holds_refl 360)
  exact scanFacts hp hs (holds_relator 360 (level0Relator 0) (level0_relator 0))

theorem edge1041Inv : Holds level0Subgroup PresentedGroup.of representative ⟨360, [(false, false)], 468⟩ :=
  holds_reverse edge1041

theorem edge1042 : Holds level0Subgroup PresentedGroup.of representative ⟨469, [(false, true)], 361⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨361, [(false, true)], 469⟩ :=
    edge468
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨361, [], 361⟩ :=
    (holds_refl 361)
  exact scanFacts hp hs (holds_relator 361 (level0Relator 0) (level0_relator 0))

theorem edge1042Inv : Holds level0Subgroup PresentedGroup.of representative ⟨361, [(false, false)], 469⟩ :=
  holds_reverse edge1042

theorem edge1043 : Holds level0Subgroup PresentedGroup.of representative ⟨470, [(false, true)], 362⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨362, [(false, true)], 470⟩ :=
    edge469
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨362, [], 362⟩ :=
    (holds_refl 362)
  exact scanFacts hp hs (holds_relator 362 (level0Relator 0) (level0_relator 0))

theorem edge1043Inv : Holds level0Subgroup PresentedGroup.of representative ⟨362, [(false, false)], 470⟩ :=
  holds_reverse edge1043

theorem edge1044 : Holds level0Subgroup PresentedGroup.of representative ⟨471, [(false, true)], 363⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨363, [(false, true)], 471⟩ :=
    edge470
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨363, [], 363⟩ :=
    (holds_refl 363)
  exact scanFacts hp hs (holds_relator 363 (level0Relator 0) (level0_relator 0))

theorem edge1044Inv : Holds level0Subgroup PresentedGroup.of representative ⟨363, [(false, false)], 471⟩ :=
  holds_reverse edge1044

theorem edge1045 : Holds level0Subgroup PresentedGroup.of representative ⟨472, [(false, true)], 364⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨364, [(false, true)], 472⟩ :=
    edge471
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨364, [], 364⟩ :=
    (holds_refl 364)
  exact scanFacts hp hs (holds_relator 364 (level0Relator 0) (level0_relator 0))

theorem edge1045Inv : Holds level0Subgroup PresentedGroup.of representative ⟨364, [(false, false)], 472⟩ :=
  holds_reverse edge1045

theorem edge1046 : Holds level0Subgroup PresentedGroup.of representative ⟨473, [(false, true)], 365⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨365, [(false, true)], 473⟩ :=
    edge472
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨365, [], 365⟩ :=
    (holds_refl 365)
  exact scanFacts hp hs (holds_relator 365 (level0Relator 0) (level0_relator 0))

theorem edge1046Inv : Holds level0Subgroup PresentedGroup.of representative ⟨365, [(false, false)], 473⟩ :=
  holds_reverse edge1046

theorem edge1047 : Holds level0Subgroup PresentedGroup.of representative ⟨474, [(false, true)], 366⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨366, [(false, true)], 474⟩ :=
    edge473
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨366, [], 366⟩ :=
    (holds_refl 366)
  exact scanFacts hp hs (holds_relator 366 (level0Relator 0) (level0_relator 0))

theorem edge1047Inv : Holds level0Subgroup PresentedGroup.of representative ⟨366, [(false, false)], 474⟩ :=
  holds_reverse edge1047

theorem edge1048 : Holds level0Subgroup PresentedGroup.of representative ⟨475, [(false, true)], 367⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨367, [(false, true)], 475⟩ :=
    edge474
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨367, [], 367⟩ :=
    (holds_refl 367)
  exact scanFacts hp hs (holds_relator 367 (level0Relator 0) (level0_relator 0))

theorem edge1048Inv : Holds level0Subgroup PresentedGroup.of representative ⟨367, [(false, false)], 475⟩ :=
  holds_reverse edge1048

theorem edge1049 : Holds level0Subgroup PresentedGroup.of representative ⟨476, [(false, true)], 368⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨368, [(false, true)], 476⟩ :=
    edge475
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨368, [], 368⟩ :=
    (holds_refl 368)
  exact scanFacts hp hs (holds_relator 368 (level0Relator 0) (level0_relator 0))

theorem edge1049Inv : Holds level0Subgroup PresentedGroup.of representative ⟨368, [(false, false)], 476⟩ :=
  holds_reverse edge1049

theorem edge1050 : Holds level0Subgroup PresentedGroup.of representative ⟨477, [(false, true)], 369⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨369, [(false, true)], 477⟩ :=
    edge476
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨369, [], 369⟩ :=
    (holds_refl 369)
  exact scanFacts hp hs (holds_relator 369 (level0Relator 0) (level0_relator 0))

theorem edge1050Inv : Holds level0Subgroup PresentedGroup.of representative ⟨369, [(false, false)], 477⟩ :=
  holds_reverse edge1050

theorem edge1051 : Holds level0Subgroup PresentedGroup.of representative ⟨478, [(false, true)], 370⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨370, [(false, true)], 478⟩ :=
    edge477
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨370, [], 370⟩ :=
    (holds_refl 370)
  exact scanFacts hp hs (holds_relator 370 (level0Relator 0) (level0_relator 0))

theorem edge1051Inv : Holds level0Subgroup PresentedGroup.of representative ⟨370, [(false, false)], 478⟩ :=
  holds_reverse edge1051

theorem edge1052 : Holds level0Subgroup PresentedGroup.of representative ⟨478, [(true, false)], 467⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨370, [(false, true)], 478⟩ :=
    edge477
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨467, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 370⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1040 (appendFacts edge358Inv edge900)) (appendFacts edge195Inv (appendFacts edge810 edge785Inv))) (appendFacts (appendFacts edge146 (appendFacts edge194 edge275)) (appendFacts (appendFacts edge705 edge919) (appendFacts edge214Inv edge820)))) (appendFacts (appendFacts (appendFacts edge115Inv (appendFacts edge769 edge61Inv)) (appendFacts edge741 (appendFacts edge732Inv edge43))) (appendFacts (appendFacts edge60 (appendFacts edge83 edge114)) (appendFacts (appendFacts edge156 edge213) (appendFacts edge293 edge984Inv)))))
  exact scanFacts hp hs (holds_relator 370 (level0Relator 2) (level0_relator 2))

theorem edge1052Inv : Holds level0Subgroup PresentedGroup.of representative ⟨467, [(true, true)], 478⟩ :=
  holds_reverse edge1052

theorem edge1053 : Holds level0Subgroup PresentedGroup.of representative ⟨479, [(false, true)], 372⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨372, [(false, true)], 479⟩ :=
    edge478
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨372, [], 372⟩ :=
    (holds_refl 372)
  exact scanFacts hp hs (holds_relator 372 (level0Relator 0) (level0_relator 0))

theorem edge1053Inv : Holds level0Subgroup PresentedGroup.of representative ⟨372, [(false, false)], 479⟩ :=
  holds_reverse edge1053

theorem edge1054 : Holds level0Subgroup PresentedGroup.of representative ⟨480, [(false, true)], 373⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨373, [(false, true)], 480⟩ :=
    edge479
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨373, [], 373⟩ :=
    (holds_refl 373)
  exact scanFacts hp hs (holds_relator 373 (level0Relator 0) (level0_relator 0))

theorem edge1054Inv : Holds level0Subgroup PresentedGroup.of representative ⟨373, [(false, false)], 480⟩ :=
  holds_reverse edge1054

theorem edge1055 : Holds level0Subgroup PresentedGroup.of representative ⟨481, [(false, true)], 374⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨374, [(false, true)], 481⟩ :=
    edge480
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨374, [], 374⟩ :=
    (holds_refl 374)
  exact scanFacts hp hs (holds_relator 374 (level0Relator 0) (level0_relator 0))

theorem edge1055Inv : Holds level0Subgroup PresentedGroup.of representative ⟨374, [(false, false)], 481⟩ :=
  holds_reverse edge1055

theorem edge1056 : Holds level0Subgroup PresentedGroup.of representative ⟨482, [(false, true)], 375⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨375, [(false, true)], 482⟩ :=
    edge481
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨375, [], 375⟩ :=
    (holds_refl 375)
  exact scanFacts hp hs (holds_relator 375 (level0Relator 0) (level0_relator 0))

theorem edge1056Inv : Holds level0Subgroup PresentedGroup.of representative ⟨375, [(false, false)], 482⟩ :=
  holds_reverse edge1056

theorem edge1057 : Holds level0Subgroup PresentedGroup.of representative ⟨376, [(false, true)], 447⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨376, [], 376⟩ :=
    (holds_refl 376)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨447, [(false, true)], 376⟩ :=
    edge989
  exact scanFacts hp hs (holds_relator 376 (level0Relator 0) (level0_relator 0))

theorem edge1057Inv : Holds level0Subgroup PresentedGroup.of representative ⟨447, [(false, false)], 376⟩ :=
  holds_reverse edge1057

theorem edge1058 : Holds level0Subgroup PresentedGroup.of representative ⟨483, [(false, true)], 377⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨377, [(false, true)], 483⟩ :=
    edge482
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨377, [], 377⟩ :=
    (holds_refl 377)
  exact scanFacts hp hs (holds_relator 377 (level0Relator 0) (level0_relator 0))

theorem edge1058Inv : Holds level0Subgroup PresentedGroup.of representative ⟨377, [(false, false)], 483⟩ :=
  holds_reverse edge1058

theorem edge1059 : Holds level0Subgroup PresentedGroup.of representative ⟨484, [(false, true)], 378⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨378, [(false, true)], 484⟩ :=
    edge483
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨378, [], 378⟩ :=
    (holds_refl 378)
  exact scanFacts hp hs (holds_relator 378 (level0Relator 0) (level0_relator 0))

theorem edge1059Inv : Holds level0Subgroup PresentedGroup.of representative ⟨378, [(false, false)], 484⟩ :=
  holds_reverse edge1059

theorem edge1060 : Holds level0Subgroup PresentedGroup.of representative ⟨485, [(false, true)], 380⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨380, [(false, true)], 485⟩ :=
    edge484
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨380, [], 380⟩ :=
    (holds_refl 380)
  exact scanFacts hp hs (holds_relator 380 (level0Relator 0) (level0_relator 0))

theorem edge1060Inv : Holds level0Subgroup PresentedGroup.of representative ⟨380, [(false, false)], 485⟩ :=
  holds_reverse edge1060

theorem edge1061 : Holds level0Subgroup PresentedGroup.of representative ⟨486, [(false, true)], 381⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨381, [(false, true)], 486⟩ :=
    edge485
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨381, [], 381⟩ :=
    (holds_refl 381)
  exact scanFacts hp hs (holds_relator 381 (level0Relator 0) (level0_relator 0))

theorem edge1061Inv : Holds level0Subgroup PresentedGroup.of representative ⟨381, [(false, false)], 486⟩ :=
  holds_reverse edge1061

theorem edge1062 : Holds level0Subgroup PresentedGroup.of representative ⟨487, [(false, true)], 383⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨383, [(false, true)], 487⟩ :=
    edge486
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨383, [], 383⟩ :=
    (holds_refl 383)
  exact scanFacts hp hs (holds_relator 383 (level0Relator 0) (level0_relator 0))

theorem edge1062Inv : Holds level0Subgroup PresentedGroup.of representative ⟨383, [(false, false)], 487⟩ :=
  holds_reverse edge1062

theorem edge1063 : Holds level0Subgroup PresentedGroup.of representative ⟨488, [(false, true)], 389⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨389, [(false, true)], 488⟩ :=
    edge487
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨389, [], 389⟩ :=
    (holds_refl 389)
  exact scanFacts hp hs (holds_relator 389 (level0Relator 0) (level0_relator 0))

theorem edge1063Inv : Holds level0Subgroup PresentedGroup.of representative ⟨389, [(false, false)], 488⟩ :=
  holds_reverse edge1063

theorem edge1064 : Holds level0Subgroup PresentedGroup.of representative ⟨489, [(false, true)], 390⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨390, [(false, true)], 489⟩ :=
    edge488
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨390, [], 390⟩ :=
    (holds_refl 390)
  exact scanFacts hp hs (holds_relator 390 (level0Relator 0) (level0_relator 0))

theorem edge1064Inv : Holds level0Subgroup PresentedGroup.of representative ⟨390, [(false, false)], 489⟩ :=
  holds_reverse edge1064

theorem edge1065 : Holds level0Subgroup PresentedGroup.of representative ⟨490, [(false, true)], 391⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨391, [(false, true)], 490⟩ :=
    edge489
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨391, [], 391⟩ :=
    (holds_refl 391)
  exact scanFacts hp hs (holds_relator 391 (level0Relator 0) (level0_relator 0))

theorem edge1065Inv : Holds level0Subgroup PresentedGroup.of representative ⟨391, [(false, false)], 490⟩ :=
  holds_reverse edge1065

theorem edge1066 : Holds level0Subgroup PresentedGroup.of representative ⟨491, [(false, true)], 393⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨393, [(false, true)], 491⟩ :=
    edge490
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨393, [], 393⟩ :=
    (holds_refl 393)
  exact scanFacts hp hs (holds_relator 393 (level0Relator 0) (level0_relator 0))

theorem edge1066Inv : Holds level0Subgroup PresentedGroup.of representative ⟨393, [(false, false)], 491⟩ :=
  holds_reverse edge1066

theorem edge1067 : Holds level0Subgroup PresentedGroup.of representative ⟨492, [(false, true)], 394⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨394, [(false, true)], 492⟩ :=
    edge491
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨394, [], 394⟩ :=
    (holds_refl 394)
  exact scanFacts hp hs (holds_relator 394 (level0Relator 0) (level0_relator 0))

theorem edge1067Inv : Holds level0Subgroup PresentedGroup.of representative ⟨394, [(false, false)], 492⟩ :=
  holds_reverse edge1067

theorem edge1068 : Holds level0Subgroup PresentedGroup.of representative ⟨493, [(false, true)], 395⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨395, [(false, true)], 493⟩ :=
    edge492
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨395, [], 395⟩ :=
    (holds_refl 395)
  exact scanFacts hp hs (holds_relator 395 (level0Relator 0) (level0_relator 0))

theorem edge1068Inv : Holds level0Subgroup PresentedGroup.of representative ⟨395, [(false, false)], 493⟩ :=
  holds_reverse edge1068

theorem edge1069 : Holds level0Subgroup PresentedGroup.of representative ⟨494, [(false, true)], 396⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨396, [(false, true)], 494⟩ :=
    edge493
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨396, [], 396⟩ :=
    (holds_refl 396)
  exact scanFacts hp hs (holds_relator 396 (level0Relator 0) (level0_relator 0))

theorem edge1069Inv : Holds level0Subgroup PresentedGroup.of representative ⟨396, [(false, false)], 494⟩ :=
  holds_reverse edge1069

theorem edge1070 : Holds level0Subgroup PresentedGroup.of representative ⟨495, [(false, true)], 397⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨397, [(false, true)], 495⟩ :=
    edge494
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨397, [], 397⟩ :=
    (holds_refl 397)
  exact scanFacts hp hs (holds_relator 397 (level0Relator 0) (level0_relator 0))

theorem edge1070Inv : Holds level0Subgroup PresentedGroup.of representative ⟨397, [(false, false)], 495⟩ :=
  holds_reverse edge1070

theorem edge1071 : Holds level0Subgroup PresentedGroup.of representative ⟨496, [(false, true)], 399⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨399, [(false, true)], 496⟩ :=
    edge495
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨399, [], 399⟩ :=
    (holds_refl 399)
  exact scanFacts hp hs (holds_relator 399 (level0Relator 0) (level0_relator 0))

theorem edge1071Inv : Holds level0Subgroup PresentedGroup.of representative ⟨399, [(false, false)], 496⟩ :=
  holds_reverse edge1071

theorem edge1072 : Holds level0Subgroup PresentedGroup.of representative ⟨497, [(false, true)], 400⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨400, [(false, true)], 497⟩ :=
    edge496
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨400, [], 400⟩ :=
    (holds_refl 400)
  exact scanFacts hp hs (holds_relator 400 (level0Relator 0) (level0_relator 0))

theorem edge1072Inv : Holds level0Subgroup PresentedGroup.of representative ⟨400, [(false, false)], 497⟩ :=
  holds_reverse edge1072

theorem edge1073 : Holds level0Subgroup PresentedGroup.of representative ⟨498, [(false, true)], 401⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨401, [(false, true)], 498⟩ :=
    edge497
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨401, [], 401⟩ :=
    (holds_refl 401)
  exact scanFacts hp hs (holds_relator 401 (level0Relator 0) (level0_relator 0))

theorem edge1073Inv : Holds level0Subgroup PresentedGroup.of representative ⟨401, [(false, false)], 498⟩ :=
  holds_reverse edge1073

theorem edge1074 : Holds level0Subgroup PresentedGroup.of representative ⟨499, [(false, true)], 402⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨402, [(false, true)], 499⟩ :=
    edge498
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨402, [], 402⟩ :=
    (holds_refl 402)
  exact scanFacts hp hs (holds_relator 402 (level0Relator 0) (level0_relator 0))

theorem edge1074Inv : Holds level0Subgroup PresentedGroup.of representative ⟨402, [(false, false)], 499⟩ :=
  holds_reverse edge1074

theorem edge1075 : Holds level0Subgroup PresentedGroup.of representative ⟨500, [(false, true)], 403⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨403, [(false, true)], 500⟩ :=
    edge499
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨403, [], 403⟩ :=
    (holds_refl 403)
  exact scanFacts hp hs (holds_relator 403 (level0Relator 0) (level0_relator 0))

theorem edge1075Inv : Holds level0Subgroup PresentedGroup.of representative ⟨403, [(false, false)], 500⟩ :=
  holds_reverse edge1075

theorem edge1076 : Holds level0Subgroup PresentedGroup.of representative ⟨501, [(false, true)], 405⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨405, [(false, true)], 501⟩ :=
    edge500
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨405, [], 405⟩ :=
    (holds_refl 405)
  exact scanFacts hp hs (holds_relator 405 (level0Relator 0) (level0_relator 0))

theorem edge1076Inv : Holds level0Subgroup PresentedGroup.of representative ⟨405, [(false, false)], 501⟩ :=
  holds_reverse edge1076

theorem edge1077 : Holds level0Subgroup PresentedGroup.of representative ⟨407, [(false, true)], 426⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨407, [], 407⟩ :=
    (holds_refl 407)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨426, [(false, true)], 407⟩ :=
    edge948
  exact scanFacts hp hs (holds_relator 407 (level0Relator 0) (level0_relator 0))

theorem edge1077Inv : Holds level0Subgroup PresentedGroup.of representative ⟨426, [(false, false)], 407⟩ :=
  holds_reverse edge1077

theorem edge1078 : Holds level0Subgroup PresentedGroup.of representative ⟨502, [(false, true)], 409⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨409, [(false, true)], 502⟩ :=
    edge501
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨409, [], 409⟩ :=
    (holds_refl 409)
  exact scanFacts hp hs (holds_relator 409 (level0Relator 0) (level0_relator 0))

theorem edge1078Inv : Holds level0Subgroup PresentedGroup.of representative ⟨409, [(false, false)], 502⟩ :=
  holds_reverse edge1078

theorem edge1079 : Holds level0Subgroup PresentedGroup.of representative ⟨503, [(false, true)], 410⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨410, [(false, true)], 503⟩ :=
    edge502
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨410, [], 410⟩ :=
    (holds_refl 410)
  exact scanFacts hp hs (holds_relator 410 (level0Relator 0) (level0_relator 0))

theorem edge1079Inv : Holds level0Subgroup PresentedGroup.of representative ⟨410, [(false, false)], 503⟩ :=
  holds_reverse edge1079

theorem edge1080 : Holds level0Subgroup PresentedGroup.of representative ⟨504, [(false, true)], 411⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨411, [(false, true)], 504⟩ :=
    edge503
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨411, [], 411⟩ :=
    (holds_refl 411)
  exact scanFacts hp hs (holds_relator 411 (level0Relator 0) (level0_relator 0))

theorem edge1080Inv : Holds level0Subgroup PresentedGroup.of representative ⟨411, [(false, false)], 504⟩ :=
  holds_reverse edge1080

theorem edge1081 : Holds level0Subgroup PresentedGroup.of representative ⟨505, [(false, true)], 412⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨412, [(false, true)], 505⟩ :=
    edge504
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨412, [], 412⟩ :=
    (holds_refl 412)
  exact scanFacts hp hs (holds_relator 412 (level0Relator 0) (level0_relator 0))

theorem edge1081Inv : Holds level0Subgroup PresentedGroup.of representative ⟨412, [(false, false)], 505⟩ :=
  holds_reverse edge1081

theorem edge1082 : Holds level0Subgroup PresentedGroup.of representative ⟨506, [(false, true)], 413⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨413, [(false, true)], 506⟩ :=
    edge505
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨413, [], 413⟩ :=
    (holds_refl 413)
  exact scanFacts hp hs (holds_relator 413 (level0Relator 0) (level0_relator 0))

theorem edge1082Inv : Holds level0Subgroup PresentedGroup.of representative ⟨413, [(false, false)], 506⟩ :=
  holds_reverse edge1082

theorem edge1083 : Holds level0Subgroup PresentedGroup.of representative ⟨507, [(false, true)], 414⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨414, [(false, true)], 507⟩ :=
    edge506
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨414, [], 414⟩ :=
    (holds_refl 414)
  exact scanFacts hp hs (holds_relator 414 (level0Relator 0) (level0_relator 0))

theorem edge1083Inv : Holds level0Subgroup PresentedGroup.of representative ⟨414, [(false, false)], 507⟩ :=
  holds_reverse edge1083

theorem edge1084 : Holds level0Subgroup PresentedGroup.of representative ⟨508, [(false, true)], 415⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨415, [(false, true)], 508⟩ :=
    edge507
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨415, [], 415⟩ :=
    (holds_refl 415)
  exact scanFacts hp hs (holds_relator 415 (level0Relator 0) (level0_relator 0))

theorem edge1084Inv : Holds level0Subgroup PresentedGroup.of representative ⟨415, [(false, false)], 508⟩ :=
  holds_reverse edge1084

theorem edge1085 : Holds level0Subgroup PresentedGroup.of representative ⟨509, [(false, true)], 417⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨417, [(false, true)], 509⟩ :=
    edge508
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨417, [], 417⟩ :=
    (holds_refl 417)
  exact scanFacts hp hs (holds_relator 417 (level0Relator 0) (level0_relator 0))

theorem edge1085Inv : Holds level0Subgroup PresentedGroup.of representative ⟨417, [(false, false)], 509⟩ :=
  holds_reverse edge1085

theorem edge1086 : Holds level0Subgroup PresentedGroup.of representative ⟨510, [(false, true)], 419⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨419, [(false, true)], 510⟩ :=
    edge509
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨419, [], 419⟩ :=
    (holds_refl 419)
  exact scanFacts hp hs (holds_relator 419 (level0Relator 0) (level0_relator 0))

theorem edge1086Inv : Holds level0Subgroup PresentedGroup.of representative ⟨419, [(false, false)], 510⟩ :=
  holds_reverse edge1086

theorem edge1087 : Holds level0Subgroup PresentedGroup.of representative ⟨511, [(false, true)], 420⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨420, [(false, true)], 511⟩ :=
    edge510
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨420, [], 420⟩ :=
    (holds_refl 420)
  exact scanFacts hp hs (holds_relator 420 (level0Relator 0) (level0_relator 0))

theorem edge1087Inv : Holds level0Subgroup PresentedGroup.of representative ⟨420, [(false, false)], 511⟩ :=
  holds_reverse edge1087


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
