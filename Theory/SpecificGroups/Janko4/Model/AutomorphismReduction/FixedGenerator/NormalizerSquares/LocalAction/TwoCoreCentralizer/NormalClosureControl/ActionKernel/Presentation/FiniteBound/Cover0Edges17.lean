module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges16

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

theorem edge1088 : Holds level0Subgroup PresentedGroup.of representative ⟨512, [(false, true)], 422⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨422, [(false, true)], 512⟩ :=
    edge511
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨422, [], 422⟩ :=
    (holds_refl 422)
  exact scanFacts hp hs (holds_relator 422 (level0Relator 0) (level0_relator 0))

theorem edge1088Inv : Holds level0Subgroup PresentedGroup.of representative ⟨422, [(false, false)], 512⟩ :=
  holds_reverse edge1088

theorem edge1089 : Holds level0Subgroup PresentedGroup.of representative ⟨513, [(false, true)], 424⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨424, [(false, true)], 513⟩ :=
    edge512
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨424, [], 424⟩ :=
    (holds_refl 424)
  exact scanFacts hp hs (holds_relator 424 (level0Relator 0) (level0_relator 0))

theorem edge1089Inv : Holds level0Subgroup PresentedGroup.of representative ⟨424, [(false, false)], 513⟩ :=
  holds_reverse edge1089

theorem edge1090 : Holds level0Subgroup PresentedGroup.of representative ⟨514, [(false, true)], 425⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨425, [(false, true)], 514⟩ :=
    edge513
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨425, [], 425⟩ :=
    (holds_refl 425)
  exact scanFacts hp hs (holds_relator 425 (level0Relator 0) (level0_relator 0))

theorem edge1090Inv : Holds level0Subgroup PresentedGroup.of representative ⟨425, [(false, false)], 514⟩ :=
  holds_reverse edge1090

theorem edge1091 : Holds level0Subgroup PresentedGroup.of representative ⟨515, [(false, true)], 427⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨427, [(false, true)], 515⟩ :=
    edge514
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨427, [], 427⟩ :=
    (holds_refl 427)
  exact scanFacts hp hs (holds_relator 427 (level0Relator 0) (level0_relator 0))

theorem edge1091Inv : Holds level0Subgroup PresentedGroup.of representative ⟨427, [(false, false)], 515⟩ :=
  holds_reverse edge1091

theorem edge1092 : Holds level0Subgroup PresentedGroup.of representative ⟨516, [(false, true)], 428⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨428, [(false, true)], 516⟩ :=
    edge515
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨428, [], 428⟩ :=
    (holds_refl 428)
  exact scanFacts hp hs (holds_relator 428 (level0Relator 0) (level0_relator 0))

theorem edge1092Inv : Holds level0Subgroup PresentedGroup.of representative ⟨428, [(false, false)], 516⟩ :=
  holds_reverse edge1092

theorem edge1093 : Holds level0Subgroup PresentedGroup.of representative ⟨517, [(false, true)], 429⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨429, [(false, true)], 517⟩ :=
    edge516
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨429, [], 429⟩ :=
    (holds_refl 429)
  exact scanFacts hp hs (holds_relator 429 (level0Relator 0) (level0_relator 0))

theorem edge1093Inv : Holds level0Subgroup PresentedGroup.of representative ⟨429, [(false, false)], 517⟩ :=
  holds_reverse edge1093

theorem edge1094 : Holds level0Subgroup PresentedGroup.of representative ⟨518, [(false, true)], 430⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨430, [(false, true)], 518⟩ :=
    edge517
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨430, [], 430⟩ :=
    (holds_refl 430)
  exact scanFacts hp hs (holds_relator 430 (level0Relator 0) (level0_relator 0))

theorem edge1094Inv : Holds level0Subgroup PresentedGroup.of representative ⟨430, [(false, false)], 518⟩ :=
  holds_reverse edge1094

theorem edge1095 : Holds level0Subgroup PresentedGroup.of representative ⟨519, [(false, true)], 431⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨431, [(false, true)], 519⟩ :=
    edge518
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨431, [], 431⟩ :=
    (holds_refl 431)
  exact scanFacts hp hs (holds_relator 431 (level0Relator 0) (level0_relator 0))

theorem edge1095Inv : Holds level0Subgroup PresentedGroup.of representative ⟨431, [(false, false)], 519⟩ :=
  holds_reverse edge1095

theorem edge1096 : Holds level0Subgroup PresentedGroup.of representative ⟨520, [(false, true)], 435⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨435, [(false, true)], 520⟩ :=
    edge519
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨435, [], 435⟩ :=
    (holds_refl 435)
  exact scanFacts hp hs (holds_relator 435 (level0Relator 0) (level0_relator 0))

theorem edge1096Inv : Holds level0Subgroup PresentedGroup.of representative ⟨435, [(false, false)], 520⟩ :=
  holds_reverse edge1096

theorem edge1097 : Holds level0Subgroup PresentedGroup.of representative ⟨521, [(false, true)], 436⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨436, [(false, true)], 521⟩ :=
    edge520
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨436, [], 436⟩ :=
    (holds_refl 436)
  exact scanFacts hp hs (holds_relator 436 (level0Relator 0) (level0_relator 0))

theorem edge1097Inv : Holds level0Subgroup PresentedGroup.of representative ⟨436, [(false, false)], 521⟩ :=
  holds_reverse edge1097

theorem edge1098 : Holds level0Subgroup PresentedGroup.of representative ⟨522, [(false, true)], 438⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨438, [(false, true)], 522⟩ :=
    edge521
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨438, [], 438⟩ :=
    (holds_refl 438)
  exact scanFacts hp hs (holds_relator 438 (level0Relator 0) (level0_relator 0))

theorem edge1098Inv : Holds level0Subgroup PresentedGroup.of representative ⟨438, [(false, false)], 522⟩ :=
  holds_reverse edge1098

theorem edge1099 : Holds level0Subgroup PresentedGroup.of representative ⟨523, [(false, true)], 441⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨441, [(false, true)], 523⟩ :=
    edge522
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨441, [], 441⟩ :=
    (holds_refl 441)
  exact scanFacts hp hs (holds_relator 441 (level0Relator 0) (level0_relator 0))

theorem edge1099Inv : Holds level0Subgroup PresentedGroup.of representative ⟨441, [(false, false)], 523⟩ :=
  holds_reverse edge1099

theorem edge1100 : Holds level0Subgroup PresentedGroup.of representative ⟨524, [(false, true)], 443⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨443, [(false, true)], 524⟩ :=
    edge523
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨443, [], 443⟩ :=
    (holds_refl 443)
  exact scanFacts hp hs (holds_relator 443 (level0Relator 0) (level0_relator 0))

theorem edge1100Inv : Holds level0Subgroup PresentedGroup.of representative ⟨443, [(false, false)], 524⟩ :=
  holds_reverse edge1100

theorem edge1101 : Holds level0Subgroup PresentedGroup.of representative ⟨525, [(false, true)], 444⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨444, [(false, true)], 525⟩ :=
    edge524
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨444, [], 444⟩ :=
    (holds_refl 444)
  exact scanFacts hp hs (holds_relator 444 (level0Relator 0) (level0_relator 0))

theorem edge1101Inv : Holds level0Subgroup PresentedGroup.of representative ⟨444, [(false, false)], 525⟩ :=
  holds_reverse edge1101

theorem edge1102 : Holds level0Subgroup PresentedGroup.of representative ⟨526, [(false, true)], 445⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨445, [(false, true)], 526⟩ :=
    edge525
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨445, [], 445⟩ :=
    (holds_refl 445)
  exact scanFacts hp hs (holds_relator 445 (level0Relator 0) (level0_relator 0))

theorem edge1102Inv : Holds level0Subgroup PresentedGroup.of representative ⟨445, [(false, false)], 526⟩ :=
  holds_reverse edge1102

theorem edge1103 : Holds level0Subgroup PresentedGroup.of representative ⟨527, [(false, true)], 446⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨446, [(false, true)], 527⟩ :=
    edge526
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨446, [], 446⟩ :=
    (holds_refl 446)
  exact scanFacts hp hs (holds_relator 446 (level0Relator 0) (level0_relator 0))

theorem edge1103Inv : Holds level0Subgroup PresentedGroup.of representative ⟨446, [(false, false)], 527⟩ :=
  holds_reverse edge1103

theorem edge1104 : Holds level0Subgroup PresentedGroup.of representative ⟨528, [(false, true)], 448⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨448, [(false, true)], 528⟩ :=
    edge527
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨448, [], 448⟩ :=
    (holds_refl 448)
  exact scanFacts hp hs (holds_relator 448 (level0Relator 0) (level0_relator 0))

theorem edge1104Inv : Holds level0Subgroup PresentedGroup.of representative ⟨448, [(false, false)], 528⟩ :=
  holds_reverse edge1104

theorem edge1105 : Holds level0Subgroup PresentedGroup.of representative ⟨529, [(false, true)], 449⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨449, [(false, true)], 529⟩ :=
    edge528
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨449, [], 449⟩ :=
    (holds_refl 449)
  exact scanFacts hp hs (holds_relator 449 (level0Relator 0) (level0_relator 0))

theorem edge1105Inv : Holds level0Subgroup PresentedGroup.of representative ⟨449, [(false, false)], 529⟩ :=
  holds_reverse edge1105

theorem edge1106 : Holds level0Subgroup PresentedGroup.of representative ⟨530, [(false, true)], 450⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨450, [(false, true)], 530⟩ :=
    edge529
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨450, [], 450⟩ :=
    (holds_refl 450)
  exact scanFacts hp hs (holds_relator 450 (level0Relator 0) (level0_relator 0))

theorem edge1106Inv : Holds level0Subgroup PresentedGroup.of representative ⟨450, [(false, false)], 530⟩ :=
  holds_reverse edge1106

theorem edge1107 : Holds level0Subgroup PresentedGroup.of representative ⟨531, [(false, true)], 451⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨451, [(false, true)], 531⟩ :=
    edge530
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨451, [], 451⟩ :=
    (holds_refl 451)
  exact scanFacts hp hs (holds_relator 451 (level0Relator 0) (level0_relator 0))

theorem edge1107Inv : Holds level0Subgroup PresentedGroup.of representative ⟨451, [(false, false)], 531⟩ :=
  holds_reverse edge1107

theorem edge1108 : Holds level0Subgroup PresentedGroup.of representative ⟨624, [(false, true)], 532⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨451, [(false, true), (true, false)], 624⟩ :=
    (appendFacts edge530 edge623)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨532, [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 451⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge531Inv (appendFacts edge1025 edge338Inv)) (appendFacts edge888 (appendFacts edge183Inv edge804))) (appendFacts (appendFacts edge97Inv (appendFacts edge760 edge51Inv)) (appendFacts edge736 (appendFacts edge27Inv edge724)))) (appendFacts (appendFacts (appendFacts edge719Inv (appendFacts edge693 edge722Inv)) (appendFacts edge26 (appendFacts edge38 edge50))) (appendFacts (appendFacts edge74 (appendFacts edge96 edge140)) (appendFacts (appendFacts edge182 edge263) (appendFacts edge337 edge450)))))
  exact scanFacts hp hs (holds_relator 451 (level0Relator 2) (level0_relator 2))

theorem edge1108Inv : Holds level0Subgroup PresentedGroup.of representative ⟨532, [(false, false)], 624⟩ :=
  holds_reverse edge1108

theorem edge1109 : Holds level0Subgroup PresentedGroup.of representative ⟨533, [(true, true)], 534⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨453, [(true, true)], 533⟩ :=
    edge532
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨534, [(true, true)], 453⟩ :=
    edge533Inv
  exact scanFacts hp hs (holds_relator 453 (level0Relator 1) (level0_relator 1))

theorem edge1109Inv : Holds level0Subgroup PresentedGroup.of representative ⟨534, [(true, false)], 533⟩ :=
  holds_reverse edge1109

theorem edge1110 : Holds level0Subgroup PresentedGroup.of representative ⟨535, [(true, true)], 536⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨454, [(true, true)], 535⟩ :=
    edge534
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨536, [(true, true)], 454⟩ :=
    edge535Inv
  exact scanFacts hp hs (holds_relator 454 (level0Relator 1) (level0_relator 1))

theorem edge1110Inv : Holds level0Subgroup PresentedGroup.of representative ⟨536, [(true, false)], 535⟩ :=
  holds_reverse edge1110

theorem edge1111 : Holds level0Subgroup PresentedGroup.of representative ⟨537, [(true, true)], 538⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨455, [(true, true)], 537⟩ :=
    edge536
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨538, [(true, true)], 455⟩ :=
    edge537Inv
  exact scanFacts hp hs (holds_relator 455 (level0Relator 1) (level0_relator 1))

theorem edge1111Inv : Holds level0Subgroup PresentedGroup.of representative ⟨538, [(true, false)], 537⟩ :=
  holds_reverse edge1111

theorem edge1112 : Holds level0Subgroup PresentedGroup.of representative ⟨463, [(true, false)], 464⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨464, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)], 463⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1037 (appendFacts edge355Inv edge898)) (appendFacts edge193Inv (appendFacts edge809 edge103Inv))) (appendFacts (appendFacts edge763 (appendFacts edge55Inv edge738)) (appendFacts (appendFacts edge29Inv edge725) (appendFacts edge15Inv edge716)))) (appendFacts (appendFacts (appendFacts edge713Inv (appendFacts edge9 edge14)) (appendFacts (appendFacts edge21 edge28) (appendFacts edge40 edge54))) (appendFacts (appendFacts edge77 (appendFacts edge102 edge145)) (appendFacts (appendFacts edge192 edge273) (appendFacts edge354 edge462)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨464, [], 464⟩ :=
    (holds_refl 464)
  exact scanFacts hp hs (holds_relator 464 (level0Relator 2) (level0_relator 2))

theorem edge1112Inv : Holds level0Subgroup PresentedGroup.of representative ⟨464, [(true, true)], 463⟩ :=
  holds_reverse edge1112

theorem edge1113 : Holds level0Subgroup PresentedGroup.of representative ⟨546, [(true, true)], 547⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨466, [(true, true)], 546⟩ :=
    edge545
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨547, [(true, true)], 466⟩ :=
    edge546Inv
  exact scanFacts hp hs (holds_relator 466 (level0Relator 1) (level0_relator 1))

theorem edge1113Inv : Holds level0Subgroup PresentedGroup.of representative ⟨547, [(true, false)], 546⟩ :=
  holds_reverse edge1113

theorem edge1114 : Holds level0Subgroup PresentedGroup.of representative ⟨478, [(true, true)], 548⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨467, [(true, true)], 478⟩ :=
    edge1052Inv
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨548, [(true, true)], 467⟩ :=
    edge547Inv
  exact scanFacts hp hs (holds_relator 467 (level0Relator 1) (level0_relator 1))

theorem edge1114Inv : Holds level0Subgroup PresentedGroup.of representative ⟨548, [(true, false)], 478⟩ :=
  holds_reverse edge1114

theorem edge1115 : Holds level0Subgroup PresentedGroup.of representative ⟨549, [(true, true)], 550⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨469, [(true, true)], 549⟩ :=
    edge548
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨550, [(true, true)], 469⟩ :=
    edge549Inv
  exact scanFacts hp hs (holds_relator 469 (level0Relator 1) (level0_relator 1))

theorem edge1115Inv : Holds level0Subgroup PresentedGroup.of representative ⟨550, [(true, false)], 549⟩ :=
  holds_reverse edge1115

theorem edge1116 : Holds level0Subgroup PresentedGroup.of representative ⟨553, [(true, true)], 554⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨472, [(true, true)], 553⟩ :=
    edge552
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨554, [(true, true)], 472⟩ :=
    edge553Inv
  exact scanFacts hp hs (holds_relator 472 (level0Relator 1) (level0_relator 1))

theorem edge1116Inv : Holds level0Subgroup PresentedGroup.of representative ⟨554, [(true, false)], 553⟩ :=
  holds_reverse edge1116

theorem edge1117 : Holds level0Subgroup PresentedGroup.of representative ⟨555, [(true, true)], 556⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨473, [(true, true)], 555⟩ :=
    edge554
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨556, [(true, true)], 473⟩ :=
    edge555Inv
  exact scanFacts hp hs (holds_relator 473 (level0Relator 1) (level0_relator 1))

theorem edge1117Inv : Holds level0Subgroup PresentedGroup.of representative ⟨556, [(true, false)], 555⟩ :=
  holds_reverse edge1117

theorem edge1118 : Holds level0Subgroup PresentedGroup.of representative ⟨557, [(true, true)], 558⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨474, [(true, true)], 557⟩ :=
    edge556
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨558, [(true, true)], 474⟩ :=
    edge557Inv
  exact scanFacts hp hs (holds_relator 474 (level0Relator 1) (level0_relator 1))

theorem edge1118Inv : Holds level0Subgroup PresentedGroup.of representative ⟨558, [(true, false)], 557⟩ :=
  holds_reverse edge1118

theorem edge1119 : Holds level0Subgroup PresentedGroup.of representative ⟨559, [(true, true)], 560⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨475, [(true, true)], 559⟩ :=
    edge558
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨560, [(true, true)], 475⟩ :=
    edge559Inv
  exact scanFacts hp hs (holds_relator 475 (level0Relator 1) (level0_relator 1))

theorem edge1119Inv : Holds level0Subgroup PresentedGroup.of representative ⟨560, [(true, false)], 559⟩ :=
  holds_reverse edge1119

theorem edge1120 : Holds level0Subgroup PresentedGroup.of representative ⟨562, [(true, true)], 563⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨477, [(true, true)], 562⟩ :=
    edge561
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨563, [(true, true)], 477⟩ :=
    edge562Inv
  exact scanFacts hp hs (holds_relator 477 (level0Relator 1) (level0_relator 1))

theorem edge1120Inv : Holds level0Subgroup PresentedGroup.of representative ⟨563, [(true, false)], 562⟩ :=
  holds_reverse edge1120

theorem edge1121 : Holds level0Subgroup PresentedGroup.of representative ⟨564, [(true, true)], 565⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨479, [(true, true)], 564⟩ :=
    edge563
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨565, [(true, true)], 479⟩ :=
    edge564Inv
  exact scanFacts hp hs (holds_relator 479 (level0Relator 1) (level0_relator 1))

theorem edge1121Inv : Holds level0Subgroup PresentedGroup.of representative ⟨565, [(true, false)], 564⟩ :=
  holds_reverse edge1121

theorem edge1122 : Holds level0Subgroup PresentedGroup.of representative ⟨566, [(true, true)], 567⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨480, [(true, true)], 566⟩ :=
    edge565
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨567, [(true, true)], 480⟩ :=
    edge566Inv
  exact scanFacts hp hs (holds_relator 480 (level0Relator 1) (level0_relator 1))

theorem edge1122Inv : Holds level0Subgroup PresentedGroup.of representative ⟨567, [(true, false)], 566⟩ :=
  holds_reverse edge1122

theorem edge1123 : Holds level0Subgroup PresentedGroup.of representative ⟨568, [(true, true)], 569⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨481, [(true, true)], 568⟩ :=
    edge567
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨569, [(true, true)], 481⟩ :=
    edge568Inv
  exact scanFacts hp hs (holds_relator 481 (level0Relator 1) (level0_relator 1))

theorem edge1123Inv : Holds level0Subgroup PresentedGroup.of representative ⟨569, [(true, false)], 568⟩ :=
  holds_reverse edge1123

theorem edge1124 : Holds level0Subgroup PresentedGroup.of representative ⟨570, [(true, true)], 571⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨484, [(true, true)], 570⟩ :=
    edge569
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨571, [(true, true)], 484⟩ :=
    edge570Inv
  exact scanFacts hp hs (holds_relator 484 (level0Relator 1) (level0_relator 1))

theorem edge1124Inv : Holds level0Subgroup PresentedGroup.of representative ⟨571, [(true, false)], 570⟩ :=
  holds_reverse edge1124

theorem edge1125 : Holds level0Subgroup PresentedGroup.of representative ⟨574, [(true, true)], 575⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨489, [(true, true)], 574⟩ :=
    edge573
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨575, [(true, true)], 489⟩ :=
    edge574Inv
  exact scanFacts hp hs (holds_relator 489 (level0Relator 1) (level0_relator 1))

theorem edge1125Inv : Holds level0Subgroup PresentedGroup.of representative ⟨575, [(true, false)], 574⟩ :=
  holds_reverse edge1125

theorem edge1126 : Holds level0Subgroup PresentedGroup.of representative ⟨576, [(true, true)], 577⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨490, [(true, true)], 576⟩ :=
    edge575
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨577, [(true, true)], 490⟩ :=
    edge576Inv
  exact scanFacts hp hs (holds_relator 490 (level0Relator 1) (level0_relator 1))

theorem edge1126Inv : Holds level0Subgroup PresentedGroup.of representative ⟨577, [(true, false)], 576⟩ :=
  holds_reverse edge1126

theorem edge1127 : Holds level0Subgroup PresentedGroup.of representative ⟨578, [(true, true)], 579⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨491, [(true, true)], 578⟩ :=
    edge577
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨579, [(true, true)], 491⟩ :=
    edge578Inv
  exact scanFacts hp hs (holds_relator 491 (level0Relator 1) (level0_relator 1))

theorem edge1127Inv : Holds level0Subgroup PresentedGroup.of representative ⟨579, [(true, false)], 578⟩ :=
  holds_reverse edge1127

theorem edge1128 : Holds level0Subgroup PresentedGroup.of representative ⟨580, [(true, true)], 581⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨493, [(true, true)], 580⟩ :=
    edge579
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨581, [(true, true)], 493⟩ :=
    edge580Inv
  exact scanFacts hp hs (holds_relator 493 (level0Relator 1) (level0_relator 1))

theorem edge1128Inv : Holds level0Subgroup PresentedGroup.of representative ⟨581, [(true, false)], 580⟩ :=
  holds_reverse edge1128

theorem edge1129 : Holds level0Subgroup PresentedGroup.of representative ⟨582, [(true, true)], 583⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨495, [(true, true)], 582⟩ :=
    edge581
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨583, [(true, true)], 495⟩ :=
    edge582Inv
  exact scanFacts hp hs (holds_relator 495 (level0Relator 1) (level0_relator 1))

theorem edge1129Inv : Holds level0Subgroup PresentedGroup.of representative ⟨583, [(true, false)], 582⟩ :=
  holds_reverse edge1129

theorem edge1130 : Holds level0Subgroup PresentedGroup.of representative ⟨584, [(true, true)], 585⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨496, [(true, true)], 584⟩ :=
    edge583
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨585, [(true, true)], 496⟩ :=
    edge584Inv
  exact scanFacts hp hs (holds_relator 496 (level0Relator 1) (level0_relator 1))

theorem edge1130Inv : Holds level0Subgroup PresentedGroup.of representative ⟨585, [(true, false)], 584⟩ :=
  holds_reverse edge1130

theorem edge1131 : Holds level0Subgroup PresentedGroup.of representative ⟨586, [(true, true)], 587⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨498, [(true, true)], 586⟩ :=
    edge585
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨587, [(true, true)], 498⟩ :=
    edge586Inv
  exact scanFacts hp hs (holds_relator 498 (level0Relator 1) (level0_relator 1))

theorem edge1131Inv : Holds level0Subgroup PresentedGroup.of representative ⟨587, [(true, false)], 586⟩ :=
  holds_reverse edge1131

theorem edge1132 : Holds level0Subgroup PresentedGroup.of representative ⟨588, [(true, true)], 589⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨499, [(true, true)], 588⟩ :=
    edge587
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨589, [(true, true)], 499⟩ :=
    edge588Inv
  exact scanFacts hp hs (holds_relator 499 (level0Relator 1) (level0_relator 1))

theorem edge1132Inv : Holds level0Subgroup PresentedGroup.of representative ⟨589, [(true, false)], 588⟩ :=
  holds_reverse edge1132

theorem edge1133 : Holds level0Subgroup PresentedGroup.of representative ⟨590, [(true, true)], 591⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨500, [(true, true)], 590⟩ :=
    edge589
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨591, [(true, true)], 500⟩ :=
    edge590Inv
  exact scanFacts hp hs (holds_relator 500 (level0Relator 1) (level0_relator 1))

theorem edge1133Inv : Holds level0Subgroup PresentedGroup.of representative ⟨591, [(true, false)], 590⟩ :=
  holds_reverse edge1133

theorem edge1134 : Holds level0Subgroup PresentedGroup.of representative ⟨592, [(true, true)], 593⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨501, [(true, true)], 592⟩ :=
    edge591
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨593, [(true, true)], 501⟩ :=
    edge592Inv
  exact scanFacts hp hs (holds_relator 501 (level0Relator 1) (level0_relator 1))

theorem edge1134Inv : Holds level0Subgroup PresentedGroup.of representative ⟨593, [(true, false)], 592⟩ :=
  holds_reverse edge1134

theorem edge1135 : Holds level0Subgroup PresentedGroup.of representative ⟨594, [(true, true)], 595⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨502, [(true, true)], 594⟩ :=
    edge593
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨595, [(true, true)], 502⟩ :=
    edge594Inv
  exact scanFacts hp hs (holds_relator 502 (level0Relator 1) (level0_relator 1))

theorem edge1135Inv : Holds level0Subgroup PresentedGroup.of representative ⟨595, [(true, false)], 594⟩ :=
  holds_reverse edge1135

theorem edge1136 : Holds level0Subgroup PresentedGroup.of representative ⟨596, [(true, true)], 597⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨505, [(true, true)], 596⟩ :=
    edge595
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨597, [(true, true)], 505⟩ :=
    edge596Inv
  exact scanFacts hp hs (holds_relator 505 (level0Relator 1) (level0_relator 1))

theorem edge1136Inv : Holds level0Subgroup PresentedGroup.of representative ⟨597, [(true, false)], 596⟩ :=
  holds_reverse edge1136

theorem edge1137 : Holds level0Subgroup PresentedGroup.of representative ⟨599, [(true, true)], 600⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨511, [(true, true)], 599⟩ :=
    edge598
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨600, [(true, true)], 511⟩ :=
    edge599Inv
  exact scanFacts hp hs (holds_relator 511 (level0Relator 1) (level0_relator 1))

theorem edge1137Inv : Holds level0Subgroup PresentedGroup.of representative ⟨600, [(true, false)], 599⟩ :=
  holds_reverse edge1137

theorem edge1138 : Holds level0Subgroup PresentedGroup.of representative ⟨601, [(true, true)], 602⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨512, [(true, true)], 601⟩ :=
    edge600
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨602, [(true, true)], 512⟩ :=
    edge601Inv
  exact scanFacts hp hs (holds_relator 512 (level0Relator 1) (level0_relator 1))

theorem edge1138Inv : Holds level0Subgroup PresentedGroup.of representative ⟨602, [(true, false)], 601⟩ :=
  holds_reverse edge1138

theorem edge1139 : Holds level0Subgroup PresentedGroup.of representative ⟨603, [(true, true)], 604⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨513, [(true, true)], 603⟩ :=
    edge602
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨604, [(true, true)], 513⟩ :=
    edge603Inv
  exact scanFacts hp hs (holds_relator 513 (level0Relator 1) (level0_relator 1))

theorem edge1139Inv : Holds level0Subgroup PresentedGroup.of representative ⟨604, [(true, false)], 603⟩ :=
  holds_reverse edge1139

theorem edge1140 : Holds level0Subgroup PresentedGroup.of representative ⟨516, [(true, false)], 517⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨517, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)], 516⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1093 (appendFacts edge428Inv edge950)) (appendFacts edge248Inv (appendFacts edge838 edge133Inv))) (appendFacts (appendFacts edge778 (appendFacts edge71Inv edge746)) (appendFacts (appendFacts edge37Inv edge729) (appendFacts edge19Inv edge718)))) (appendFacts (appendFacts (appendFacts edge714Inv (appendFacts edge11 edge18)) (appendFacts (appendFacts edge25 edge36) (appendFacts edge48 edge70))) (appendFacts (appendFacts edge92 (appendFacts edge132 edge174)) (appendFacts (appendFacts edge247 edge321) (appendFacts edge427 edge515)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨517, [], 517⟩ :=
    (holds_refl 517)
  exact scanFacts hp hs (holds_relator 517 (level0Relator 2) (level0_relator 2))

theorem edge1140Inv : Holds level0Subgroup PresentedGroup.of representative ⟨517, [(true, true)], 516⟩ :=
  holds_reverse edge1140

theorem edge1141 : Holds level0Subgroup PresentedGroup.of representative ⟨607, [(true, true)], 608⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨518, [(true, true)], 607⟩ :=
    edge606
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨608, [(true, true)], 518⟩ :=
    edge607Inv
  exact scanFacts hp hs (holds_relator 518 (level0Relator 1) (level0_relator 1))

theorem edge1141Inv : Holds level0Subgroup PresentedGroup.of representative ⟨608, [(true, false)], 607⟩ :=
  holds_reverse edge1141

theorem edge1142 : Holds level0Subgroup PresentedGroup.of representative ⟨609, [(true, true)], 610⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨521, [(true, true)], 609⟩ :=
    edge608
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨610, [(true, true)], 521⟩ :=
    edge609Inv
  exact scanFacts hp hs (holds_relator 521 (level0Relator 1) (level0_relator 1))

theorem edge1142Inv : Holds level0Subgroup PresentedGroup.of representative ⟨610, [(true, false)], 609⟩ :=
  holds_reverse edge1142

theorem edge1143 : Holds level0Subgroup PresentedGroup.of representative ⟨611, [(true, true)], 612⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨522, [(true, true)], 611⟩ :=
    edge610
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨612, [(true, true)], 522⟩ :=
    edge611Inv
  exact scanFacts hp hs (holds_relator 522 (level0Relator 1) (level0_relator 1))

theorem edge1143Inv : Holds level0Subgroup PresentedGroup.of representative ⟨612, [(true, false)], 611⟩ :=
  holds_reverse edge1143

theorem edge1144 : Holds level0Subgroup PresentedGroup.of representative ⟨613, [(true, true)], 614⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨524, [(true, true)], 613⟩ :=
    edge612
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨614, [(true, true)], 524⟩ :=
    edge613Inv
  exact scanFacts hp hs (holds_relator 524 (level0Relator 1) (level0_relator 1))

theorem edge1144Inv : Holds level0Subgroup PresentedGroup.of representative ⟨614, [(true, false)], 613⟩ :=
  holds_reverse edge1144

theorem edge1145 : Holds level0Subgroup PresentedGroup.of representative ⟨615, [(true, true)], 616⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨525, [(true, true)], 615⟩ :=
    edge614
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨616, [(true, true)], 525⟩ :=
    edge615Inv
  exact scanFacts hp hs (holds_relator 525 (level0Relator 1) (level0_relator 1))

theorem edge1145Inv : Holds level0Subgroup PresentedGroup.of representative ⟨616, [(true, false)], 615⟩ :=
  holds_reverse edge1145

theorem edge1146 : Holds level0Subgroup PresentedGroup.of representative ⟨617, [(true, true)], 618⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨527, [(true, true)], 617⟩ :=
    edge616
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨618, [(true, true)], 527⟩ :=
    edge617Inv
  exact scanFacts hp hs (holds_relator 527 (level0Relator 1) (level0_relator 1))

theorem edge1146Inv : Holds level0Subgroup PresentedGroup.of representative ⟨618, [(true, false)], 617⟩ :=
  holds_reverse edge1146

theorem edge1147 : Holds level0Subgroup PresentedGroup.of representative ⟨619, [(true, true)], 620⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨529, [(true, true)], 619⟩ :=
    edge618
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨620, [(true, true)], 529⟩ :=
    edge619Inv
  exact scanFacts hp hs (holds_relator 529 (level0Relator 1) (level0_relator 1))

theorem edge1147Inv : Holds level0Subgroup PresentedGroup.of representative ⟨620, [(true, false)], 619⟩ :=
  holds_reverse edge1147

theorem edge1148 : Holds level0Subgroup PresentedGroup.of representative ⟨621, [(true, true)], 622⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨530, [(true, true)], 621⟩ :=
    edge620
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨622, [(true, true)], 530⟩ :=
    edge621Inv
  exact scanFacts hp hs (holds_relator 530 (level0Relator 1) (level0_relator 1))

theorem edge1148Inv : Holds level0Subgroup PresentedGroup.of representative ⟨622, [(true, false)], 621⟩ :=
  holds_reverse edge1148

theorem edge1149 : Holds level0Subgroup PresentedGroup.of representative ⟨623, [(true, true)], 624⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨531, [(true, true)], 623⟩ :=
    edge622
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨624, [(true, true)], 531⟩ :=
    edge623Inv
  exact scanFacts hp hs (holds_relator 531 (level0Relator 1) (level0_relator 1))

theorem edge1149Inv : Holds level0Subgroup PresentedGroup.of representative ⟨624, [(true, false)], 623⟩ :=
  holds_reverse edge1149

theorem edge1150 : Holds level0Subgroup PresentedGroup.of representative ⟨532, [(false, true)], 624⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨532, [], 532⟩ :=
    (holds_refl 532)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨624, [(false, true)], 532⟩ :=
    edge1108
  exact scanFacts hp hs (holds_relator 532 (level0Relator 0) (level0_relator 0))

theorem edge1150Inv : Holds level0Subgroup PresentedGroup.of representative ⟨624, [(false, false)], 532⟩ :=
  holds_reverse edge1150

theorem edge1151 : Holds level0Subgroup PresentedGroup.of representative ⟨625, [(false, true)], 538⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨538, [(false, true)], 625⟩ :=
    edge624
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨538, [], 538⟩ :=
    (holds_refl 538)
  exact scanFacts hp hs (holds_relator 538 (level0Relator 0) (level0_relator 0))

theorem edge1151Inv : Holds level0Subgroup PresentedGroup.of representative ⟨538, [(false, false)], 625⟩ :=
  holds_reverse edge1151


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
