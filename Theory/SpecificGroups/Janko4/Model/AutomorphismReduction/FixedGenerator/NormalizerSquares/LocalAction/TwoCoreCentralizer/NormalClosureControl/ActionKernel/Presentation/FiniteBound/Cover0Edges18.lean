module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges17

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

theorem edge1152 : Holds level0Subgroup PresentedGroup.of representative ⟨544, [(true, true)], 464⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨544, [], 544⟩ :=
    (holds_refl 544)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨464, [(true, true), (true, true)], 544⟩ :=
    (appendFacts edge1112Inv edge543)
  exact scanFacts hp hs (holds_relator 544 (level0Relator 1) (level0_relator 1))

theorem edge1152Inv : Holds level0Subgroup PresentedGroup.of representative ⟨464, [(true, false)], 544⟩ :=
  holds_reverse edge1152

theorem edge1153 : Holds level0Subgroup PresentedGroup.of representative ⟨626, [(false, true)], 545⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨545, [(false, true)], 626⟩ :=
    edge625
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨545, [], 545⟩ :=
    (holds_refl 545)
  exact scanFacts hp hs (holds_relator 545 (level0Relator 0) (level0_relator 0))

theorem edge1153Inv : Holds level0Subgroup PresentedGroup.of representative ⟨545, [(false, false)], 626⟩ :=
  holds_reverse edge1153

theorem edge1154 : Holds level0Subgroup PresentedGroup.of representative ⟨627, [(false, true)], 547⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨547, [(false, true)], 627⟩ :=
    edge626
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨547, [], 547⟩ :=
    (holds_refl 547)
  exact scanFacts hp hs (holds_relator 547 (level0Relator 0) (level0_relator 0))

theorem edge1154Inv : Holds level0Subgroup PresentedGroup.of representative ⟨547, [(false, false)], 627⟩ :=
  holds_reverse edge1154

theorem edge1155 : Holds level0Subgroup PresentedGroup.of representative ⟨628, [(false, true)], 548⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨548, [(false, true)], 628⟩ :=
    edge627
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨548, [], 548⟩ :=
    (holds_refl 548)
  exact scanFacts hp hs (holds_relator 548 (level0Relator 0) (level0_relator 0))

theorem edge1155Inv : Holds level0Subgroup PresentedGroup.of representative ⟨548, [(false, false)], 628⟩ :=
  holds_reverse edge1155

theorem edge1156 : Holds level0Subgroup PresentedGroup.of representative ⟨629, [(false, true)], 549⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨549, [(false, true)], 629⟩ :=
    edge628
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨549, [], 549⟩ :=
    (holds_refl 549)
  exact scanFacts hp hs (holds_relator 549 (level0Relator 0) (level0_relator 0))

theorem edge1156Inv : Holds level0Subgroup PresentedGroup.of representative ⟨549, [(false, false)], 629⟩ :=
  holds_reverse edge1156

theorem edge1157 : Holds level0Subgroup PresentedGroup.of representative ⟨630, [(false, true)], 551⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨551, [(false, true)], 630⟩ :=
    edge629
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨551, [], 551⟩ :=
    (holds_refl 551)
  exact scanFacts hp hs (holds_relator 551 (level0Relator 0) (level0_relator 0))

theorem edge1157Inv : Holds level0Subgroup PresentedGroup.of representative ⟨551, [(false, false)], 630⟩ :=
  holds_reverse edge1157

theorem edge1158 : Holds level0Subgroup PresentedGroup.of representative ⟨631, [(false, true)], 555⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨555, [(false, true)], 631⟩ :=
    edge630
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨555, [], 555⟩ :=
    (holds_refl 555)
  exact scanFacts hp hs (holds_relator 555 (level0Relator 0) (level0_relator 0))

theorem edge1158Inv : Holds level0Subgroup PresentedGroup.of representative ⟨555, [(false, false)], 631⟩ :=
  holds_reverse edge1158

theorem edge1159 : Holds level0Subgroup PresentedGroup.of representative ⟨632, [(false, true)], 556⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨556, [(false, true)], 632⟩ :=
    edge631
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨556, [], 556⟩ :=
    (holds_refl 556)
  exact scanFacts hp hs (holds_relator 556 (level0Relator 0) (level0_relator 0))

theorem edge1159Inv : Holds level0Subgroup PresentedGroup.of representative ⟨556, [(false, false)], 632⟩ :=
  holds_reverse edge1159

theorem edge1160 : Holds level0Subgroup PresentedGroup.of representative ⟨633, [(false, true)], 557⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨557, [(false, true)], 633⟩ :=
    edge632
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨557, [], 557⟩ :=
    (holds_refl 557)
  exact scanFacts hp hs (holds_relator 557 (level0Relator 0) (level0_relator 0))

theorem edge1160Inv : Holds level0Subgroup PresentedGroup.of representative ⟨557, [(false, false)], 633⟩ :=
  holds_reverse edge1160

theorem edge1161 : Holds level0Subgroup PresentedGroup.of representative ⟨634, [(false, true)], 559⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨559, [(false, true)], 634⟩ :=
    edge633
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨559, [], 559⟩ :=
    (holds_refl 559)
  exact scanFacts hp hs (holds_relator 559 (level0Relator 0) (level0_relator 0))

theorem edge1161Inv : Holds level0Subgroup PresentedGroup.of representative ⟨559, [(false, false)], 634⟩ :=
  holds_reverse edge1161

theorem edge1162 : Holds level0Subgroup PresentedGroup.of representative ⟨635, [(false, true)], 563⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨563, [(false, true)], 635⟩ :=
    edge634
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨563, [], 563⟩ :=
    (holds_refl 563)
  exact scanFacts hp hs (holds_relator 563 (level0Relator 0) (level0_relator 0))

theorem edge1162Inv : Holds level0Subgroup PresentedGroup.of representative ⟨563, [(false, false)], 635⟩ :=
  holds_reverse edge1162

theorem edge1163 : Holds level0Subgroup PresentedGroup.of representative ⟨636, [(false, true)], 564⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨564, [(false, true)], 636⟩ :=
    edge635
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨564, [], 564⟩ :=
    (holds_refl 564)
  exact scanFacts hp hs (holds_relator 564 (level0Relator 0) (level0_relator 0))

theorem edge1163Inv : Holds level0Subgroup PresentedGroup.of representative ⟨564, [(false, false)], 636⟩ :=
  holds_reverse edge1163

theorem edge1164 : Holds level0Subgroup PresentedGroup.of representative ⟨637, [(false, true)], 565⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨565, [(false, true)], 637⟩ :=
    edge636
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨565, [], 565⟩ :=
    (holds_refl 565)
  exact scanFacts hp hs (holds_relator 565 (level0Relator 0) (level0_relator 0))

theorem edge1164Inv : Holds level0Subgroup PresentedGroup.of representative ⟨565, [(false, false)], 637⟩ :=
  holds_reverse edge1164

theorem edge1165 : Holds level0Subgroup PresentedGroup.of representative ⟨638, [(false, true)], 566⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨566, [(false, true)], 638⟩ :=
    edge637
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨566, [], 566⟩ :=
    (holds_refl 566)
  exact scanFacts hp hs (holds_relator 566 (level0Relator 0) (level0_relator 0))

theorem edge1165Inv : Holds level0Subgroup PresentedGroup.of representative ⟨566, [(false, false)], 638⟩ :=
  holds_reverse edge1165

theorem edge1166 : Holds level0Subgroup PresentedGroup.of representative ⟨639, [(false, true)], 567⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨567, [(false, true)], 639⟩ :=
    edge638
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨567, [], 567⟩ :=
    (holds_refl 567)
  exact scanFacts hp hs (holds_relator 567 (level0Relator 0) (level0_relator 0))

theorem edge1166Inv : Holds level0Subgroup PresentedGroup.of representative ⟨567, [(false, false)], 639⟩ :=
  holds_reverse edge1166

theorem edge1167 : Holds level0Subgroup PresentedGroup.of representative ⟨640, [(false, true)], 569⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨569, [(false, true)], 640⟩ :=
    edge639
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨569, [], 569⟩ :=
    (holds_refl 569)
  exact scanFacts hp hs (holds_relator 569 (level0Relator 0) (level0_relator 0))

theorem edge1167Inv : Holds level0Subgroup PresentedGroup.of representative ⟨569, [(false, false)], 640⟩ :=
  holds_reverse edge1167

theorem edge1168 : Holds level0Subgroup PresentedGroup.of representative ⟨641, [(false, true)], 570⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨570, [(false, true)], 641⟩ :=
    edge640
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨570, [], 570⟩ :=
    (holds_refl 570)
  exact scanFacts hp hs (holds_relator 570 (level0Relator 0) (level0_relator 0))

theorem edge1168Inv : Holds level0Subgroup PresentedGroup.of representative ⟨570, [(false, false)], 641⟩ :=
  holds_reverse edge1168

theorem edge1169 : Holds level0Subgroup PresentedGroup.of representative ⟨642, [(false, true)], 573⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨573, [(false, true)], 642⟩ :=
    edge641
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨573, [], 573⟩ :=
    (holds_refl 573)
  exact scanFacts hp hs (holds_relator 573 (level0Relator 0) (level0_relator 0))

theorem edge1169Inv : Holds level0Subgroup PresentedGroup.of representative ⟨573, [(false, false)], 642⟩ :=
  holds_reverse edge1169

theorem edge1170 : Holds level0Subgroup PresentedGroup.of representative ⟨643, [(false, true)], 576⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨576, [(false, true)], 643⟩ :=
    edge642
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨576, [], 576⟩ :=
    (holds_refl 576)
  exact scanFacts hp hs (holds_relator 576 (level0Relator 0) (level0_relator 0))

theorem edge1170Inv : Holds level0Subgroup PresentedGroup.of representative ⟨576, [(false, false)], 643⟩ :=
  holds_reverse edge1170

theorem edge1171 : Holds level0Subgroup PresentedGroup.of representative ⟨644, [(false, true)], 578⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨578, [(false, true)], 644⟩ :=
    edge643
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨578, [], 578⟩ :=
    (holds_refl 578)
  exact scanFacts hp hs (holds_relator 578 (level0Relator 0) (level0_relator 0))

theorem edge1171Inv : Holds level0Subgroup PresentedGroup.of representative ⟨578, [(false, false)], 644⟩ :=
  holds_reverse edge1171

theorem edge1172 : Holds level0Subgroup PresentedGroup.of representative ⟨645, [(false, true)], 584⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨584, [(false, true)], 645⟩ :=
    edge644
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨584, [], 584⟩ :=
    (holds_refl 584)
  exact scanFacts hp hs (holds_relator 584 (level0Relator 0) (level0_relator 0))

theorem edge1172Inv : Holds level0Subgroup PresentedGroup.of representative ⟨584, [(false, false)], 645⟩ :=
  holds_reverse edge1172

theorem edge1173 : Holds level0Subgroup PresentedGroup.of representative ⟨646, [(false, true)], 588⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨588, [(false, true)], 646⟩ :=
    edge645
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨588, [], 588⟩ :=
    (holds_refl 588)
  exact scanFacts hp hs (holds_relator 588 (level0Relator 0) (level0_relator 0))

theorem edge1173Inv : Holds level0Subgroup PresentedGroup.of representative ⟨588, [(false, false)], 646⟩ :=
  holds_reverse edge1173

theorem edge1174 : Holds level0Subgroup PresentedGroup.of representative ⟨647, [(false, true)], 589⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨589, [(false, true)], 647⟩ :=
    edge646
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨589, [], 589⟩ :=
    (holds_refl 589)
  exact scanFacts hp hs (holds_relator 589 (level0Relator 0) (level0_relator 0))

theorem edge1174Inv : Holds level0Subgroup PresentedGroup.of representative ⟨589, [(false, false)], 647⟩ :=
  holds_reverse edge1174

theorem edge1175 : Holds level0Subgroup PresentedGroup.of representative ⟨648, [(false, true)], 590⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨590, [(false, true)], 648⟩ :=
    edge647
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨590, [], 590⟩ :=
    (holds_refl 590)
  exact scanFacts hp hs (holds_relator 590 (level0Relator 0) (level0_relator 0))

theorem edge1175Inv : Holds level0Subgroup PresentedGroup.of representative ⟨590, [(false, false)], 648⟩ :=
  holds_reverse edge1175

theorem edge1176 : Holds level0Subgroup PresentedGroup.of representative ⟨649, [(false, true)], 592⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨592, [(false, true)], 649⟩ :=
    edge648
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨592, [], 592⟩ :=
    (holds_refl 592)
  exact scanFacts hp hs (holds_relator 592 (level0Relator 0) (level0_relator 0))

theorem edge1176Inv : Holds level0Subgroup PresentedGroup.of representative ⟨592, [(false, false)], 649⟩ :=
  holds_reverse edge1176

theorem edge1177 : Holds level0Subgroup PresentedGroup.of representative ⟨650, [(false, true)], 593⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨593, [(false, true)], 650⟩ :=
    edge649
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨593, [], 593⟩ :=
    (holds_refl 593)
  exact scanFacts hp hs (holds_relator 593 (level0Relator 0) (level0_relator 0))

theorem edge1177Inv : Holds level0Subgroup PresentedGroup.of representative ⟨593, [(false, false)], 650⟩ :=
  holds_reverse edge1177

theorem edge1178 : Holds level0Subgroup PresentedGroup.of representative ⟨651, [(false, true)], 597⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨597, [(false, true)], 651⟩ :=
    edge650
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨597, [], 597⟩ :=
    (holds_refl 597)
  exact scanFacts hp hs (holds_relator 597 (level0Relator 0) (level0_relator 0))

theorem edge1178Inv : Holds level0Subgroup PresentedGroup.of representative ⟨597, [(false, false)], 651⟩ :=
  holds_reverse edge1178

theorem edge1179 : Holds level0Subgroup PresentedGroup.of representative ⟨652, [(false, true)], 599⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨599, [(false, true)], 652⟩ :=
    edge651
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨599, [], 599⟩ :=
    (holds_refl 599)
  exact scanFacts hp hs (holds_relator 599 (level0Relator 0) (level0_relator 0))

theorem edge1179Inv : Holds level0Subgroup PresentedGroup.of representative ⟨599, [(false, false)], 652⟩ :=
  holds_reverse edge1179

theorem edge1180 : Holds level0Subgroup PresentedGroup.of representative ⟨653, [(false, true)], 601⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨601, [(false, true)], 653⟩ :=
    edge652
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨601, [], 601⟩ :=
    (holds_refl 601)
  exact scanFacts hp hs (holds_relator 601 (level0Relator 0) (level0_relator 0))

theorem edge1180Inv : Holds level0Subgroup PresentedGroup.of representative ⟨601, [(false, false)], 653⟩ :=
  holds_reverse edge1180

theorem edge1181 : Holds level0Subgroup PresentedGroup.of representative ⟨654, [(false, true)], 603⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨603, [(false, true)], 654⟩ :=
    edge653
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨603, [], 603⟩ :=
    (holds_refl 603)
  exact scanFacts hp hs (holds_relator 603 (level0Relator 0) (level0_relator 0))

theorem edge1181Inv : Holds level0Subgroup PresentedGroup.of representative ⟨603, [(false, false)], 654⟩ :=
  holds_reverse edge1181

theorem edge1182 : Holds level0Subgroup PresentedGroup.of representative ⟨655, [(false, true)], 606⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨606, [(false, true)], 655⟩ :=
    edge654
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨606, [], 606⟩ :=
    (holds_refl 606)
  exact scanFacts hp hs (holds_relator 606 (level0Relator 0) (level0_relator 0))

theorem edge1182Inv : Holds level0Subgroup PresentedGroup.of representative ⟨606, [(false, false)], 655⟩ :=
  holds_reverse edge1182

theorem edge1183 : Holds level0Subgroup PresentedGroup.of representative ⟨606, [(true, true)], 517⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨606, [], 606⟩ :=
    (holds_refl 606)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨517, [(true, true), (true, true)], 606⟩ :=
    (appendFacts edge1140Inv edge605)
  exact scanFacts hp hs (holds_relator 606 (level0Relator 1) (level0_relator 1))

theorem edge1183Inv : Holds level0Subgroup PresentedGroup.of representative ⟨517, [(true, false)], 606⟩ :=
  holds_reverse edge1183

theorem edge1184 : Holds level0Subgroup PresentedGroup.of representative ⟨656, [(false, true)], 612⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨612, [(false, true)], 656⟩ :=
    edge655
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨612, [], 612⟩ :=
    (holds_refl 612)
  exact scanFacts hp hs (holds_relator 612 (level0Relator 0) (level0_relator 0))

theorem edge1184Inv : Holds level0Subgroup PresentedGroup.of representative ⟨612, [(false, false)], 656⟩ :=
  holds_reverse edge1184

theorem edge1185 : Holds level0Subgroup PresentedGroup.of representative ⟨657, [(false, true)], 613⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨613, [(false, true)], 657⟩ :=
    edge656
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨613, [], 613⟩ :=
    (holds_refl 613)
  exact scanFacts hp hs (holds_relator 613 (level0Relator 0) (level0_relator 0))

theorem edge1185Inv : Holds level0Subgroup PresentedGroup.of representative ⟨613, [(false, false)], 657⟩ :=
  holds_reverse edge1185

theorem edge1186 : Holds level0Subgroup PresentedGroup.of representative ⟨658, [(false, true)], 615⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨615, [(false, true)], 658⟩ :=
    edge657
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨615, [], 615⟩ :=
    (holds_refl 615)
  exact scanFacts hp hs (holds_relator 615 (level0Relator 0) (level0_relator 0))

theorem edge1186Inv : Holds level0Subgroup PresentedGroup.of representative ⟨615, [(false, false)], 658⟩ :=
  holds_reverse edge1186

theorem edge1187 : Holds level0Subgroup PresentedGroup.of representative ⟨659, [(false, true)], 616⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨616, [(false, true)], 659⟩ :=
    edge658
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨616, [], 616⟩ :=
    (holds_refl 616)
  exact scanFacts hp hs (holds_relator 616 (level0Relator 0) (level0_relator 0))

theorem edge1187Inv : Holds level0Subgroup PresentedGroup.of representative ⟨616, [(false, false)], 659⟩ :=
  holds_reverse edge1187

theorem edge1188 : Holds level0Subgroup PresentedGroup.of representative ⟨660, [(false, true)], 617⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨617, [(false, true)], 660⟩ :=
    edge659
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨617, [], 617⟩ :=
    (holds_refl 617)
  exact scanFacts hp hs (holds_relator 617 (level0Relator 0) (level0_relator 0))

theorem edge1188Inv : Holds level0Subgroup PresentedGroup.of representative ⟨617, [(false, false)], 660⟩ :=
  holds_reverse edge1188

theorem edge1189 : Holds level0Subgroup PresentedGroup.of representative ⟨661, [(false, true)], 619⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨619, [(false, true)], 661⟩ :=
    edge660
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨619, [], 619⟩ :=
    (holds_refl 619)
  exact scanFacts hp hs (holds_relator 619 (level0Relator 0) (level0_relator 0))

theorem edge1189Inv : Holds level0Subgroup PresentedGroup.of representative ⟨619, [(false, false)], 661⟩ :=
  holds_reverse edge1189

theorem edge1190 : Holds level0Subgroup PresentedGroup.of representative ⟨662, [(false, true)], 621⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨621, [(false, true)], 662⟩ :=
    edge661
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨621, [], 621⟩ :=
    (holds_refl 621)
  exact scanFacts hp hs (holds_relator 621 (level0Relator 0) (level0_relator 0))

theorem edge1190Inv : Holds level0Subgroup PresentedGroup.of representative ⟨621, [(false, false)], 662⟩ :=
  holds_reverse edge1190

theorem edge1191 : Holds level0Subgroup PresentedGroup.of representative ⟨663, [(true, true)], 664⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨626, [(true, true)], 663⟩ :=
    edge662
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨664, [(true, true)], 626⟩ :=
    edge663Inv
  exact scanFacts hp hs (holds_relator 626 (level0Relator 1) (level0_relator 1))

theorem edge1191Inv : Holds level0Subgroup PresentedGroup.of representative ⟨664, [(true, false)], 663⟩ :=
  holds_reverse edge1191

theorem edge1192 : Holds level0Subgroup PresentedGroup.of representative ⟨669, [(true, true)], 670⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨637, [(true, true)], 669⟩ :=
    edge668
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨670, [(true, true)], 637⟩ :=
    edge669Inv
  exact scanFacts hp hs (holds_relator 637 (level0Relator 1) (level0_relator 1))

theorem edge1192Inv : Holds level0Subgroup PresentedGroup.of representative ⟨670, [(true, false)], 669⟩ :=
  holds_reverse edge1192

theorem edge1193 : Holds level0Subgroup PresentedGroup.of representative ⟨673, [(true, true)], 674⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨640, [(true, true)], 673⟩ :=
    edge672
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨674, [(true, true)], 640⟩ :=
    edge673Inv
  exact scanFacts hp hs (holds_relator 640 (level0Relator 1) (level0_relator 1))

theorem edge1193Inv : Holds level0Subgroup PresentedGroup.of representative ⟨674, [(true, false)], 673⟩ :=
  holds_reverse edge1193

theorem edge1194 : Holds level0Subgroup PresentedGroup.of representative ⟨678, [(true, true)], 679⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨651, [(true, true)], 678⟩ :=
    edge677
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨679, [(true, true)], 651⟩ :=
    edge678Inv
  exact scanFacts hp hs (holds_relator 651 (level0Relator 1) (level0_relator 1))

theorem edge1194Inv : Holds level0Subgroup PresentedGroup.of representative ⟨679, [(true, false)], 678⟩ :=
  holds_reverse edge1194

theorem edge1195 : Holds level0Subgroup PresentedGroup.of representative ⟨680, [(true, true)], 681⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨655, [(true, true)], 680⟩ :=
    edge679
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨681, [(true, true)], 655⟩ :=
    edge680Inv
  exact scanFacts hp hs (holds_relator 655 (level0Relator 1) (level0_relator 1))

theorem edge1195Inv : Holds level0Subgroup PresentedGroup.of representative ⟨681, [(true, false)], 680⟩ :=
  holds_reverse edge1195

theorem edge1196 : Holds level0Subgroup PresentedGroup.of representative ⟨682, [(true, true)], 683⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨659, [(true, true)], 682⟩ :=
    edge681
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨683, [(true, true)], 659⟩ :=
    edge682Inv
  exact scanFacts hp hs (holds_relator 659 (level0Relator 1) (level0_relator 1))

theorem edge1196Inv : Holds level0Subgroup PresentedGroup.of representative ⟨683, [(true, false)], 682⟩ :=
  holds_reverse edge1196

theorem edge1197 : Holds level0Subgroup PresentedGroup.of representative ⟨684, [(false, true)], 663⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨663, [(false, true)], 684⟩ :=
    edge683
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨663, [], 663⟩ :=
    (holds_refl 663)
  exact scanFacts hp hs (holds_relator 663 (level0Relator 0) (level0_relator 0))

theorem edge1197Inv : Holds level0Subgroup PresentedGroup.of representative ⟨663, [(false, false)], 684⟩ :=
  holds_reverse edge1197

theorem edge1198 : Holds level0Subgroup PresentedGroup.of representative ⟨685, [(false, true)], 665⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨665, [(false, true)], 685⟩ :=
    edge684
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨665, [], 665⟩ :=
    (holds_refl 665)
  exact scanFacts hp hs (holds_relator 665 (level0Relator 0) (level0_relator 0))

theorem edge1198Inv : Holds level0Subgroup PresentedGroup.of representative ⟨665, [(false, false)], 685⟩ :=
  holds_reverse edge1198

theorem edge1199 : Holds level0Subgroup PresentedGroup.of representative ⟨686, [(false, true)], 669⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨669, [(false, true)], 686⟩ :=
    edge685
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨669, [], 669⟩ :=
    (holds_refl 669)
  exact scanFacts hp hs (holds_relator 669 (level0Relator 0) (level0_relator 0))

theorem edge1199Inv : Holds level0Subgroup PresentedGroup.of representative ⟨669, [(false, false)], 686⟩ :=
  holds_reverse edge1199

theorem edge1200 : Holds level0Subgroup PresentedGroup.of representative ⟨687, [(false, true)], 670⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨670, [(false, true)], 687⟩ :=
    edge686
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨670, [], 670⟩ :=
    (holds_refl 670)
  exact scanFacts hp hs (holds_relator 670 (level0Relator 0) (level0_relator 0))

theorem edge1200Inv : Holds level0Subgroup PresentedGroup.of representative ⟨670, [(false, false)], 687⟩ :=
  holds_reverse edge1200

theorem edge1201 : Holds level0Subgroup PresentedGroup.of representative ⟨688, [(false, true)], 671⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨671, [(false, true)], 688⟩ :=
    edge687
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨671, [], 671⟩ :=
    (holds_refl 671)
  exact scanFacts hp hs (holds_relator 671 (level0Relator 0) (level0_relator 0))

theorem edge1201Inv : Holds level0Subgroup PresentedGroup.of representative ⟨671, [(false, false)], 688⟩ :=
  holds_reverse edge1201

theorem edge1202 : Holds level0Subgroup PresentedGroup.of representative ⟨689, [(false, true)], 680⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨680, [(false, true)], 689⟩ :=
    edge688
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨680, [], 680⟩ :=
    (holds_refl 680)
  exact scanFacts hp hs (holds_relator 680 (level0Relator 0) (level0_relator 0))

theorem edge1202Inv : Holds level0Subgroup PresentedGroup.of representative ⟨680, [(false, false)], 689⟩ :=
  holds_reverse edge1202

theorem edge1203 : Holds level0Subgroup PresentedGroup.of representative ⟨690, [(false, true)], 682⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨682, [(false, true)], 690⟩ :=
    edge689
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨682, [], 682⟩ :=
    (holds_refl 682)
  exact scanFacts hp hs (holds_relator 682 (level0Relator 0) (level0_relator 0))

theorem edge1203Inv : Holds level0Subgroup PresentedGroup.of representative ⟨682, [(false, false)], 690⟩ :=
  holds_reverse edge1203

theorem edge1204 : Holds level0Subgroup PresentedGroup.of representative ⟨691, [(false, true)], 683⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨683, [(false, true)], 691⟩ :=
    edge690
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨683, [], 683⟩ :=
    (holds_refl 683)
  exact scanFacts hp hs (holds_relator 683 (level0Relator 0) (level0_relator 0))

theorem edge1204Inv : Holds level0Subgroup PresentedGroup.of representative ⟨683, [(false, false)], 691⟩ :=
  holds_reverse edge1204

theorem edge1205 : Holds level0Subgroup PresentedGroup.of representative ⟨465, [(true, true)], 492⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨1, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)], 465⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge709 edge692) (appendFacts edge0 (appendFacts edge1 edge3))) (appendFacts (appendFacts edge6 (appendFacts edge10 edge15)) (appendFacts edge22 (appendFacts edge30 edge42)))) (appendFacts (appendFacts (appendFacts edge58 edge81) (appendFacts edge109 (appendFacts edge152 edge205))) (appendFacts (appendFacts edge286 (appendFacts edge708 edge961)) (appendFacts edge259Inv (appendFacts edge843 edge138Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge780 edge73Inv) (appendFacts edge747 (appendFacts edge38Inv edge729))) (appendFacts (appendFacts edge722 (appendFacts edge723 edge13Inv)) (appendFacts edge715 (appendFacts edge713 edge10)))) (appendFacts (appendFacts (appendFacts edge15 (appendFacts edge22 edge29)) (appendFacts edge41 (appendFacts edge55 edge78))) (appendFacts (appendFacts edge103 (appendFacts edge146 edge193)) (appendFacts edge274 (appendFacts edge356 edge464))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨492, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 1⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1067 edge393Inv) (appendFacts edge926 edge223Inv)) (appendFacts (appendFacts edge824 edge119Inv) (appendFacts edge771 (appendFacts edge754 edge695)))) (appendFacts (appendFacts (appendFacts edge64Inv edge742) (appendFacts edge33Inv edge727)) (appendFacts (appendFacts edge17Inv edge717) (appendFacts edge7Inv (appendFacts edge712 edge2Inv)))))
  exact scanFacts hp hs (holds_relator 1 (level0Relator 3) (level0_relator 3))

theorem edge1205Inv : Holds level0Subgroup PresentedGroup.of representative ⟨492, [(true, false)], 465⟩ :=
  holds_reverse edge1205

theorem edge1206 : Holds level0Subgroup PresentedGroup.of representative ⟨485, [(true, true)], 514⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨8, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)], 485⟩ :=
    (appendFacts (appendFacts (appendFacts edge11 (appendFacts edge18 edge25)) (appendFacts (appendFacts edge36 edge48) (appendFacts edge69 edge91))) (appendFacts (appendFacts (appendFacts edge129 edge171) (appendFacts edge241 edge913)) (appendFacts (appendFacts edge859 edge289) (appendFacts edge379 edge484))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨514, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 8⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1090 (appendFacts edge424Inv edge947)) (appendFacts (appendFacts edge245Inv edge836) (appendFacts edge131Inv edge777))) (appendFacts (appendFacts edge70Inv (appendFacts edge745 edge36Inv)) (appendFacts (appendFacts edge728 edge18Inv) (appendFacts edge717 edge7Inv)))) (appendFacts (appendFacts (appendFacts edge712 (appendFacts edge710Inv edge3)) (appendFacts (appendFacts edge6 edge10) (appendFacts edge15 edge22))) (appendFacts (appendFacts (appendFacts edge29 edge41) (appendFacts edge55 edge78)) (appendFacts (appendFacts edge103 edge146) (appendFacts edge193 edge274))))) (appendFacts (appendFacts (appendFacts (appendFacts edge356 (appendFacts edge464 edge1205)) (appendFacts (appendFacts edge1067 edge393Inv) (appendFacts edge926 edge866Inv))) (appendFacts (appendFacts edge925 (appendFacts edge220Inv edge823)) (appendFacts (appendFacts edge118Inv edge770) (appendFacts edge62Inv edge741)))) (appendFacts (appendFacts (appendFacts edge32Inv (appendFacts edge726 edge16Inv)) (appendFacts (appendFacts edge716 edge6Inv) (appendFacts edge711 edge710))) (appendFacts (appendFacts (appendFacts edge4 edge8) (appendFacts edge12 edge20)) (appendFacts (appendFacts edge723 edge719) (appendFacts edge21 edge27)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge39 (appendFacts edge51 edge75)) (appendFacts (appendFacts edge98 edge696) (appendFacts edge98Inv edge760))) (appendFacts (appendFacts edge51Inv (appendFacts edge736 edge27Inv)) (appendFacts (appendFacts edge724 edge14Inv) (appendFacts edge715 edge5Inv)))) (appendFacts (appendFacts (appendFacts edge711 (appendFacts edge1Inv edge709)) (appendFacts (appendFacts edge692Inv edge0) (appendFacts edge1 edge3))) (appendFacts (appendFacts (appendFacts edge6 edge10) (appendFacts edge16 edge23)) (appendFacts (appendFacts edge31 edge43) (appendFacts edge59 edge82))))) (appendFacts (appendFacts (appendFacts (appendFacts edge112 (appendFacts edge154 edge208)) (appendFacts (appendFacts edge699 edge241Inv) (appendFacts edge834 edge129Inv))) (appendFacts (appendFacts edge776 (appendFacts edge69Inv edge745)) (appendFacts (appendFacts edge36Inv edge728) (appendFacts edge18Inv edge717)))) (appendFacts (appendFacts (appendFacts edge7Inv (appendFacts edge712 edge2Inv)) (appendFacts (appendFacts edge709 edge692) (appendFacts edge0 edge1))) (appendFacts (appendFacts (appendFacts edge3 edge5) (appendFacts edge9 edge13)) (appendFacts (appendFacts edge693 edge20Inv) (appendFacts edge718 edge714Inv)))))))
  exact scanFacts hp hs (holds_relator 8 (level0Relator 12) (level0_relator 12))

theorem edge1206Inv : Holds level0Subgroup PresentedGroup.of representative ⟨514, [(true, false)], 485⟩ :=
  holds_reverse edge1206

theorem edge1207 : Holds level0Subgroup PresentedGroup.of representative ⟨471, [(true, true)], 507⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨9, [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)], 471⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge12 (appendFacts edge19 edge26)) (appendFacts edge38 (appendFacts edge50 edge73))) (appendFacts (appendFacts edge95 (appendFacts edge138 edge180)) (appendFacts edge259 (appendFacts edge333 edge708Inv)))) (appendFacts (appendFacts (appendFacts edge910 (appendFacts edge205Inv edge815)) (appendFacts edge788 (appendFacts edge697 edge110Inv))) (appendFacts (appendFacts edge766 (appendFacts edge58Inv edge739)) (appendFacts (appendFacts edge30Inv edge725) (appendFacts edge15Inv edge716))))) (appendFacts (appendFacts (appendFacts (appendFacts edge6Inv (appendFacts edge711 edge710)) (appendFacts edge4 (appendFacts edge8 edge12))) (appendFacts (appendFacts edge20 (appendFacts edge723 edge719)) (appendFacts edge21 (appendFacts edge27 edge39)))) (appendFacts (appendFacts (appendFacts edge51 (appendFacts edge75 edge98)) (appendFacts edge696 (appendFacts edge98Inv edge760))) (appendFacts (appendFacts edge51Inv (appendFacts edge736 edge27Inv)) (appendFacts (appendFacts edge724 edge719Inv) (appendFacts edge693 edge20Inv)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge718 (appendFacts edge8Inv edge712)) (appendFacts edge2Inv (appendFacts edge709 edge692Inv))) (appendFacts (appendFacts edge0 (appendFacts edge1 edge3)) (appendFacts edge6 (appendFacts edge10 edge15)))) (appendFacts (appendFacts (appendFacts edge22 (appendFacts edge30 edge42)) (appendFacts edge58 (appendFacts edge81 edge110))) (appendFacts (appendFacts edge697 (appendFacts edge110Inv edge766)) (appendFacts (appendFacts edge58Inv edge739) (appendFacts edge30Inv edge725))))) (appendFacts (appendFacts (appendFacts (appendFacts edge15Inv (appendFacts edge716 edge6Inv)) (appendFacts edge711 (appendFacts edge710 edge4))) (appendFacts (appendFacts edge8 (appendFacts edge12 edge20)) (appendFacts (appendFacts edge723 edge13Inv) (appendFacts edge715 edge713)))) (appendFacts (appendFacts (appendFacts edge10 (appendFacts edge15 edge22)) (appendFacts edge29 (appendFacts edge41 edge56))) (appendFacts (appendFacts edge79 (appendFacts edge105 edge148)) (appendFacts (appendFacts edge197 edge278) (appendFacts edge362 edge470)))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨507, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)], 9⟩ :=
    (appendFacts (appendFacts (appendFacts edge1083 (appendFacts edge413Inv edge940)) (appendFacts (appendFacts edge237Inv edge832) (appendFacts edge127Inv edge775))) (appendFacts (appendFacts edge68Inv (appendFacts edge744 edge35Inv)) (appendFacts (appendFacts edge728 edge18Inv) (appendFacts edge717 edge714))))
  exact scanFacts hp hs (holds_relator 9 (level0Relator 6) (level0_relator 6))

theorem edge1207Inv : Holds level0Subgroup PresentedGroup.of representative ⟨507, [(true, false)], 471⟩ :=
  holds_reverse edge1207

theorem edge1208 : Holds level0Subgroup PresentedGroup.of representative ⟨468, [(true, true)], 462⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨15, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)], 468⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge21 (appendFacts edge27 edge39)) (appendFacts (appendFacts edge51 edge75) (appendFacts edge98 edge696))) (appendFacts (appendFacts (appendFacts edge98Inv edge760) (appendFacts edge51Inv edge736)) (appendFacts (appendFacts edge27Inv edge724) (appendFacts edge719Inv edge693)))) (appendFacts (appendFacts (appendFacts edge20Inv (appendFacts edge718 edge8Inv)) (appendFacts (appendFacts edge712 edge710Inv) (appendFacts edge3 edge6))) (appendFacts (appendFacts (appendFacts edge10 edge15) (appendFacts edge22 edge30)) (appendFacts (appendFacts edge42 edge58) (appendFacts edge81 edge110))))) (appendFacts (appendFacts (appendFacts (appendFacts edge697 (appendFacts edge110Inv edge766)) (appendFacts (appendFacts edge58Inv edge739) (appendFacts edge30Inv edge725))) (appendFacts (appendFacts (appendFacts edge15Inv edge716) (appendFacts edge6Inv edge711)) (appendFacts (appendFacts edge1Inv edge709) (appendFacts edge692 edge0)))) (appendFacts (appendFacts (appendFacts (appendFacts edge1 edge3) (appendFacts edge6 edge10)) (appendFacts (appendFacts edge15 edge22) (appendFacts edge29 edge41))) (appendFacts (appendFacts (appendFacts edge55 edge78) (appendFacts edge104 edge147)) (appendFacts (appendFacts edge195 edge276) (appendFacts edge359 edge467))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨462, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 15⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1035 edge351Inv) (appendFacts edge896 (appendFacts edge191Inv edge808))) (appendFacts (appendFacts edge102Inv (appendFacts edge762 edge54Inv)) (appendFacts edge737 (appendFacts edge28Inv edge724)))) (appendFacts (appendFacts (appendFacts edge14Inv edge715) (appendFacts edge5Inv (appendFacts edge711 edge1Inv))) (appendFacts (appendFacts edge709 (appendFacts edge692 edge0)) (appendFacts edge2 (appendFacts edge4 edge7))))) (appendFacts (appendFacts (appendFacts (appendFacts edge11 edge17) (appendFacts edge24 (appendFacts edge34 edge46))) (appendFacts (appendFacts edge66 (appendFacts edge88 edge124)) (appendFacts edge166 (appendFacts edge233 edge701)))) (appendFacts (appendFacts (appendFacts edge246Inv (appendFacts edge837 edge132Inv)) (appendFacts edge777 (appendFacts edge70Inv edge745))) (appendFacts (appendFacts edge36Inv (appendFacts edge728 edge18Inv)) (appendFacts edge717 (appendFacts edge7Inv edge712)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge710Inv edge3) (appendFacts edge6 (appendFacts edge10 edge15))) (appendFacts (appendFacts edge22 (appendFacts edge29 edge41)) (appendFacts edge55 (appendFacts edge78 edge103)))) (appendFacts (appendFacts (appendFacts edge146 edge193) (appendFacts edge274 (appendFacts edge356 edge464))) (appendFacts (appendFacts edge1205 (appendFacts edge1067 edge393Inv)) (appendFacts edge926 (appendFacts edge866Inv edge925))))) (appendFacts (appendFacts (appendFacts (appendFacts edge220Inv edge823) (appendFacts edge118Inv (appendFacts edge770 edge62Inv))) (appendFacts (appendFacts edge741 (appendFacts edge32Inv edge726)) (appendFacts edge16Inv (appendFacts edge716 edge6Inv)))) (appendFacts (appendFacts (appendFacts edge711 (appendFacts edge1Inv edge709)) (appendFacts edge692Inv (appendFacts edge0 edge2))) (appendFacts (appendFacts edge4 (appendFacts edge8 edge12)) (appendFacts edge20 (appendFacts edge723 edge719)))))))
  exact scanFacts hp hs (holds_relator 15 (level0Relator 17) (level0_relator 17))

theorem edge1208Inv : Holds level0Subgroup PresentedGroup.of representative ⟨462, [(true, false)], 468⟩ :=
  holds_reverse edge1208

theorem edge1209 : Holds level0Subgroup PresentedGroup.of representative ⟨580, [(false, true)], 537⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨21, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)], 580⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge723 (appendFacts edge719 edge21)) (appendFacts edge27 (appendFacts edge39 edge52))) (appendFacts (appendFacts edge76 (appendFacts edge99 edge142)) (appendFacts edge186 (appendFacts edge267 edge704)))) (appendFacts (appendFacts (appendFacts edge920 (appendFacts edge215Inv edge820)) (appendFacts edge115Inv (appendFacts edge769 edge61Inv))) (appendFacts (appendFacts edge741 (appendFacts edge32Inv edge726)) (appendFacts (appendFacts edge16Inv edge716) (appendFacts edge713Inv edge9))))) (appendFacts (appendFacts (appendFacts (appendFacts edge13 (appendFacts edge693 edge20Inv)) (appendFacts edge718 (appendFacts edge714Inv edge11))) (appendFacts (appendFacts edge17 (appendFacts edge24 edge33)) (appendFacts edge45 (appendFacts edge63 edge86)))) (appendFacts (appendFacts (appendFacts edge119 (appendFacts edge161 edge222)) (appendFacts edge925 (appendFacts edge865 edge867))) (appendFacts (appendFacts edge865Inv (appendFacts edge700 edge866)) (appendFacts (appendFacts edge300 edge394) (appendFacts edge492 edge579))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨537, [(true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 21⟩ :=
    (appendFacts (appendFacts (appendFacts edge536Inv (appendFacts edge1028 edge968)) (appendFacts edge951 (appendFacts edge249Inv edge838))) (appendFacts (appendFacts edge133Inv (appendFacts edge778 edge71Inv)) (appendFacts (appendFacts edge746 edge37Inv) (appendFacts edge729 edge722))))
  exact scanFacts hp hs (holds_relator 21 (level0Relator 3) (level0_relator 3))

theorem edge1209Inv : Holds level0Subgroup PresentedGroup.of representative ⟨537, [(false, false)], 580⟩ :=
  holds_reverse edge1209

theorem edge1210 : Holds level0Subgroup PresentedGroup.of representative ⟨354, [(false, true)], 388⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨34, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)], 354⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge45 edge63) (appendFacts edge86 edge119)) (appendFacts (appendFacts edge161 edge223) (appendFacts edge300 edge393))) (appendFacts (appendFacts (appendFacts edge491 edge1205Inv) (appendFacts edge1038 edge976Inv)) (appendFacts (appendFacts edge463 edge1112Inv) (appendFacts edge1036 edge975Inv))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨388, [(true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 34⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge387Inv edge922) (appendFacts edge217Inv (appendFacts edge821 edge116Inv))) (appendFacts (appendFacts edge769 (appendFacts edge61Inv edge741)) (appendFacts edge32Inv (appendFacts edge726 edge16Inv)))) (appendFacts (appendFacts (appendFacts edge716 (appendFacts edge713Inv edge9)) (appendFacts edge13 (appendFacts edge693 edge20Inv))) (appendFacts (appendFacts edge718 (appendFacts edge8Inv edge712)) (appendFacts edge2Inv (appendFacts edge709 edge692))))) (appendFacts (appendFacts (appendFacts (appendFacts edge0 (appendFacts edge1 edge3)) (appendFacts edge6 (appendFacts edge10 edge15))) (appendFacts (appendFacts edge22 (appendFacts edge30 edge42)) (appendFacts edge57 (appendFacts edge80 edge108)))) (appendFacts (appendFacts (appendFacts edge151 (appendFacts edge698 edge831)) (appendFacts edge126Inv (appendFacts edge774 edge67Inv))) (appendFacts (appendFacts edge744 (appendFacts edge35Inv edge728)) (appendFacts edge721Inv (appendFacts edge24 edge33))))))
  exact scanFacts hp hs (holds_relator 34 (level0Relator 3) (level0_relator 3))

theorem edge1210Inv : Holds level0Subgroup PresentedGroup.of representative ⟨388, [(false, false)], 354⟩ :=
  holds_reverse edge1210

theorem edge1211 : Holds level0Subgroup PresentedGroup.of representative ⟨470, [(true, false)], 508⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨56, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)], 470⟩ :=
    (appendFacts (appendFacts edge78 (appendFacts edge104 edge147)) (appendFacts (appendFacts edge196 edge277) (appendFacts edge361 edge469)))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨508, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 56⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1084 edge414Inv) (appendFacts edge941 (appendFacts edge238Inv edge833))) (appendFacts (appendFacts edge797Inv edge169) (appendFacts edge237 (appendFacts edge313 edge413)))) (appendFacts (appendFacts (appendFacts edge506 edge1207Inv) (appendFacts edge1044 (appendFacts edge362Inv edge902))) (appendFacts (appendFacts edge197Inv edge811) (appendFacts edge105Inv (appendFacts edge764 edge750Inv)))))
  exact scanFacts hp hs (holds_relator 56 (level0Relator 2) (level0_relator 2))

theorem edge1211Inv : Holds level0Subgroup PresentedGroup.of representative ⟨508, [(true, true)], 470⟩ :=
  holds_reverse edge1211

theorem edge1212 : Holds level0Subgroup PresentedGroup.of representative ⟨343, [(false, true)], 379⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨76, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)], 343⟩ :=
    (appendFacts (appendFacts (appendFacts edge760 edge748) (appendFacts edge76 edge99)) (appendFacts (appendFacts edge142 edge186) (appendFacts edge267 edge342)))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨379, [(true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 76⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge378Inv (appendFacts edge914 edge859Inv)) (appendFacts edge699 (appendFacts edge241Inv edge834))) (appendFacts (appendFacts edge129Inv (appendFacts edge776 edge69Inv)) (appendFacts (appendFacts edge745 edge36Inv) (appendFacts edge728 edge18Inv)))) (appendFacts (appendFacts (appendFacts edge717 (appendFacts edge7Inv edge712)) (appendFacts (appendFacts edge2Inv edge709) (appendFacts edge692 edge0))) (appendFacts (appendFacts edge2 (appendFacts edge4 edge7)) (appendFacts (appendFacts edge11 edge17) (appendFacts edge24 edge33))))) (appendFacts (appendFacts (appendFacts (appendFacts edge45 (appendFacts edge63 edge86)) (appendFacts (appendFacts edge119 edge161) (appendFacts edge222 edge925))) (appendFacts (appendFacts edge220Inv (appendFacts edge823 edge118Inv)) (appendFacts (appendFacts edge770 edge753Inv) (appendFacts edge84 edge115)))) (appendFacts (appendFacts (appendFacts edge157 (appendFacts edge215 edge295)) (appendFacts (appendFacts edge704Inv edge891) (appendFacts edge186Inv edge805))) (appendFacts (appendFacts edge99Inv (appendFacts edge761 edge748Inv)) (appendFacts (appendFacts edge75 edge98) (appendFacts edge696 edge98Inv))))))
  exact scanFacts hp hs (holds_relator 76 (level0Relator 3) (level0_relator 3))

theorem edge1212Inv : Holds level0Subgroup PresentedGroup.of representative ⟨379, [(false, false)], 343⟩ :=
  holds_reverse edge1212

theorem edge1213 : Holds level0Subgroup PresentedGroup.of representative ⟨423, [(false, true)], 437⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨82, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)], 423⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge766 edge58Inv) (appendFacts edge739 edge30Inv)) (appendFacts (appendFacts edge725 edge15Inv) (appendFacts edge716 (appendFacts edge6Inv edge711)))) (appendFacts (appendFacts (appendFacts edge1Inv edge709) (appendFacts edge692Inv (appendFacts edge0 edge1))) (appendFacts (appendFacts edge3 edge6) (appendFacts edge10 (appendFacts edge16 edge23))))) (appendFacts (appendFacts (appendFacts (appendFacts edge31 edge43) (appendFacts edge59 edge82)) (appendFacts (appendFacts edge112 edge154) (appendFacts edge208 (appendFacts edge699 edge241Inv)))) (appendFacts (appendFacts (appendFacts edge834 edge129Inv) (appendFacts edge776 (appendFacts edge757 edge92))) (appendFacts (appendFacts edge131 edge173) (appendFacts edge244 (appendFacts edge319 edge422))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨437, [(true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 82⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge436Inv (appendFacts edge955 edge253Inv)) (appendFacts edge840 (appendFacts edge135Inv edge779))) (appendFacts (appendFacts edge72Inv (appendFacts edge746 edge37Inv)) (appendFacts edge729 (appendFacts edge722 edge723)))) (appendFacts (appendFacts (appendFacts edge13Inv (appendFacts edge715 edge713)) (appendFacts edge10 (appendFacts edge15 edge22))) (appendFacts (appendFacts edge30 (appendFacts edge42 edge58)) (appendFacts (appendFacts edge81 edge110) (appendFacts edge697 edge110Inv)))))
  exact scanFacts hp hs (holds_relator 82 (level0Relator 3) (level0_relator 3))

theorem edge1213Inv : Holds level0Subgroup PresentedGroup.of representative ⟨437, [(false, false)], 423⟩ :=
  holds_reverse edge1213

theorem edge1214 : Holds level0Subgroup PresentedGroup.of representative ⟨468, [(true, false)], 482⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨153, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)], 468⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge815 (appendFacts edge788 edge697)) (appendFacts (appendFacts edge110Inv edge766) (appendFacts edge751Inv edge80))) (appendFacts (appendFacts edge107 (appendFacts edge150 edge202)) (appendFacts (appendFacts edge283 edge702Inv) (appendFacts edge889 edge184Inv)))) (appendFacts (appendFacts (appendFacts edge804 (appendFacts edge97Inv edge760)) (appendFacts (appendFacts edge51Inv edge736) (appendFacts edge730 edge40))) (appendFacts (appendFacts (appendFacts edge53 edge694) (appendFacts edge53Inv edge737)) (appendFacts (appendFacts edge28Inv edge724) (appendFacts edge14Inv edge715))))) (appendFacts (appendFacts (appendFacts (appendFacts edge5Inv (appendFacts edge711 edge710)) (appendFacts (appendFacts edge4 edge7) (appendFacts edge11 edge17))) (appendFacts (appendFacts (appendFacts edge24 edge33) (appendFacts edge45 edge63)) (appendFacts (appendFacts edge86 edge119) (appendFacts edge161 edge223)))) (appendFacts (appendFacts (appendFacts edge300 (appendFacts edge393 edge491)) (appendFacts (appendFacts edge1205Inv edge1038) (appendFacts edge356Inv edge898))) (appendFacts (appendFacts (appendFacts edge193Inv edge809) (appendFacts edge785 edge147)) (appendFacts (appendFacts edge195 edge276) (appendFacts edge359 edge467))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨482, [(false, true), (true, false), (false, true), (true, true)], 153⟩ :=
    (appendFacts (appendFacts edge1056 edge374Inv) (appendFacts edge910 edge205Inv))
  exact scanFacts hp hs (holds_relator 153 (level0Relator 3) (level0_relator 3))

theorem edge1214Inv : Holds level0Subgroup PresentedGroup.of representative ⟨482, [(true, true)], 468⟩ :=
  holds_reverse edge1214

theorem edge1215 : Holds level0Subgroup PresentedGroup.of representative ⟨483, [(true, true)], 483⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨187, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)], 483⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge267 edge704) (appendFacts edge920 edge215Inv)) (appendFacts (appendFacts edge820 edge115Inv) (appendFacts edge769 (appendFacts edge61Inv edge741)))) (appendFacts (appendFacts (appendFacts edge732Inv edge43) (appendFacts edge59 (appendFacts edge82 edge111))) (appendFacts (appendFacts edge153 edge206) (appendFacts edge287 (appendFacts edge376 edge482)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨483, [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 187⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1058 (appendFacts edge376Inv edge911)) (appendFacts edge206Inv (appendFacts edge816 edge111Inv))) (appendFacts (appendFacts edge767 (appendFacts edge59Inv edge740)) (appendFacts (appendFacts edge31Inv edge726) (appendFacts edge720Inv edge22)))) (appendFacts (appendFacts (appendFacts edge29 (appendFacts edge41 edge55)) (appendFacts edge78 (appendFacts edge104 edge147))) (appendFacts (appendFacts edge195 (appendFacts edge276 edge359)) (appendFacts (appendFacts edge467 edge1214) (appendFacts edge1056 edge374Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge910 (appendFacts edge205Inv edge815)) (appendFacts edge788 (appendFacts edge697 edge110Inv))) (appendFacts (appendFacts edge766 (appendFacts edge751Inv edge80)) (appendFacts (appendFacts edge107 edge150) (appendFacts edge202 edge283)))) (appendFacts (appendFacts (appendFacts edge702Inv (appendFacts edge889 edge184Inv)) (appendFacts edge804 (appendFacts edge782 edge696))) (appendFacts (appendFacts edge98Inv (appendFacts edge760 edge748)) (appendFacts (appendFacts edge76 edge99) (appendFacts edge142 edge186))))))
  exact scanFacts hp hs (holds_relator 187 (level0Relator 4) (level0_relator 4))

theorem edge1215Inv : Holds level0Subgroup PresentedGroup.of representative ⟨483, [(true, false)], 483⟩ :=
  holds_reverse edge1215


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
