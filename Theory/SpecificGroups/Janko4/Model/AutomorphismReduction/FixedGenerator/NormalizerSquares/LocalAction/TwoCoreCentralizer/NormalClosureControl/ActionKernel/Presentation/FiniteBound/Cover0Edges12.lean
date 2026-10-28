module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges11

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

theorem edge768 : Holds level0Subgroup PresentedGroup.of representative ⟨84, [(false, true)], 61⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨61, [(false, true)], 84⟩ :=
    edge83
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨61, [], 61⟩ :=
    (holds_refl 61)
  exact scanFacts hp hs (holds_relator 61 (level0Relator 0) (level0_relator 0))

theorem edge768Inv : Holds level0Subgroup PresentedGroup.of representative ⟨61, [(false, false)], 84⟩ :=
  holds_reverse edge768

theorem edge769 : Holds level0Subgroup PresentedGroup.of representative ⟨85, [(false, true)], 62⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨62, [(false, true)], 85⟩ :=
    edge84
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨62, [], 62⟩ :=
    (holds_refl 62)
  exact scanFacts hp hs (holds_relator 62 (level0Relator 0) (level0_relator 0))

theorem edge769Inv : Holds level0Subgroup PresentedGroup.of representative ⟨62, [(false, false)], 85⟩ :=
  holds_reverse edge769

theorem edge770 : Holds level0Subgroup PresentedGroup.of representative ⟨86, [(false, true)], 63⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨63, [(false, true)], 86⟩ :=
    edge85
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨63, [], 63⟩ :=
    (holds_refl 63)
  exact scanFacts hp hs (holds_relator 63 (level0Relator 0) (level0_relator 0))

theorem edge770Inv : Holds level0Subgroup PresentedGroup.of representative ⟨63, [(false, false)], 86⟩ :=
  holds_reverse edge770

theorem edge771 : Holds level0Subgroup PresentedGroup.of representative ⟨87, [(false, true)], 64⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨64, [(false, true)], 87⟩ :=
    edge86
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨64, [], 64⟩ :=
    (holds_refl 64)
  exact scanFacts hp hs (holds_relator 64 (level0Relator 0) (level0_relator 0))

theorem edge771Inv : Holds level0Subgroup PresentedGroup.of representative ⟨64, [(false, false)], 87⟩ :=
  holds_reverse edge771

theorem edge772 : Holds level0Subgroup PresentedGroup.of representative ⟨88, [(false, true)], 66⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨66, [(false, true)], 88⟩ :=
    edge87
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨66, [], 66⟩ :=
    (holds_refl 66)
  exact scanFacts hp hs (holds_relator 66 (level0Relator 0) (level0_relator 0))

theorem edge772Inv : Holds level0Subgroup PresentedGroup.of representative ⟨66, [(false, false)], 88⟩ :=
  holds_reverse edge772

theorem edge773 : Holds level0Subgroup PresentedGroup.of representative ⟨89, [(false, true)], 67⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨67, [(false, true)], 89⟩ :=
    edge88
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨67, [], 67⟩ :=
    (holds_refl 67)
  exact scanFacts hp hs (holds_relator 67 (level0Relator 0) (level0_relator 0))

theorem edge773Inv : Holds level0Subgroup PresentedGroup.of representative ⟨67, [(false, false)], 89⟩ :=
  holds_reverse edge773

theorem edge774 : Holds level0Subgroup PresentedGroup.of representative ⟨90, [(false, true)], 68⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨68, [(false, true)], 90⟩ :=
    edge89
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨68, [], 68⟩ :=
    (holds_refl 68)
  exact scanFacts hp hs (holds_relator 68 (level0Relator 0) (level0_relator 0))

theorem edge774Inv : Holds level0Subgroup PresentedGroup.of representative ⟨68, [(false, false)], 90⟩ :=
  holds_reverse edge774

theorem edge775 : Holds level0Subgroup PresentedGroup.of representative ⟨91, [(false, true)], 69⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨69, [(false, true)], 91⟩ :=
    edge90
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨69, [], 69⟩ :=
    (holds_refl 69)
  exact scanFacts hp hs (holds_relator 69 (level0Relator 0) (level0_relator 0))

theorem edge775Inv : Holds level0Subgroup PresentedGroup.of representative ⟨69, [(false, false)], 91⟩ :=
  holds_reverse edge775

theorem edge776 : Holds level0Subgroup PresentedGroup.of representative ⟨92, [(false, true)], 70⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨70, [(false, true)], 92⟩ :=
    edge91
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨70, [], 70⟩ :=
    (holds_refl 70)
  exact scanFacts hp hs (holds_relator 70 (level0Relator 0) (level0_relator 0))

theorem edge776Inv : Holds level0Subgroup PresentedGroup.of representative ⟨70, [(false, false)], 92⟩ :=
  holds_reverse edge776

theorem edge777 : Holds level0Subgroup PresentedGroup.of representative ⟨93, [(false, true)], 71⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨71, [(false, true)], 93⟩ :=
    edge92
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨71, [], 71⟩ :=
    (holds_refl 71)
  exact scanFacts hp hs (holds_relator 71 (level0Relator 0) (level0_relator 0))

theorem edge777Inv : Holds level0Subgroup PresentedGroup.of representative ⟨71, [(false, false)], 93⟩ :=
  holds_reverse edge777

theorem edge778 : Holds level0Subgroup PresentedGroup.of representative ⟨94, [(false, true)], 72⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨72, [(false, true)], 94⟩ :=
    edge93
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨72, [], 72⟩ :=
    (holds_refl 72)
  exact scanFacts hp hs (holds_relator 72 (level0Relator 0) (level0_relator 0))

theorem edge778Inv : Holds level0Subgroup PresentedGroup.of representative ⟨72, [(false, false)], 94⟩ :=
  holds_reverse edge778

theorem edge779 : Holds level0Subgroup PresentedGroup.of representative ⟨95, [(false, true)], 73⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨73, [(false, true)], 95⟩ :=
    edge94
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨73, [], 73⟩ :=
    (holds_refl 73)
  exact scanFacts hp hs (holds_relator 73 (level0Relator 0) (level0_relator 0))

theorem edge779Inv : Holds level0Subgroup PresentedGroup.of representative ⟨73, [(false, false)], 95⟩ :=
  holds_reverse edge779

theorem edge780 : Holds level0Subgroup PresentedGroup.of representative ⟨96, [(false, true)], 74⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨74, [(false, true)], 96⟩ :=
    edge95
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨74, [], 74⟩ :=
    (holds_refl 74)
  exact scanFacts hp hs (holds_relator 74 (level0Relator 0) (level0_relator 0))

theorem edge780Inv : Holds level0Subgroup PresentedGroup.of representative ⟨74, [(false, false)], 96⟩ :=
  holds_reverse edge780

theorem edge781 : Holds level0Subgroup PresentedGroup.of representative ⟨97, [(false, true)], 75⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨75, [(false, true)], 97⟩ :=
    edge96
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨75, [], 75⟩ :=
    (holds_refl 75)
  exact scanFacts hp hs (holds_relator 75 (level0Relator 0) (level0_relator 0))

theorem edge781Inv : Holds level0Subgroup PresentedGroup.of representative ⟨75, [(false, false)], 97⟩ :=
  holds_reverse edge781

theorem edge782 : Holds level0Subgroup PresentedGroup.of representative ⟨98, [(true, true)], 99⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨76, [(true, true)], 98⟩ :=
    edge97
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨99, [(true, true)], 76⟩ :=
    edge98Inv
  exact scanFacts hp hs (holds_relator 76 (level0Relator 1) (level0_relator 1))

theorem edge782Inv : Holds level0Subgroup PresentedGroup.of representative ⟨99, [(true, false)], 98⟩ :=
  holds_reverse edge782

theorem edge783 : Holds level0Subgroup PresentedGroup.of representative ⟨100, [(true, true)], 101⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨77, [(true, true)], 100⟩ :=
    edge99
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨101, [(true, true)], 77⟩ :=
    edge100Inv
  exact scanFacts hp hs (holds_relator 77 (level0Relator 1) (level0_relator 1))

theorem edge783Inv : Holds level0Subgroup PresentedGroup.of representative ⟨101, [(true, false)], 100⟩ :=
  holds_reverse edge783

theorem edge784 : Holds level0Subgroup PresentedGroup.of representative ⟨102, [(true, true)], 103⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨78, [(true, true)], 102⟩ :=
    edge101
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨103, [(true, true)], 78⟩ :=
    edge102Inv
  exact scanFacts hp hs (holds_relator 78 (level0Relator 1) (level0_relator 1))

theorem edge784Inv : Holds level0Subgroup PresentedGroup.of representative ⟨103, [(true, false)], 102⟩ :=
  holds_reverse edge784

theorem edge785 : Holds level0Subgroup PresentedGroup.of representative ⟨104, [(true, true)], 105⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨79, [(true, true)], 104⟩ :=
    edge103
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨105, [(true, true)], 79⟩ :=
    edge104Inv
  exact scanFacts hp hs (holds_relator 79 (level0Relator 1) (level0_relator 1))

theorem edge785Inv : Holds level0Subgroup PresentedGroup.of representative ⟨105, [(true, false)], 104⟩ :=
  holds_reverse edge785

theorem edge786 : Holds level0Subgroup PresentedGroup.of representative ⟨106, [(true, true)], 107⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨80, [(true, true)], 106⟩ :=
    edge105
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨107, [(true, true)], 80⟩ :=
    edge106Inv
  exact scanFacts hp hs (holds_relator 80 (level0Relator 1) (level0_relator 1))

theorem edge786Inv : Holds level0Subgroup PresentedGroup.of representative ⟨107, [(true, false)], 106⟩ :=
  holds_reverse edge786

theorem edge787 : Holds level0Subgroup PresentedGroup.of representative ⟨108, [(true, true)], 109⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨81, [(true, true)], 108⟩ :=
    edge107
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨109, [(true, true)], 81⟩ :=
    edge108Inv
  exact scanFacts hp hs (holds_relator 81 (level0Relator 1) (level0_relator 1))

theorem edge787Inv : Holds level0Subgroup PresentedGroup.of representative ⟨109, [(true, false)], 108⟩ :=
  holds_reverse edge787

theorem edge788 : Holds level0Subgroup PresentedGroup.of representative ⟨110, [(true, true)], 111⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨82, [(true, true)], 110⟩ :=
    edge109
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨111, [(true, true)], 82⟩ :=
    edge110Inv
  exact scanFacts hp hs (holds_relator 82 (level0Relator 1) (level0_relator 1))

theorem edge788Inv : Holds level0Subgroup PresentedGroup.of representative ⟨111, [(true, false)], 110⟩ :=
  holds_reverse edge788

theorem edge789 : Holds level0Subgroup PresentedGroup.of representative ⟨112, [(true, true)], 113⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨83, [(true, true)], 112⟩ :=
    edge111
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨113, [(true, true)], 83⟩ :=
    edge112Inv
  exact scanFacts hp hs (holds_relator 83 (level0Relator 1) (level0_relator 1))

theorem edge789Inv : Holds level0Subgroup PresentedGroup.of representative ⟨113, [(true, false)], 112⟩ :=
  holds_reverse edge789

theorem edge790 : Holds level0Subgroup PresentedGroup.of representative ⟨114, [(true, true)], 115⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨84, [(true, true)], 114⟩ :=
    edge113
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨115, [(true, true)], 84⟩ :=
    edge114Inv
  exact scanFacts hp hs (holds_relator 84 (level0Relator 1) (level0_relator 1))

theorem edge790Inv : Holds level0Subgroup PresentedGroup.of representative ⟨115, [(true, false)], 114⟩ :=
  holds_reverse edge790

theorem edge791 : Holds level0Subgroup PresentedGroup.of representative ⟨116, [(true, true)], 117⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨85, [(true, true)], 116⟩ :=
    edge115
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨117, [(true, true)], 85⟩ :=
    edge116Inv
  exact scanFacts hp hs (holds_relator 85 (level0Relator 1) (level0_relator 1))

theorem edge791Inv : Holds level0Subgroup PresentedGroup.of representative ⟨117, [(true, false)], 116⟩ :=
  holds_reverse edge791

theorem edge792 : Holds level0Subgroup PresentedGroup.of representative ⟨118, [(true, true)], 119⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨86, [(true, true)], 118⟩ :=
    edge117
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨119, [(true, true)], 86⟩ :=
    edge118Inv
  exact scanFacts hp hs (holds_relator 86 (level0Relator 1) (level0_relator 1))

theorem edge792Inv : Holds level0Subgroup PresentedGroup.of representative ⟨119, [(true, false)], 118⟩ :=
  holds_reverse edge792

theorem edge793 : Holds level0Subgroup PresentedGroup.of representative ⟨120, [(true, true)], 121⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨87, [(true, true)], 120⟩ :=
    edge119
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨121, [(true, true)], 87⟩ :=
    edge120Inv
  exact scanFacts hp hs (holds_relator 87 (level0Relator 1) (level0_relator 1))

theorem edge793Inv : Holds level0Subgroup PresentedGroup.of representative ⟨121, [(true, false)], 120⟩ :=
  holds_reverse edge793

theorem edge794 : Holds level0Subgroup PresentedGroup.of representative ⟨122, [(true, true)], 123⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨88, [(true, true)], 122⟩ :=
    edge121
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨123, [(true, true)], 88⟩ :=
    edge122Inv
  exact scanFacts hp hs (holds_relator 88 (level0Relator 1) (level0_relator 1))

theorem edge794Inv : Holds level0Subgroup PresentedGroup.of representative ⟨123, [(true, false)], 122⟩ :=
  holds_reverse edge794

theorem edge795 : Holds level0Subgroup PresentedGroup.of representative ⟨124, [(true, true)], 125⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨89, [(true, true)], 124⟩ :=
    edge123
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨125, [(true, true)], 89⟩ :=
    edge124Inv
  exact scanFacts hp hs (holds_relator 89 (level0Relator 1) (level0_relator 1))

theorem edge795Inv : Holds level0Subgroup PresentedGroup.of representative ⟨125, [(true, false)], 124⟩ :=
  holds_reverse edge795

theorem edge796 : Holds level0Subgroup PresentedGroup.of representative ⟨126, [(true, true)], 127⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨90, [(true, true)], 126⟩ :=
    edge125
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨127, [(true, true)], 90⟩ :=
    edge126Inv
  exact scanFacts hp hs (holds_relator 90 (level0Relator 1) (level0_relator 1))

theorem edge796Inv : Holds level0Subgroup PresentedGroup.of representative ⟨127, [(true, false)], 126⟩ :=
  holds_reverse edge796

theorem edge797 : Holds level0Subgroup PresentedGroup.of representative ⟨128, [(true, true)], 129⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨91, [(true, true)], 128⟩ :=
    edge127
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨129, [(true, true)], 91⟩ :=
    edge128Inv
  exact scanFacts hp hs (holds_relator 91 (level0Relator 1) (level0_relator 1))

theorem edge797Inv : Holds level0Subgroup PresentedGroup.of representative ⟨129, [(true, false)], 128⟩ :=
  holds_reverse edge797

theorem edge798 : Holds level0Subgroup PresentedGroup.of representative ⟨130, [(true, true)], 131⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨92, [(true, true)], 130⟩ :=
    edge129
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨131, [(true, true)], 92⟩ :=
    edge130Inv
  exact scanFacts hp hs (holds_relator 92 (level0Relator 1) (level0_relator 1))

theorem edge798Inv : Holds level0Subgroup PresentedGroup.of representative ⟨131, [(true, false)], 130⟩ :=
  holds_reverse edge798

theorem edge799 : Holds level0Subgroup PresentedGroup.of representative ⟨132, [(true, true)], 133⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨93, [(true, true)], 132⟩ :=
    edge131
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨133, [(true, true)], 93⟩ :=
    edge132Inv
  exact scanFacts hp hs (holds_relator 93 (level0Relator 1) (level0_relator 1))

theorem edge799Inv : Holds level0Subgroup PresentedGroup.of representative ⟨133, [(true, false)], 132⟩ :=
  holds_reverse edge799

theorem edge800 : Holds level0Subgroup PresentedGroup.of representative ⟨134, [(true, true)], 135⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨94, [(true, true)], 134⟩ :=
    edge133
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨135, [(true, true)], 94⟩ :=
    edge134Inv
  exact scanFacts hp hs (holds_relator 94 (level0Relator 1) (level0_relator 1))

theorem edge800Inv : Holds level0Subgroup PresentedGroup.of representative ⟨135, [(true, false)], 134⟩ :=
  holds_reverse edge800

theorem edge801 : Holds level0Subgroup PresentedGroup.of representative ⟨136, [(true, true)], 137⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨95, [(true, true)], 136⟩ :=
    edge135
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨137, [(true, true)], 95⟩ :=
    edge136Inv
  exact scanFacts hp hs (holds_relator 95 (level0Relator 1) (level0_relator 1))

theorem edge801Inv : Holds level0Subgroup PresentedGroup.of representative ⟨137, [(true, false)], 136⟩ :=
  holds_reverse edge801

theorem edge802 : Holds level0Subgroup PresentedGroup.of representative ⟨138, [(true, true)], 139⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨96, [(true, true)], 138⟩ :=
    edge137
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨139, [(true, true)], 96⟩ :=
    edge138Inv
  exact scanFacts hp hs (holds_relator 96 (level0Relator 1) (level0_relator 1))

theorem edge802Inv : Holds level0Subgroup PresentedGroup.of representative ⟨139, [(true, false)], 138⟩ :=
  holds_reverse edge802

theorem edge803 : Holds level0Subgroup PresentedGroup.of representative ⟨140, [(true, true)], 141⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨97, [(true, true)], 140⟩ :=
    edge139
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨141, [(true, true)], 97⟩ :=
    edge140Inv
  exact scanFacts hp hs (holds_relator 97 (level0Relator 1) (level0_relator 1))

theorem edge803Inv : Holds level0Subgroup PresentedGroup.of representative ⟨141, [(true, false)], 140⟩ :=
  holds_reverse edge803

theorem edge804 : Holds level0Subgroup PresentedGroup.of representative ⟨142, [(false, true)], 98⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨98, [(false, true)], 142⟩ :=
    edge141
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨98, [], 98⟩ :=
    (holds_refl 98)
  exact scanFacts hp hs (holds_relator 98 (level0Relator 0) (level0_relator 0))

theorem edge804Inv : Holds level0Subgroup PresentedGroup.of representative ⟨98, [(false, false)], 142⟩ :=
  holds_reverse edge804

theorem edge805 : Holds level0Subgroup PresentedGroup.of representative ⟨143, [(false, true)], 100⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨100, [(false, true)], 143⟩ :=
    edge142
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨100, [], 100⟩ :=
    (holds_refl 100)
  exact scanFacts hp hs (holds_relator 100 (level0Relator 0) (level0_relator 0))

theorem edge805Inv : Holds level0Subgroup PresentedGroup.of representative ⟨100, [(false, false)], 143⟩ :=
  holds_reverse edge805

theorem edge806 : Holds level0Subgroup PresentedGroup.of representative ⟨144, [(false, true)], 101⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨101, [(false, true)], 144⟩ :=
    edge143
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨101, [], 101⟩ :=
    (holds_refl 101)
  exact scanFacts hp hs (holds_relator 101 (level0Relator 0) (level0_relator 0))

theorem edge806Inv : Holds level0Subgroup PresentedGroup.of representative ⟨101, [(false, false)], 144⟩ :=
  holds_reverse edge806

theorem edge807 : Holds level0Subgroup PresentedGroup.of representative ⟨145, [(false, true)], 102⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨102, [(false, true)], 145⟩ :=
    edge144
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨102, [], 102⟩ :=
    (holds_refl 102)
  exact scanFacts hp hs (holds_relator 102 (level0Relator 0) (level0_relator 0))

theorem edge807Inv : Holds level0Subgroup PresentedGroup.of representative ⟨102, [(false, false)], 145⟩ :=
  holds_reverse edge807

theorem edge808 : Holds level0Subgroup PresentedGroup.of representative ⟨146, [(false, true)], 103⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨103, [(false, true)], 146⟩ :=
    edge145
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨103, [], 103⟩ :=
    (holds_refl 103)
  exact scanFacts hp hs (holds_relator 103 (level0Relator 0) (level0_relator 0))

theorem edge808Inv : Holds level0Subgroup PresentedGroup.of representative ⟨103, [(false, false)], 146⟩ :=
  holds_reverse edge808

theorem edge809 : Holds level0Subgroup PresentedGroup.of representative ⟨147, [(false, true)], 104⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨104, [(false, true)], 147⟩ :=
    edge146
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨104, [], 104⟩ :=
    (holds_refl 104)
  exact scanFacts hp hs (holds_relator 104 (level0Relator 0) (level0_relator 0))

theorem edge809Inv : Holds level0Subgroup PresentedGroup.of representative ⟨104, [(false, false)], 147⟩ :=
  holds_reverse edge809

theorem edge810 : Holds level0Subgroup PresentedGroup.of representative ⟨148, [(false, true)], 105⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨105, [(false, true)], 148⟩ :=
    edge147
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨105, [], 105⟩ :=
    (holds_refl 105)
  exact scanFacts hp hs (holds_relator 105 (level0Relator 0) (level0_relator 0))

theorem edge810Inv : Holds level0Subgroup PresentedGroup.of representative ⟨105, [(false, false)], 148⟩ :=
  holds_reverse edge810

theorem edge811 : Holds level0Subgroup PresentedGroup.of representative ⟨149, [(false, true)], 106⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨106, [(false, true)], 149⟩ :=
    edge148
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨106, [], 106⟩ :=
    (holds_refl 106)
  exact scanFacts hp hs (holds_relator 106 (level0Relator 0) (level0_relator 0))

theorem edge811Inv : Holds level0Subgroup PresentedGroup.of representative ⟨106, [(false, false)], 149⟩ :=
  holds_reverse edge811

theorem edge812 : Holds level0Subgroup PresentedGroup.of representative ⟨150, [(false, true)], 107⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨107, [(false, true)], 150⟩ :=
    edge149
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨107, [], 107⟩ :=
    (holds_refl 107)
  exact scanFacts hp hs (holds_relator 107 (level0Relator 0) (level0_relator 0))

theorem edge812Inv : Holds level0Subgroup PresentedGroup.of representative ⟨107, [(false, false)], 150⟩ :=
  holds_reverse edge812

theorem edge813 : Holds level0Subgroup PresentedGroup.of representative ⟨151, [(false, true)], 108⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨108, [(false, true)], 151⟩ :=
    edge150
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨108, [], 108⟩ :=
    (holds_refl 108)
  exact scanFacts hp hs (holds_relator 108 (level0Relator 0) (level0_relator 0))

theorem edge813Inv : Holds level0Subgroup PresentedGroup.of representative ⟨108, [(false, false)], 151⟩ :=
  holds_reverse edge813

theorem edge814 : Holds level0Subgroup PresentedGroup.of representative ⟨152, [(false, true)], 109⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨109, [(false, true)], 152⟩ :=
    edge151
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨109, [], 109⟩ :=
    (holds_refl 109)
  exact scanFacts hp hs (holds_relator 109 (level0Relator 0) (level0_relator 0))

theorem edge814Inv : Holds level0Subgroup PresentedGroup.of representative ⟨109, [(false, false)], 152⟩ :=
  holds_reverse edge814

theorem edge815 : Holds level0Subgroup PresentedGroup.of representative ⟨153, [(false, true)], 110⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨110, [(false, true)], 153⟩ :=
    edge152
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨110, [], 110⟩ :=
    (holds_refl 110)
  exact scanFacts hp hs (holds_relator 110 (level0Relator 0) (level0_relator 0))

theorem edge815Inv : Holds level0Subgroup PresentedGroup.of representative ⟨110, [(false, false)], 153⟩ :=
  holds_reverse edge815

theorem edge816 : Holds level0Subgroup PresentedGroup.of representative ⟨154, [(false, true)], 112⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨112, [(false, true)], 154⟩ :=
    edge153
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨112, [], 112⟩ :=
    (holds_refl 112)
  exact scanFacts hp hs (holds_relator 112 (level0Relator 0) (level0_relator 0))

theorem edge816Inv : Holds level0Subgroup PresentedGroup.of representative ⟨112, [(false, false)], 154⟩ :=
  holds_reverse edge816

theorem edge817 : Holds level0Subgroup PresentedGroup.of representative ⟨155, [(false, true)], 113⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨113, [(false, true)], 155⟩ :=
    edge154
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨113, [], 113⟩ :=
    (holds_refl 113)
  exact scanFacts hp hs (holds_relator 113 (level0Relator 0) (level0_relator 0))

theorem edge817Inv : Holds level0Subgroup PresentedGroup.of representative ⟨113, [(false, false)], 155⟩ :=
  holds_reverse edge817

theorem edge818 : Holds level0Subgroup PresentedGroup.of representative ⟨156, [(false, true)], 114⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨114, [(false, true)], 156⟩ :=
    edge155
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨114, [], 114⟩ :=
    (holds_refl 114)
  exact scanFacts hp hs (holds_relator 114 (level0Relator 0) (level0_relator 0))

theorem edge818Inv : Holds level0Subgroup PresentedGroup.of representative ⟨114, [(false, false)], 156⟩ :=
  holds_reverse edge818

theorem edge819 : Holds level0Subgroup PresentedGroup.of representative ⟨157, [(false, true)], 115⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨115, [(false, true)], 157⟩ :=
    edge156
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨115, [], 115⟩ :=
    (holds_refl 115)
  exact scanFacts hp hs (holds_relator 115 (level0Relator 0) (level0_relator 0))

theorem edge819Inv : Holds level0Subgroup PresentedGroup.of representative ⟨115, [(false, false)], 157⟩ :=
  holds_reverse edge819

theorem edge820 : Holds level0Subgroup PresentedGroup.of representative ⟨158, [(false, true)], 116⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨116, [(false, true)], 158⟩ :=
    edge157
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨116, [], 116⟩ :=
    (holds_refl 116)
  exact scanFacts hp hs (holds_relator 116 (level0Relator 0) (level0_relator 0))

theorem edge820Inv : Holds level0Subgroup PresentedGroup.of representative ⟨116, [(false, false)], 158⟩ :=
  holds_reverse edge820

theorem edge821 : Holds level0Subgroup PresentedGroup.of representative ⟨159, [(false, true)], 117⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨117, [(false, true)], 159⟩ :=
    edge158
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨117, [], 117⟩ :=
    (holds_refl 117)
  exact scanFacts hp hs (holds_relator 117 (level0Relator 0) (level0_relator 0))

theorem edge821Inv : Holds level0Subgroup PresentedGroup.of representative ⟨117, [(false, false)], 159⟩ :=
  holds_reverse edge821

theorem edge822 : Holds level0Subgroup PresentedGroup.of representative ⟨160, [(false, true)], 118⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨118, [(false, true)], 160⟩ :=
    edge159
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨118, [], 118⟩ :=
    (holds_refl 118)
  exact scanFacts hp hs (holds_relator 118 (level0Relator 0) (level0_relator 0))

theorem edge822Inv : Holds level0Subgroup PresentedGroup.of representative ⟨118, [(false, false)], 160⟩ :=
  holds_reverse edge822

theorem edge823 : Holds level0Subgroup PresentedGroup.of representative ⟨161, [(false, true)], 119⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨119, [(false, true)], 161⟩ :=
    edge160
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨119, [], 119⟩ :=
    (holds_refl 119)
  exact scanFacts hp hs (holds_relator 119 (level0Relator 0) (level0_relator 0))

theorem edge823Inv : Holds level0Subgroup PresentedGroup.of representative ⟨119, [(false, false)], 161⟩ :=
  holds_reverse edge823

theorem edge824 : Holds level0Subgroup PresentedGroup.of representative ⟨162, [(false, true)], 120⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨120, [(false, true)], 162⟩ :=
    edge161
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨120, [], 120⟩ :=
    (holds_refl 120)
  exact scanFacts hp hs (holds_relator 120 (level0Relator 0) (level0_relator 0))

theorem edge824Inv : Holds level0Subgroup PresentedGroup.of representative ⟨120, [(false, false)], 162⟩ :=
  holds_reverse edge824

theorem edge825 : Holds level0Subgroup PresentedGroup.of representative ⟨163, [(false, true)], 121⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨121, [(false, true)], 163⟩ :=
    edge162
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨121, [], 121⟩ :=
    (holds_refl 121)
  exact scanFacts hp hs (holds_relator 121 (level0Relator 0) (level0_relator 0))

theorem edge825Inv : Holds level0Subgroup PresentedGroup.of representative ⟨121, [(false, false)], 163⟩ :=
  holds_reverse edge825

theorem edge826 : Holds level0Subgroup PresentedGroup.of representative ⟨164, [(false, true)], 122⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨122, [(false, true)], 164⟩ :=
    edge163
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨122, [], 122⟩ :=
    (holds_refl 122)
  exact scanFacts hp hs (holds_relator 122 (level0Relator 0) (level0_relator 0))

theorem edge826Inv : Holds level0Subgroup PresentedGroup.of representative ⟨122, [(false, false)], 164⟩ :=
  holds_reverse edge826

theorem edge827 : Holds level0Subgroup PresentedGroup.of representative ⟨165, [(false, true)], 123⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨123, [(false, true)], 165⟩ :=
    edge164
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨123, [], 123⟩ :=
    (holds_refl 123)
  exact scanFacts hp hs (holds_relator 123 (level0Relator 0) (level0_relator 0))

theorem edge827Inv : Holds level0Subgroup PresentedGroup.of representative ⟨123, [(false, false)], 165⟩ :=
  holds_reverse edge827

theorem edge828 : Holds level0Subgroup PresentedGroup.of representative ⟨166, [(false, true)], 124⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨124, [(false, true)], 166⟩ :=
    edge165
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨124, [], 124⟩ :=
    (holds_refl 124)
  exact scanFacts hp hs (holds_relator 124 (level0Relator 0) (level0_relator 0))

theorem edge828Inv : Holds level0Subgroup PresentedGroup.of representative ⟨124, [(false, false)], 166⟩ :=
  holds_reverse edge828

theorem edge829 : Holds level0Subgroup PresentedGroup.of representative ⟨167, [(false, true)], 125⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨125, [(false, true)], 167⟩ :=
    edge166
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨125, [], 125⟩ :=
    (holds_refl 125)
  exact scanFacts hp hs (holds_relator 125 (level0Relator 0) (level0_relator 0))

theorem edge829Inv : Holds level0Subgroup PresentedGroup.of representative ⟨125, [(false, false)], 167⟩ :=
  holds_reverse edge829

theorem edge830 : Holds level0Subgroup PresentedGroup.of representative ⟨168, [(false, true)], 126⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨126, [(false, true)], 168⟩ :=
    edge167
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨126, [], 126⟩ :=
    (holds_refl 126)
  exact scanFacts hp hs (holds_relator 126 (level0Relator 0) (level0_relator 0))

theorem edge830Inv : Holds level0Subgroup PresentedGroup.of representative ⟨126, [(false, false)], 168⟩ :=
  holds_reverse edge830

theorem edge831 : Holds level0Subgroup PresentedGroup.of representative ⟨169, [(false, true)], 127⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨127, [(false, true)], 169⟩ :=
    edge168
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨127, [], 127⟩ :=
    (holds_refl 127)
  exact scanFacts hp hs (holds_relator 127 (level0Relator 0) (level0_relator 0))

theorem edge831Inv : Holds level0Subgroup PresentedGroup.of representative ⟨127, [(false, false)], 169⟩ :=
  holds_reverse edge831


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
