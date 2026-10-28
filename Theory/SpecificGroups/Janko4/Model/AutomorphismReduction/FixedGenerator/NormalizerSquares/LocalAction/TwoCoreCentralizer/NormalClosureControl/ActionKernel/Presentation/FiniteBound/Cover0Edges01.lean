module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges00

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

theorem edge64 : Holds level0Subgroup PresentedGroup.of representative ⟨46, [(true, false)], 65⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge64Inv : Holds level0Subgroup PresentedGroup.of representative ⟨65, [(true, true)], 46⟩ :=
  holds_reverse edge64

theorem edge65 : Holds level0Subgroup PresentedGroup.of representative ⟨47, [(true, true)], 66⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge65Inv : Holds level0Subgroup PresentedGroup.of representative ⟨66, [(true, false)], 47⟩ :=
  holds_reverse edge65

theorem edge66 : Holds level0Subgroup PresentedGroup.of representative ⟨47, [(true, false)], 67⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge66Inv : Holds level0Subgroup PresentedGroup.of representative ⟨67, [(true, true)], 47⟩ :=
  holds_reverse edge66

theorem edge67 : Holds level0Subgroup PresentedGroup.of representative ⟨48, [(true, true)], 68⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge67Inv : Holds level0Subgroup PresentedGroup.of representative ⟨68, [(true, false)], 48⟩ :=
  holds_reverse edge67

theorem edge68 : Holds level0Subgroup PresentedGroup.of representative ⟨48, [(true, false)], 69⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge68Inv : Holds level0Subgroup PresentedGroup.of representative ⟨69, [(true, true)], 48⟩ :=
  holds_reverse edge68

theorem edge69 : Holds level0Subgroup PresentedGroup.of representative ⟨49, [(true, true)], 70⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge69Inv : Holds level0Subgroup PresentedGroup.of representative ⟨70, [(true, false)], 49⟩ :=
  holds_reverse edge69

theorem edge70 : Holds level0Subgroup PresentedGroup.of representative ⟨49, [(true, false)], 71⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge70Inv : Holds level0Subgroup PresentedGroup.of representative ⟨71, [(true, true)], 49⟩ :=
  holds_reverse edge70

theorem edge71 : Holds level0Subgroup PresentedGroup.of representative ⟨50, [(true, true)], 72⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge71Inv : Holds level0Subgroup PresentedGroup.of representative ⟨72, [(true, false)], 50⟩ :=
  holds_reverse edge71

theorem edge72 : Holds level0Subgroup PresentedGroup.of representative ⟨50, [(true, false)], 73⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge72Inv : Holds level0Subgroup PresentedGroup.of representative ⟨73, [(true, true)], 50⟩ :=
  holds_reverse edge72

theorem edge73 : Holds level0Subgroup PresentedGroup.of representative ⟨51, [(true, true)], 74⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge73Inv : Holds level0Subgroup PresentedGroup.of representative ⟨74, [(true, false)], 51⟩ :=
  holds_reverse edge73

theorem edge74 : Holds level0Subgroup PresentedGroup.of representative ⟨51, [(true, false)], 75⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge74Inv : Holds level0Subgroup PresentedGroup.of representative ⟨75, [(true, true)], 51⟩ :=
  holds_reverse edge74

theorem edge75 : Holds level0Subgroup PresentedGroup.of representative ⟨52, [(false, true)], 76⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge75Inv : Holds level0Subgroup PresentedGroup.of representative ⟨76, [(false, false)], 52⟩ :=
  holds_reverse edge75

theorem edge76 : Holds level0Subgroup PresentedGroup.of representative ⟨53, [(false, true)], 77⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge76Inv : Holds level0Subgroup PresentedGroup.of representative ⟨77, [(false, false)], 53⟩ :=
  holds_reverse edge76

theorem edge77 : Holds level0Subgroup PresentedGroup.of representative ⟨55, [(false, true)], 78⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge77Inv : Holds level0Subgroup PresentedGroup.of representative ⟨78, [(false, false)], 55⟩ :=
  holds_reverse edge77

theorem edge78 : Holds level0Subgroup PresentedGroup.of representative ⟨56, [(false, true)], 79⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge78Inv : Holds level0Subgroup PresentedGroup.of representative ⟨79, [(false, false)], 56⟩ :=
  holds_reverse edge78

theorem edge79 : Holds level0Subgroup PresentedGroup.of representative ⟨57, [(false, true)], 80⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge79Inv : Holds level0Subgroup PresentedGroup.of representative ⟨80, [(false, false)], 57⟩ :=
  holds_reverse edge79

theorem edge80 : Holds level0Subgroup PresentedGroup.of representative ⟨58, [(false, true)], 81⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge80Inv : Holds level0Subgroup PresentedGroup.of representative ⟨81, [(false, false)], 58⟩ :=
  holds_reverse edge80

theorem edge81 : Holds level0Subgroup PresentedGroup.of representative ⟨59, [(false, true)], 82⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge81Inv : Holds level0Subgroup PresentedGroup.of representative ⟨82, [(false, false)], 59⟩ :=
  holds_reverse edge81

theorem edge82 : Holds level0Subgroup PresentedGroup.of representative ⟨60, [(false, true)], 83⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge82Inv : Holds level0Subgroup PresentedGroup.of representative ⟨83, [(false, false)], 60⟩ :=
  holds_reverse edge82

theorem edge83 : Holds level0Subgroup PresentedGroup.of representative ⟨61, [(false, true)], 84⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge83Inv : Holds level0Subgroup PresentedGroup.of representative ⟨84, [(false, false)], 61⟩ :=
  holds_reverse edge83

theorem edge84 : Holds level0Subgroup PresentedGroup.of representative ⟨62, [(false, true)], 85⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge84Inv : Holds level0Subgroup PresentedGroup.of representative ⟨85, [(false, false)], 62⟩ :=
  holds_reverse edge84

theorem edge85 : Holds level0Subgroup PresentedGroup.of representative ⟨63, [(false, true)], 86⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge85Inv : Holds level0Subgroup PresentedGroup.of representative ⟨86, [(false, false)], 63⟩ :=
  holds_reverse edge85

theorem edge86 : Holds level0Subgroup PresentedGroup.of representative ⟨64, [(false, true)], 87⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge86Inv : Holds level0Subgroup PresentedGroup.of representative ⟨87, [(false, false)], 64⟩ :=
  holds_reverse edge86

theorem edge87 : Holds level0Subgroup PresentedGroup.of representative ⟨66, [(false, true)], 88⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge87Inv : Holds level0Subgroup PresentedGroup.of representative ⟨88, [(false, false)], 66⟩ :=
  holds_reverse edge87

theorem edge88 : Holds level0Subgroup PresentedGroup.of representative ⟨67, [(false, true)], 89⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge88Inv : Holds level0Subgroup PresentedGroup.of representative ⟨89, [(false, false)], 67⟩ :=
  holds_reverse edge88

theorem edge89 : Holds level0Subgroup PresentedGroup.of representative ⟨68, [(false, true)], 90⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge89Inv : Holds level0Subgroup PresentedGroup.of representative ⟨90, [(false, false)], 68⟩ :=
  holds_reverse edge89

theorem edge90 : Holds level0Subgroup PresentedGroup.of representative ⟨69, [(false, true)], 91⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge90Inv : Holds level0Subgroup PresentedGroup.of representative ⟨91, [(false, false)], 69⟩ :=
  holds_reverse edge90

theorem edge91 : Holds level0Subgroup PresentedGroup.of representative ⟨70, [(false, true)], 92⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge91Inv : Holds level0Subgroup PresentedGroup.of representative ⟨92, [(false, false)], 70⟩ :=
  holds_reverse edge91

theorem edge92 : Holds level0Subgroup PresentedGroup.of representative ⟨71, [(false, true)], 93⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge92Inv : Holds level0Subgroup PresentedGroup.of representative ⟨93, [(false, false)], 71⟩ :=
  holds_reverse edge92

theorem edge93 : Holds level0Subgroup PresentedGroup.of representative ⟨72, [(false, true)], 94⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge93Inv : Holds level0Subgroup PresentedGroup.of representative ⟨94, [(false, false)], 72⟩ :=
  holds_reverse edge93

theorem edge94 : Holds level0Subgroup PresentedGroup.of representative ⟨73, [(false, true)], 95⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge94Inv : Holds level0Subgroup PresentedGroup.of representative ⟨95, [(false, false)], 73⟩ :=
  holds_reverse edge94

theorem edge95 : Holds level0Subgroup PresentedGroup.of representative ⟨74, [(false, true)], 96⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge95Inv : Holds level0Subgroup PresentedGroup.of representative ⟨96, [(false, false)], 74⟩ :=
  holds_reverse edge95

theorem edge96 : Holds level0Subgroup PresentedGroup.of representative ⟨75, [(false, true)], 97⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge96Inv : Holds level0Subgroup PresentedGroup.of representative ⟨97, [(false, false)], 75⟩ :=
  holds_reverse edge96

theorem edge97 : Holds level0Subgroup PresentedGroup.of representative ⟨76, [(true, true)], 98⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge97Inv : Holds level0Subgroup PresentedGroup.of representative ⟨98, [(true, false)], 76⟩ :=
  holds_reverse edge97

theorem edge98 : Holds level0Subgroup PresentedGroup.of representative ⟨76, [(true, false)], 99⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge98Inv : Holds level0Subgroup PresentedGroup.of representative ⟨99, [(true, true)], 76⟩ :=
  holds_reverse edge98

theorem edge99 : Holds level0Subgroup PresentedGroup.of representative ⟨77, [(true, true)], 100⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge99Inv : Holds level0Subgroup PresentedGroup.of representative ⟨100, [(true, false)], 77⟩ :=
  holds_reverse edge99

theorem edge100 : Holds level0Subgroup PresentedGroup.of representative ⟨77, [(true, false)], 101⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge100Inv : Holds level0Subgroup PresentedGroup.of representative ⟨101, [(true, true)], 77⟩ :=
  holds_reverse edge100

theorem edge101 : Holds level0Subgroup PresentedGroup.of representative ⟨78, [(true, true)], 102⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge101Inv : Holds level0Subgroup PresentedGroup.of representative ⟨102, [(true, false)], 78⟩ :=
  holds_reverse edge101

theorem edge102 : Holds level0Subgroup PresentedGroup.of representative ⟨78, [(true, false)], 103⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge102Inv : Holds level0Subgroup PresentedGroup.of representative ⟨103, [(true, true)], 78⟩ :=
  holds_reverse edge102

theorem edge103 : Holds level0Subgroup PresentedGroup.of representative ⟨79, [(true, true)], 104⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge103Inv : Holds level0Subgroup PresentedGroup.of representative ⟨104, [(true, false)], 79⟩ :=
  holds_reverse edge103

theorem edge104 : Holds level0Subgroup PresentedGroup.of representative ⟨79, [(true, false)], 105⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge104Inv : Holds level0Subgroup PresentedGroup.of representative ⟨105, [(true, true)], 79⟩ :=
  holds_reverse edge104

theorem edge105 : Holds level0Subgroup PresentedGroup.of representative ⟨80, [(true, true)], 106⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge105Inv : Holds level0Subgroup PresentedGroup.of representative ⟨106, [(true, false)], 80⟩ :=
  holds_reverse edge105

theorem edge106 : Holds level0Subgroup PresentedGroup.of representative ⟨80, [(true, false)], 107⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge106Inv : Holds level0Subgroup PresentedGroup.of representative ⟨107, [(true, true)], 80⟩ :=
  holds_reverse edge106

theorem edge107 : Holds level0Subgroup PresentedGroup.of representative ⟨81, [(true, true)], 108⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge107Inv : Holds level0Subgroup PresentedGroup.of representative ⟨108, [(true, false)], 81⟩ :=
  holds_reverse edge107

theorem edge108 : Holds level0Subgroup PresentedGroup.of representative ⟨81, [(true, false)], 109⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge108Inv : Holds level0Subgroup PresentedGroup.of representative ⟨109, [(true, true)], 81⟩ :=
  holds_reverse edge108

theorem edge109 : Holds level0Subgroup PresentedGroup.of representative ⟨82, [(true, true)], 110⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge109Inv : Holds level0Subgroup PresentedGroup.of representative ⟨110, [(true, false)], 82⟩ :=
  holds_reverse edge109

theorem edge110 : Holds level0Subgroup PresentedGroup.of representative ⟨82, [(true, false)], 111⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge110Inv : Holds level0Subgroup PresentedGroup.of representative ⟨111, [(true, true)], 82⟩ :=
  holds_reverse edge110

theorem edge111 : Holds level0Subgroup PresentedGroup.of representative ⟨83, [(true, true)], 112⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge111Inv : Holds level0Subgroup PresentedGroup.of representative ⟨112, [(true, false)], 83⟩ :=
  holds_reverse edge111

theorem edge112 : Holds level0Subgroup PresentedGroup.of representative ⟨83, [(true, false)], 113⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge112Inv : Holds level0Subgroup PresentedGroup.of representative ⟨113, [(true, true)], 83⟩ :=
  holds_reverse edge112

theorem edge113 : Holds level0Subgroup PresentedGroup.of representative ⟨84, [(true, true)], 114⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge113Inv : Holds level0Subgroup PresentedGroup.of representative ⟨114, [(true, false)], 84⟩ :=
  holds_reverse edge113

theorem edge114 : Holds level0Subgroup PresentedGroup.of representative ⟨84, [(true, false)], 115⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge114Inv : Holds level0Subgroup PresentedGroup.of representative ⟨115, [(true, true)], 84⟩ :=
  holds_reverse edge114

theorem edge115 : Holds level0Subgroup PresentedGroup.of representative ⟨85, [(true, true)], 116⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge115Inv : Holds level0Subgroup PresentedGroup.of representative ⟨116, [(true, false)], 85⟩ :=
  holds_reverse edge115

theorem edge116 : Holds level0Subgroup PresentedGroup.of representative ⟨85, [(true, false)], 117⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge116Inv : Holds level0Subgroup PresentedGroup.of representative ⟨117, [(true, true)], 85⟩ :=
  holds_reverse edge116

theorem edge117 : Holds level0Subgroup PresentedGroup.of representative ⟨86, [(true, true)], 118⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge117Inv : Holds level0Subgroup PresentedGroup.of representative ⟨118, [(true, false)], 86⟩ :=
  holds_reverse edge117

theorem edge118 : Holds level0Subgroup PresentedGroup.of representative ⟨86, [(true, false)], 119⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge118Inv : Holds level0Subgroup PresentedGroup.of representative ⟨119, [(true, true)], 86⟩ :=
  holds_reverse edge118

theorem edge119 : Holds level0Subgroup PresentedGroup.of representative ⟨87, [(true, true)], 120⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge119Inv : Holds level0Subgroup PresentedGroup.of representative ⟨120, [(true, false)], 87⟩ :=
  holds_reverse edge119

theorem edge120 : Holds level0Subgroup PresentedGroup.of representative ⟨87, [(true, false)], 121⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge120Inv : Holds level0Subgroup PresentedGroup.of representative ⟨121, [(true, true)], 87⟩ :=
  holds_reverse edge120

theorem edge121 : Holds level0Subgroup PresentedGroup.of representative ⟨88, [(true, true)], 122⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge121Inv : Holds level0Subgroup PresentedGroup.of representative ⟨122, [(true, false)], 88⟩ :=
  holds_reverse edge121

theorem edge122 : Holds level0Subgroup PresentedGroup.of representative ⟨88, [(true, false)], 123⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge122Inv : Holds level0Subgroup PresentedGroup.of representative ⟨123, [(true, true)], 88⟩ :=
  holds_reverse edge122

theorem edge123 : Holds level0Subgroup PresentedGroup.of representative ⟨89, [(true, true)], 124⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge123Inv : Holds level0Subgroup PresentedGroup.of representative ⟨124, [(true, false)], 89⟩ :=
  holds_reverse edge123

theorem edge124 : Holds level0Subgroup PresentedGroup.of representative ⟨89, [(true, false)], 125⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge124Inv : Holds level0Subgroup PresentedGroup.of representative ⟨125, [(true, true)], 89⟩ :=
  holds_reverse edge124

theorem edge125 : Holds level0Subgroup PresentedGroup.of representative ⟨90, [(true, true)], 126⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge125Inv : Holds level0Subgroup PresentedGroup.of representative ⟨126, [(true, false)], 90⟩ :=
  holds_reverse edge125

theorem edge126 : Holds level0Subgroup PresentedGroup.of representative ⟨90, [(true, false)], 127⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge126Inv : Holds level0Subgroup PresentedGroup.of representative ⟨127, [(true, true)], 90⟩ :=
  holds_reverse edge126

theorem edge127 : Holds level0Subgroup PresentedGroup.of representative ⟨91, [(true, true)], 128⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge127Inv : Holds level0Subgroup PresentedGroup.of representative ⟨128, [(true, false)], 91⟩ :=
  holds_reverse edge127


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
