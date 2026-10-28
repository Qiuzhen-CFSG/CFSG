module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges01

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

theorem edge128 : Holds level0Subgroup PresentedGroup.of representative ⟨91, [(true, false)], 129⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge128Inv : Holds level0Subgroup PresentedGroup.of representative ⟨129, [(true, true)], 91⟩ :=
  holds_reverse edge128

theorem edge129 : Holds level0Subgroup PresentedGroup.of representative ⟨92, [(true, true)], 130⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge129Inv : Holds level0Subgroup PresentedGroup.of representative ⟨130, [(true, false)], 92⟩ :=
  holds_reverse edge129

theorem edge130 : Holds level0Subgroup PresentedGroup.of representative ⟨92, [(true, false)], 131⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge130Inv : Holds level0Subgroup PresentedGroup.of representative ⟨131, [(true, true)], 92⟩ :=
  holds_reverse edge130

theorem edge131 : Holds level0Subgroup PresentedGroup.of representative ⟨93, [(true, true)], 132⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge131Inv : Holds level0Subgroup PresentedGroup.of representative ⟨132, [(true, false)], 93⟩ :=
  holds_reverse edge131

theorem edge132 : Holds level0Subgroup PresentedGroup.of representative ⟨93, [(true, false)], 133⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge132Inv : Holds level0Subgroup PresentedGroup.of representative ⟨133, [(true, true)], 93⟩ :=
  holds_reverse edge132

theorem edge133 : Holds level0Subgroup PresentedGroup.of representative ⟨94, [(true, true)], 134⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge133Inv : Holds level0Subgroup PresentedGroup.of representative ⟨134, [(true, false)], 94⟩ :=
  holds_reverse edge133

theorem edge134 : Holds level0Subgroup PresentedGroup.of representative ⟨94, [(true, false)], 135⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge134Inv : Holds level0Subgroup PresentedGroup.of representative ⟨135, [(true, true)], 94⟩ :=
  holds_reverse edge134

theorem edge135 : Holds level0Subgroup PresentedGroup.of representative ⟨95, [(true, true)], 136⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge135Inv : Holds level0Subgroup PresentedGroup.of representative ⟨136, [(true, false)], 95⟩ :=
  holds_reverse edge135

theorem edge136 : Holds level0Subgroup PresentedGroup.of representative ⟨95, [(true, false)], 137⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge136Inv : Holds level0Subgroup PresentedGroup.of representative ⟨137, [(true, true)], 95⟩ :=
  holds_reverse edge136

theorem edge137 : Holds level0Subgroup PresentedGroup.of representative ⟨96, [(true, true)], 138⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge137Inv : Holds level0Subgroup PresentedGroup.of representative ⟨138, [(true, false)], 96⟩ :=
  holds_reverse edge137

theorem edge138 : Holds level0Subgroup PresentedGroup.of representative ⟨96, [(true, false)], 139⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge138Inv : Holds level0Subgroup PresentedGroup.of representative ⟨139, [(true, true)], 96⟩ :=
  holds_reverse edge138

theorem edge139 : Holds level0Subgroup PresentedGroup.of representative ⟨97, [(true, true)], 140⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge139Inv : Holds level0Subgroup PresentedGroup.of representative ⟨140, [(true, false)], 97⟩ :=
  holds_reverse edge139

theorem edge140 : Holds level0Subgroup PresentedGroup.of representative ⟨97, [(true, false)], 141⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge140Inv : Holds level0Subgroup PresentedGroup.of representative ⟨141, [(true, true)], 97⟩ :=
  holds_reverse edge140

theorem edge141 : Holds level0Subgroup PresentedGroup.of representative ⟨98, [(false, true)], 142⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge141Inv : Holds level0Subgroup PresentedGroup.of representative ⟨142, [(false, false)], 98⟩ :=
  holds_reverse edge141

theorem edge142 : Holds level0Subgroup PresentedGroup.of representative ⟨100, [(false, true)], 143⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge142Inv : Holds level0Subgroup PresentedGroup.of representative ⟨143, [(false, false)], 100⟩ :=
  holds_reverse edge142

theorem edge143 : Holds level0Subgroup PresentedGroup.of representative ⟨101, [(false, true)], 144⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge143Inv : Holds level0Subgroup PresentedGroup.of representative ⟨144, [(false, false)], 101⟩ :=
  holds_reverse edge143

theorem edge144 : Holds level0Subgroup PresentedGroup.of representative ⟨102, [(false, true)], 145⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge144Inv : Holds level0Subgroup PresentedGroup.of representative ⟨145, [(false, false)], 102⟩ :=
  holds_reverse edge144

theorem edge145 : Holds level0Subgroup PresentedGroup.of representative ⟨103, [(false, true)], 146⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge145Inv : Holds level0Subgroup PresentedGroup.of representative ⟨146, [(false, false)], 103⟩ :=
  holds_reverse edge145

theorem edge146 : Holds level0Subgroup PresentedGroup.of representative ⟨104, [(false, true)], 147⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge146Inv : Holds level0Subgroup PresentedGroup.of representative ⟨147, [(false, false)], 104⟩ :=
  holds_reverse edge146

theorem edge147 : Holds level0Subgroup PresentedGroup.of representative ⟨105, [(false, true)], 148⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge147Inv : Holds level0Subgroup PresentedGroup.of representative ⟨148, [(false, false)], 105⟩ :=
  holds_reverse edge147

theorem edge148 : Holds level0Subgroup PresentedGroup.of representative ⟨106, [(false, true)], 149⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge148Inv : Holds level0Subgroup PresentedGroup.of representative ⟨149, [(false, false)], 106⟩ :=
  holds_reverse edge148

theorem edge149 : Holds level0Subgroup PresentedGroup.of representative ⟨107, [(false, true)], 150⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge149Inv : Holds level0Subgroup PresentedGroup.of representative ⟨150, [(false, false)], 107⟩ :=
  holds_reverse edge149

theorem edge150 : Holds level0Subgroup PresentedGroup.of representative ⟨108, [(false, true)], 151⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge150Inv : Holds level0Subgroup PresentedGroup.of representative ⟨151, [(false, false)], 108⟩ :=
  holds_reverse edge150

theorem edge151 : Holds level0Subgroup PresentedGroup.of representative ⟨109, [(false, true)], 152⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge151Inv : Holds level0Subgroup PresentedGroup.of representative ⟨152, [(false, false)], 109⟩ :=
  holds_reverse edge151

theorem edge152 : Holds level0Subgroup PresentedGroup.of representative ⟨110, [(false, true)], 153⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge152Inv : Holds level0Subgroup PresentedGroup.of representative ⟨153, [(false, false)], 110⟩ :=
  holds_reverse edge152

theorem edge153 : Holds level0Subgroup PresentedGroup.of representative ⟨112, [(false, true)], 154⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge153Inv : Holds level0Subgroup PresentedGroup.of representative ⟨154, [(false, false)], 112⟩ :=
  holds_reverse edge153

theorem edge154 : Holds level0Subgroup PresentedGroup.of representative ⟨113, [(false, true)], 155⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge154Inv : Holds level0Subgroup PresentedGroup.of representative ⟨155, [(false, false)], 113⟩ :=
  holds_reverse edge154

theorem edge155 : Holds level0Subgroup PresentedGroup.of representative ⟨114, [(false, true)], 156⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge155Inv : Holds level0Subgroup PresentedGroup.of representative ⟨156, [(false, false)], 114⟩ :=
  holds_reverse edge155

theorem edge156 : Holds level0Subgroup PresentedGroup.of representative ⟨115, [(false, true)], 157⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge156Inv : Holds level0Subgroup PresentedGroup.of representative ⟨157, [(false, false)], 115⟩ :=
  holds_reverse edge156

theorem edge157 : Holds level0Subgroup PresentedGroup.of representative ⟨116, [(false, true)], 158⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge157Inv : Holds level0Subgroup PresentedGroup.of representative ⟨158, [(false, false)], 116⟩ :=
  holds_reverse edge157

theorem edge158 : Holds level0Subgroup PresentedGroup.of representative ⟨117, [(false, true)], 159⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge158Inv : Holds level0Subgroup PresentedGroup.of representative ⟨159, [(false, false)], 117⟩ :=
  holds_reverse edge158

theorem edge159 : Holds level0Subgroup PresentedGroup.of representative ⟨118, [(false, true)], 160⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge159Inv : Holds level0Subgroup PresentedGroup.of representative ⟨160, [(false, false)], 118⟩ :=
  holds_reverse edge159

theorem edge160 : Holds level0Subgroup PresentedGroup.of representative ⟨119, [(false, true)], 161⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge160Inv : Holds level0Subgroup PresentedGroup.of representative ⟨161, [(false, false)], 119⟩ :=
  holds_reverse edge160

theorem edge161 : Holds level0Subgroup PresentedGroup.of representative ⟨120, [(false, true)], 162⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge161Inv : Holds level0Subgroup PresentedGroup.of representative ⟨162, [(false, false)], 120⟩ :=
  holds_reverse edge161

theorem edge162 : Holds level0Subgroup PresentedGroup.of representative ⟨121, [(false, true)], 163⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge162Inv : Holds level0Subgroup PresentedGroup.of representative ⟨163, [(false, false)], 121⟩ :=
  holds_reverse edge162

theorem edge163 : Holds level0Subgroup PresentedGroup.of representative ⟨122, [(false, true)], 164⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge163Inv : Holds level0Subgroup PresentedGroup.of representative ⟨164, [(false, false)], 122⟩ :=
  holds_reverse edge163

theorem edge164 : Holds level0Subgroup PresentedGroup.of representative ⟨123, [(false, true)], 165⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge164Inv : Holds level0Subgroup PresentedGroup.of representative ⟨165, [(false, false)], 123⟩ :=
  holds_reverse edge164

theorem edge165 : Holds level0Subgroup PresentedGroup.of representative ⟨124, [(false, true)], 166⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge165Inv : Holds level0Subgroup PresentedGroup.of representative ⟨166, [(false, false)], 124⟩ :=
  holds_reverse edge165

theorem edge166 : Holds level0Subgroup PresentedGroup.of representative ⟨125, [(false, true)], 167⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge166Inv : Holds level0Subgroup PresentedGroup.of representative ⟨167, [(false, false)], 125⟩ :=
  holds_reverse edge166

theorem edge167 : Holds level0Subgroup PresentedGroup.of representative ⟨126, [(false, true)], 168⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge167Inv : Holds level0Subgroup PresentedGroup.of representative ⟨168, [(false, false)], 126⟩ :=
  holds_reverse edge167

theorem edge168 : Holds level0Subgroup PresentedGroup.of representative ⟨127, [(false, true)], 169⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge168Inv : Holds level0Subgroup PresentedGroup.of representative ⟨169, [(false, false)], 127⟩ :=
  holds_reverse edge168

theorem edge169 : Holds level0Subgroup PresentedGroup.of representative ⟨128, [(false, true)], 170⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge169Inv : Holds level0Subgroup PresentedGroup.of representative ⟨170, [(false, false)], 128⟩ :=
  holds_reverse edge169

theorem edge170 : Holds level0Subgroup PresentedGroup.of representative ⟨129, [(false, true)], 171⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge170Inv : Holds level0Subgroup PresentedGroup.of representative ⟨171, [(false, false)], 129⟩ :=
  holds_reverse edge170

theorem edge171 : Holds level0Subgroup PresentedGroup.of representative ⟨130, [(false, true)], 172⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge171Inv : Holds level0Subgroup PresentedGroup.of representative ⟨172, [(false, false)], 130⟩ :=
  holds_reverse edge171

theorem edge172 : Holds level0Subgroup PresentedGroup.of representative ⟨131, [(false, true)], 173⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge172Inv : Holds level0Subgroup PresentedGroup.of representative ⟨173, [(false, false)], 131⟩ :=
  holds_reverse edge172

theorem edge173 : Holds level0Subgroup PresentedGroup.of representative ⟨132, [(false, true)], 174⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge173Inv : Holds level0Subgroup PresentedGroup.of representative ⟨174, [(false, false)], 132⟩ :=
  holds_reverse edge173

theorem edge174 : Holds level0Subgroup PresentedGroup.of representative ⟨133, [(false, true)], 175⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge174Inv : Holds level0Subgroup PresentedGroup.of representative ⟨175, [(false, false)], 133⟩ :=
  holds_reverse edge174

theorem edge175 : Holds level0Subgroup PresentedGroup.of representative ⟨134, [(false, true)], 176⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge175Inv : Holds level0Subgroup PresentedGroup.of representative ⟨176, [(false, false)], 134⟩ :=
  holds_reverse edge175

theorem edge176 : Holds level0Subgroup PresentedGroup.of representative ⟨135, [(false, true)], 177⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge176Inv : Holds level0Subgroup PresentedGroup.of representative ⟨177, [(false, false)], 135⟩ :=
  holds_reverse edge176

theorem edge177 : Holds level0Subgroup PresentedGroup.of representative ⟨136, [(false, true)], 178⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge177Inv : Holds level0Subgroup PresentedGroup.of representative ⟨178, [(false, false)], 136⟩ :=
  holds_reverse edge177

theorem edge178 : Holds level0Subgroup PresentedGroup.of representative ⟨137, [(false, true)], 179⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge178Inv : Holds level0Subgroup PresentedGroup.of representative ⟨179, [(false, false)], 137⟩ :=
  holds_reverse edge178

theorem edge179 : Holds level0Subgroup PresentedGroup.of representative ⟨138, [(false, true)], 180⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge179Inv : Holds level0Subgroup PresentedGroup.of representative ⟨180, [(false, false)], 138⟩ :=
  holds_reverse edge179

theorem edge180 : Holds level0Subgroup PresentedGroup.of representative ⟨139, [(false, true)], 181⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge180Inv : Holds level0Subgroup PresentedGroup.of representative ⟨181, [(false, false)], 139⟩ :=
  holds_reverse edge180

theorem edge181 : Holds level0Subgroup PresentedGroup.of representative ⟨140, [(false, true)], 182⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge181Inv : Holds level0Subgroup PresentedGroup.of representative ⟨182, [(false, false)], 140⟩ :=
  holds_reverse edge181

theorem edge182 : Holds level0Subgroup PresentedGroup.of representative ⟨141, [(false, true)], 183⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge182Inv : Holds level0Subgroup PresentedGroup.of representative ⟨183, [(false, false)], 141⟩ :=
  holds_reverse edge182

theorem edge183 : Holds level0Subgroup PresentedGroup.of representative ⟨142, [(true, true)], 184⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge183Inv : Holds level0Subgroup PresentedGroup.of representative ⟨184, [(true, false)], 142⟩ :=
  holds_reverse edge183

theorem edge184 : Holds level0Subgroup PresentedGroup.of representative ⟨142, [(true, false)], 185⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge184Inv : Holds level0Subgroup PresentedGroup.of representative ⟨185, [(true, true)], 142⟩ :=
  holds_reverse edge184

theorem edge185 : Holds level0Subgroup PresentedGroup.of representative ⟨143, [(true, true)], 186⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge185Inv : Holds level0Subgroup PresentedGroup.of representative ⟨186, [(true, false)], 143⟩ :=
  holds_reverse edge185

theorem edge186 : Holds level0Subgroup PresentedGroup.of representative ⟨143, [(true, false)], 187⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge186Inv : Holds level0Subgroup PresentedGroup.of representative ⟨187, [(true, true)], 143⟩ :=
  holds_reverse edge186

theorem edge187 : Holds level0Subgroup PresentedGroup.of representative ⟨144, [(true, true)], 188⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge187Inv : Holds level0Subgroup PresentedGroup.of representative ⟨188, [(true, false)], 144⟩ :=
  holds_reverse edge187

theorem edge188 : Holds level0Subgroup PresentedGroup.of representative ⟨144, [(true, false)], 189⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge188Inv : Holds level0Subgroup PresentedGroup.of representative ⟨189, [(true, true)], 144⟩ :=
  holds_reverse edge188

theorem edge189 : Holds level0Subgroup PresentedGroup.of representative ⟨145, [(true, true)], 190⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge189Inv : Holds level0Subgroup PresentedGroup.of representative ⟨190, [(true, false)], 145⟩ :=
  holds_reverse edge189

theorem edge190 : Holds level0Subgroup PresentedGroup.of representative ⟨145, [(true, false)], 191⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge190Inv : Holds level0Subgroup PresentedGroup.of representative ⟨191, [(true, true)], 145⟩ :=
  holds_reverse edge190

theorem edge191 : Holds level0Subgroup PresentedGroup.of representative ⟨146, [(true, true)], 192⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge191Inv : Holds level0Subgroup PresentedGroup.of representative ⟨192, [(true, false)], 146⟩ :=
  holds_reverse edge191


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
