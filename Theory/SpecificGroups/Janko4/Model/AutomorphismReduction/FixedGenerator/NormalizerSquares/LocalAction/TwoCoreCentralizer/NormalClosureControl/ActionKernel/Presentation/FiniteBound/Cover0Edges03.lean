module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges02

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

theorem edge192 : Holds level0Subgroup PresentedGroup.of representative ⟨146, [(true, false)], 193⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge192Inv : Holds level0Subgroup PresentedGroup.of representative ⟨193, [(true, true)], 146⟩ :=
  holds_reverse edge192

theorem edge193 : Holds level0Subgroup PresentedGroup.of representative ⟨147, [(true, true)], 194⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge193Inv : Holds level0Subgroup PresentedGroup.of representative ⟨194, [(true, false)], 147⟩ :=
  holds_reverse edge193

theorem edge194 : Holds level0Subgroup PresentedGroup.of representative ⟨147, [(true, false)], 195⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge194Inv : Holds level0Subgroup PresentedGroup.of representative ⟨195, [(true, true)], 147⟩ :=
  holds_reverse edge194

theorem edge195 : Holds level0Subgroup PresentedGroup.of representative ⟨148, [(true, true)], 196⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge195Inv : Holds level0Subgroup PresentedGroup.of representative ⟨196, [(true, false)], 148⟩ :=
  holds_reverse edge195

theorem edge196 : Holds level0Subgroup PresentedGroup.of representative ⟨148, [(true, false)], 197⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge196Inv : Holds level0Subgroup PresentedGroup.of representative ⟨197, [(true, true)], 148⟩ :=
  holds_reverse edge196

theorem edge197 : Holds level0Subgroup PresentedGroup.of representative ⟨149, [(true, true)], 198⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge197Inv : Holds level0Subgroup PresentedGroup.of representative ⟨198, [(true, false)], 149⟩ :=
  holds_reverse edge197

theorem edge198 : Holds level0Subgroup PresentedGroup.of representative ⟨149, [(true, false)], 199⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge198Inv : Holds level0Subgroup PresentedGroup.of representative ⟨199, [(true, true)], 149⟩ :=
  holds_reverse edge198

theorem edge199 : Holds level0Subgroup PresentedGroup.of representative ⟨150, [(true, true)], 200⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge199Inv : Holds level0Subgroup PresentedGroup.of representative ⟨200, [(true, false)], 150⟩ :=
  holds_reverse edge199

theorem edge200 : Holds level0Subgroup PresentedGroup.of representative ⟨150, [(true, false)], 201⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge200Inv : Holds level0Subgroup PresentedGroup.of representative ⟨201, [(true, true)], 150⟩ :=
  holds_reverse edge200

theorem edge201 : Holds level0Subgroup PresentedGroup.of representative ⟨151, [(true, true)], 202⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge201Inv : Holds level0Subgroup PresentedGroup.of representative ⟨202, [(true, false)], 151⟩ :=
  holds_reverse edge201

theorem edge202 : Holds level0Subgroup PresentedGroup.of representative ⟨151, [(true, false)], 203⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge202Inv : Holds level0Subgroup PresentedGroup.of representative ⟨203, [(true, true)], 151⟩ :=
  holds_reverse edge202

theorem edge203 : Holds level0Subgroup PresentedGroup.of representative ⟨152, [(true, false)], 204⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge203Inv : Holds level0Subgroup PresentedGroup.of representative ⟨204, [(true, true)], 152⟩ :=
  holds_reverse edge203

theorem edge204 : Holds level0Subgroup PresentedGroup.of representative ⟨153, [(true, true)], 205⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge204Inv : Holds level0Subgroup PresentedGroup.of representative ⟨205, [(true, false)], 153⟩ :=
  holds_reverse edge204

theorem edge205 : Holds level0Subgroup PresentedGroup.of representative ⟨153, [(true, false)], 206⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge205Inv : Holds level0Subgroup PresentedGroup.of representative ⟨206, [(true, true)], 153⟩ :=
  holds_reverse edge205

theorem edge206 : Holds level0Subgroup PresentedGroup.of representative ⟨154, [(true, true)], 207⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge206Inv : Holds level0Subgroup PresentedGroup.of representative ⟨207, [(true, false)], 154⟩ :=
  holds_reverse edge206

theorem edge207 : Holds level0Subgroup PresentedGroup.of representative ⟨154, [(true, false)], 208⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge207Inv : Holds level0Subgroup PresentedGroup.of representative ⟨208, [(true, true)], 154⟩ :=
  holds_reverse edge207

theorem edge208 : Holds level0Subgroup PresentedGroup.of representative ⟨155, [(true, true)], 209⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge208Inv : Holds level0Subgroup PresentedGroup.of representative ⟨209, [(true, false)], 155⟩ :=
  holds_reverse edge208

theorem edge209 : Holds level0Subgroup PresentedGroup.of representative ⟨155, [(true, false)], 210⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge209Inv : Holds level0Subgroup PresentedGroup.of representative ⟨210, [(true, true)], 155⟩ :=
  holds_reverse edge209

theorem edge210 : Holds level0Subgroup PresentedGroup.of representative ⟨156, [(true, true)], 211⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge210Inv : Holds level0Subgroup PresentedGroup.of representative ⟨211, [(true, false)], 156⟩ :=
  holds_reverse edge210

theorem edge211 : Holds level0Subgroup PresentedGroup.of representative ⟨156, [(true, false)], 212⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge211Inv : Holds level0Subgroup PresentedGroup.of representative ⟨212, [(true, true)], 156⟩ :=
  holds_reverse edge211

theorem edge212 : Holds level0Subgroup PresentedGroup.of representative ⟨157, [(true, true)], 213⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge212Inv : Holds level0Subgroup PresentedGroup.of representative ⟨213, [(true, false)], 157⟩ :=
  holds_reverse edge212

theorem edge213 : Holds level0Subgroup PresentedGroup.of representative ⟨157, [(true, false)], 214⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge213Inv : Holds level0Subgroup PresentedGroup.of representative ⟨214, [(true, true)], 157⟩ :=
  holds_reverse edge213

theorem edge214 : Holds level0Subgroup PresentedGroup.of representative ⟨158, [(true, true)], 215⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge214Inv : Holds level0Subgroup PresentedGroup.of representative ⟨215, [(true, false)], 158⟩ :=
  holds_reverse edge214

theorem edge215 : Holds level0Subgroup PresentedGroup.of representative ⟨158, [(true, false)], 216⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge215Inv : Holds level0Subgroup PresentedGroup.of representative ⟨216, [(true, true)], 158⟩ :=
  holds_reverse edge215

theorem edge216 : Holds level0Subgroup PresentedGroup.of representative ⟨159, [(true, true)], 217⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge216Inv : Holds level0Subgroup PresentedGroup.of representative ⟨217, [(true, false)], 159⟩ :=
  holds_reverse edge216

theorem edge217 : Holds level0Subgroup PresentedGroup.of representative ⟨159, [(true, false)], 218⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge217Inv : Holds level0Subgroup PresentedGroup.of representative ⟨218, [(true, true)], 159⟩ :=
  holds_reverse edge217

theorem edge218 : Holds level0Subgroup PresentedGroup.of representative ⟨160, [(true, true)], 219⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge218Inv : Holds level0Subgroup PresentedGroup.of representative ⟨219, [(true, false)], 160⟩ :=
  holds_reverse edge218

theorem edge219 : Holds level0Subgroup PresentedGroup.of representative ⟨160, [(true, false)], 220⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge219Inv : Holds level0Subgroup PresentedGroup.of representative ⟨220, [(true, true)], 160⟩ :=
  holds_reverse edge219

theorem edge220 : Holds level0Subgroup PresentedGroup.of representative ⟨161, [(true, true)], 221⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge220Inv : Holds level0Subgroup PresentedGroup.of representative ⟨221, [(true, false)], 161⟩ :=
  holds_reverse edge220

theorem edge221 : Holds level0Subgroup PresentedGroup.of representative ⟨161, [(true, false)], 222⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge221Inv : Holds level0Subgroup PresentedGroup.of representative ⟨222, [(true, true)], 161⟩ :=
  holds_reverse edge221

theorem edge222 : Holds level0Subgroup PresentedGroup.of representative ⟨162, [(true, true)], 223⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge222Inv : Holds level0Subgroup PresentedGroup.of representative ⟨223, [(true, false)], 162⟩ :=
  holds_reverse edge222

theorem edge223 : Holds level0Subgroup PresentedGroup.of representative ⟨162, [(true, false)], 224⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge223Inv : Holds level0Subgroup PresentedGroup.of representative ⟨224, [(true, true)], 162⟩ :=
  holds_reverse edge223

theorem edge224 : Holds level0Subgroup PresentedGroup.of representative ⟨163, [(true, true)], 225⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge224Inv : Holds level0Subgroup PresentedGroup.of representative ⟨225, [(true, false)], 163⟩ :=
  holds_reverse edge224

theorem edge225 : Holds level0Subgroup PresentedGroup.of representative ⟨163, [(true, false)], 226⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge225Inv : Holds level0Subgroup PresentedGroup.of representative ⟨226, [(true, true)], 163⟩ :=
  holds_reverse edge225

theorem edge226 : Holds level0Subgroup PresentedGroup.of representative ⟨164, [(true, true)], 227⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge226Inv : Holds level0Subgroup PresentedGroup.of representative ⟨227, [(true, false)], 164⟩ :=
  holds_reverse edge226

theorem edge227 : Holds level0Subgroup PresentedGroup.of representative ⟨164, [(true, false)], 228⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge227Inv : Holds level0Subgroup PresentedGroup.of representative ⟨228, [(true, true)], 164⟩ :=
  holds_reverse edge227

theorem edge228 : Holds level0Subgroup PresentedGroup.of representative ⟨165, [(true, true)], 229⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge228Inv : Holds level0Subgroup PresentedGroup.of representative ⟨229, [(true, false)], 165⟩ :=
  holds_reverse edge228

theorem edge229 : Holds level0Subgroup PresentedGroup.of representative ⟨165, [(true, false)], 230⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge229Inv : Holds level0Subgroup PresentedGroup.of representative ⟨230, [(true, true)], 165⟩ :=
  holds_reverse edge229

theorem edge230 : Holds level0Subgroup PresentedGroup.of representative ⟨166, [(true, true)], 231⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge230Inv : Holds level0Subgroup PresentedGroup.of representative ⟨231, [(true, false)], 166⟩ :=
  holds_reverse edge230

theorem edge231 : Holds level0Subgroup PresentedGroup.of representative ⟨166, [(true, false)], 232⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge231Inv : Holds level0Subgroup PresentedGroup.of representative ⟨232, [(true, true)], 166⟩ :=
  holds_reverse edge231

theorem edge232 : Holds level0Subgroup PresentedGroup.of representative ⟨167, [(true, true)], 233⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge232Inv : Holds level0Subgroup PresentedGroup.of representative ⟨233, [(true, false)], 167⟩ :=
  holds_reverse edge232

theorem edge233 : Holds level0Subgroup PresentedGroup.of representative ⟨167, [(true, false)], 234⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge233Inv : Holds level0Subgroup PresentedGroup.of representative ⟨234, [(true, true)], 167⟩ :=
  holds_reverse edge233

theorem edge234 : Holds level0Subgroup PresentedGroup.of representative ⟨168, [(true, true)], 235⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge234Inv : Holds level0Subgroup PresentedGroup.of representative ⟨235, [(true, false)], 168⟩ :=
  holds_reverse edge234

theorem edge235 : Holds level0Subgroup PresentedGroup.of representative ⟨168, [(true, false)], 236⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge235Inv : Holds level0Subgroup PresentedGroup.of representative ⟨236, [(true, true)], 168⟩ :=
  holds_reverse edge235

theorem edge236 : Holds level0Subgroup PresentedGroup.of representative ⟨170, [(true, true)], 237⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge236Inv : Holds level0Subgroup PresentedGroup.of representative ⟨237, [(true, false)], 170⟩ :=
  holds_reverse edge236

theorem edge237 : Holds level0Subgroup PresentedGroup.of representative ⟨170, [(true, false)], 238⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge237Inv : Holds level0Subgroup PresentedGroup.of representative ⟨238, [(true, true)], 170⟩ :=
  holds_reverse edge237

theorem edge238 : Holds level0Subgroup PresentedGroup.of representative ⟨171, [(true, true)], 239⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge238Inv : Holds level0Subgroup PresentedGroup.of representative ⟨239, [(true, false)], 171⟩ :=
  holds_reverse edge238

theorem edge239 : Holds level0Subgroup PresentedGroup.of representative ⟨171, [(true, false)], 240⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge239Inv : Holds level0Subgroup PresentedGroup.of representative ⟨240, [(true, true)], 171⟩ :=
  holds_reverse edge239

theorem edge240 : Holds level0Subgroup PresentedGroup.of representative ⟨172, [(true, true)], 241⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge240Inv : Holds level0Subgroup PresentedGroup.of representative ⟨241, [(true, false)], 172⟩ :=
  holds_reverse edge240

theorem edge241 : Holds level0Subgroup PresentedGroup.of representative ⟨172, [(true, false)], 242⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge241Inv : Holds level0Subgroup PresentedGroup.of representative ⟨242, [(true, true)], 172⟩ :=
  holds_reverse edge241

theorem edge242 : Holds level0Subgroup PresentedGroup.of representative ⟨173, [(true, true)], 243⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge242Inv : Holds level0Subgroup PresentedGroup.of representative ⟨243, [(true, false)], 173⟩ :=
  holds_reverse edge242

theorem edge243 : Holds level0Subgroup PresentedGroup.of representative ⟨173, [(true, false)], 244⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge243Inv : Holds level0Subgroup PresentedGroup.of representative ⟨244, [(true, true)], 173⟩ :=
  holds_reverse edge243

theorem edge244 : Holds level0Subgroup PresentedGroup.of representative ⟨174, [(true, true)], 245⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge244Inv : Holds level0Subgroup PresentedGroup.of representative ⟨245, [(true, false)], 174⟩ :=
  holds_reverse edge244

theorem edge245 : Holds level0Subgroup PresentedGroup.of representative ⟨174, [(true, false)], 246⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge245Inv : Holds level0Subgroup PresentedGroup.of representative ⟨246, [(true, true)], 174⟩ :=
  holds_reverse edge245

theorem edge246 : Holds level0Subgroup PresentedGroup.of representative ⟨175, [(true, true)], 247⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge246Inv : Holds level0Subgroup PresentedGroup.of representative ⟨247, [(true, false)], 175⟩ :=
  holds_reverse edge246

theorem edge247 : Holds level0Subgroup PresentedGroup.of representative ⟨175, [(true, false)], 248⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge247Inv : Holds level0Subgroup PresentedGroup.of representative ⟨248, [(true, true)], 175⟩ :=
  holds_reverse edge247

theorem edge248 : Holds level0Subgroup PresentedGroup.of representative ⟨176, [(true, true)], 249⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge248Inv : Holds level0Subgroup PresentedGroup.of representative ⟨249, [(true, false)], 176⟩ :=
  holds_reverse edge248

theorem edge249 : Holds level0Subgroup PresentedGroup.of representative ⟨176, [(true, false)], 250⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge249Inv : Holds level0Subgroup PresentedGroup.of representative ⟨250, [(true, true)], 176⟩ :=
  holds_reverse edge249

theorem edge250 : Holds level0Subgroup PresentedGroup.of representative ⟨177, [(true, true)], 251⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge250Inv : Holds level0Subgroup PresentedGroup.of representative ⟨251, [(true, false)], 177⟩ :=
  holds_reverse edge250

theorem edge251 : Holds level0Subgroup PresentedGroup.of representative ⟨177, [(true, false)], 252⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge251Inv : Holds level0Subgroup PresentedGroup.of representative ⟨252, [(true, true)], 177⟩ :=
  holds_reverse edge251

theorem edge252 : Holds level0Subgroup PresentedGroup.of representative ⟨178, [(true, true)], 253⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge252Inv : Holds level0Subgroup PresentedGroup.of representative ⟨253, [(true, false)], 178⟩ :=
  holds_reverse edge252

theorem edge253 : Holds level0Subgroup PresentedGroup.of representative ⟨178, [(true, false)], 254⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge253Inv : Holds level0Subgroup PresentedGroup.of representative ⟨254, [(true, true)], 178⟩ :=
  holds_reverse edge253

theorem edge254 : Holds level0Subgroup PresentedGroup.of representative ⟨179, [(true, true)], 255⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge254Inv : Holds level0Subgroup PresentedGroup.of representative ⟨255, [(true, false)], 179⟩ :=
  holds_reverse edge254

theorem edge255 : Holds level0Subgroup PresentedGroup.of representative ⟨179, [(true, false)], 256⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge255Inv : Holds level0Subgroup PresentedGroup.of representative ⟨256, [(true, true)], 179⟩ :=
  holds_reverse edge255


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
