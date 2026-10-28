module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges03

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

theorem edge256 : Holds level0Subgroup PresentedGroup.of representative ⟨180, [(true, true)], 257⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge256Inv : Holds level0Subgroup PresentedGroup.of representative ⟨257, [(true, false)], 180⟩ :=
  holds_reverse edge256

theorem edge257 : Holds level0Subgroup PresentedGroup.of representative ⟨180, [(true, false)], 258⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge257Inv : Holds level0Subgroup PresentedGroup.of representative ⟨258, [(true, true)], 180⟩ :=
  holds_reverse edge257

theorem edge258 : Holds level0Subgroup PresentedGroup.of representative ⟨181, [(true, true)], 259⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge258Inv : Holds level0Subgroup PresentedGroup.of representative ⟨259, [(true, false)], 181⟩ :=
  holds_reverse edge258

theorem edge259 : Holds level0Subgroup PresentedGroup.of representative ⟨181, [(true, false)], 260⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge259Inv : Holds level0Subgroup PresentedGroup.of representative ⟨260, [(true, true)], 181⟩ :=
  holds_reverse edge259

theorem edge260 : Holds level0Subgroup PresentedGroup.of representative ⟨182, [(true, true)], 261⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, true)]).symm

theorem edge260Inv : Holds level0Subgroup PresentedGroup.of representative ⟨261, [(true, false)], 182⟩ :=
  holds_reverse edge260

theorem edge261 : Holds level0Subgroup PresentedGroup.of representative ⟨182, [(true, false)], 262⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)] [(true, false)]).symm

theorem edge261Inv : Holds level0Subgroup PresentedGroup.of representative ⟨262, [(true, true)], 182⟩ :=
  holds_reverse edge261

theorem edge262 : Holds level0Subgroup PresentedGroup.of representative ⟨183, [(true, true)], 263⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, true)]).symm

theorem edge262Inv : Holds level0Subgroup PresentedGroup.of representative ⟨263, [(true, false)], 183⟩ :=
  holds_reverse edge262

theorem edge263 : Holds level0Subgroup PresentedGroup.of representative ⟨183, [(true, false)], 264⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)] [(true, false)]).symm

theorem edge263Inv : Holds level0Subgroup PresentedGroup.of representative ⟨264, [(true, true)], 183⟩ :=
  holds_reverse edge263

theorem edge264 : Holds level0Subgroup PresentedGroup.of representative ⟨184, [(false, true)], 265⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge264Inv : Holds level0Subgroup PresentedGroup.of representative ⟨265, [(false, false)], 184⟩ :=
  holds_reverse edge264

theorem edge265 : Holds level0Subgroup PresentedGroup.of representative ⟨185, [(false, true)], 266⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge265Inv : Holds level0Subgroup PresentedGroup.of representative ⟨266, [(false, false)], 185⟩ :=
  holds_reverse edge265

theorem edge266 : Holds level0Subgroup PresentedGroup.of representative ⟨186, [(false, true)], 267⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge266Inv : Holds level0Subgroup PresentedGroup.of representative ⟨267, [(false, false)], 186⟩ :=
  holds_reverse edge266

theorem edge267 : Holds level0Subgroup PresentedGroup.of representative ⟨187, [(false, true)], 268⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge267Inv : Holds level0Subgroup PresentedGroup.of representative ⟨268, [(false, false)], 187⟩ :=
  holds_reverse edge267

theorem edge268 : Holds level0Subgroup PresentedGroup.of representative ⟨188, [(false, true)], 269⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge268Inv : Holds level0Subgroup PresentedGroup.of representative ⟨269, [(false, false)], 188⟩ :=
  holds_reverse edge268

theorem edge269 : Holds level0Subgroup PresentedGroup.of representative ⟨189, [(false, true)], 270⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge269Inv : Holds level0Subgroup PresentedGroup.of representative ⟨270, [(false, false)], 189⟩ :=
  holds_reverse edge269

theorem edge270 : Holds level0Subgroup PresentedGroup.of representative ⟨190, [(false, true)], 271⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge270Inv : Holds level0Subgroup PresentedGroup.of representative ⟨271, [(false, false)], 190⟩ :=
  holds_reverse edge270

theorem edge271 : Holds level0Subgroup PresentedGroup.of representative ⟨191, [(false, true)], 272⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge271Inv : Holds level0Subgroup PresentedGroup.of representative ⟨272, [(false, false)], 191⟩ :=
  holds_reverse edge271

theorem edge272 : Holds level0Subgroup PresentedGroup.of representative ⟨192, [(false, true)], 273⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge272Inv : Holds level0Subgroup PresentedGroup.of representative ⟨273, [(false, false)], 192⟩ :=
  holds_reverse edge272

theorem edge273 : Holds level0Subgroup PresentedGroup.of representative ⟨193, [(false, true)], 274⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge273Inv : Holds level0Subgroup PresentedGroup.of representative ⟨274, [(false, false)], 193⟩ :=
  holds_reverse edge273

theorem edge274 : Holds level0Subgroup PresentedGroup.of representative ⟨194, [(false, true)], 275⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge274Inv : Holds level0Subgroup PresentedGroup.of representative ⟨275, [(false, false)], 194⟩ :=
  holds_reverse edge274

theorem edge275 : Holds level0Subgroup PresentedGroup.of representative ⟨195, [(false, true)], 276⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge275Inv : Holds level0Subgroup PresentedGroup.of representative ⟨276, [(false, false)], 195⟩ :=
  holds_reverse edge275

theorem edge276 : Holds level0Subgroup PresentedGroup.of representative ⟨196, [(false, true)], 277⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge276Inv : Holds level0Subgroup PresentedGroup.of representative ⟨277, [(false, false)], 196⟩ :=
  holds_reverse edge276

theorem edge277 : Holds level0Subgroup PresentedGroup.of representative ⟨197, [(false, true)], 278⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge277Inv : Holds level0Subgroup PresentedGroup.of representative ⟨278, [(false, false)], 197⟩ :=
  holds_reverse edge277

theorem edge278 : Holds level0Subgroup PresentedGroup.of representative ⟨198, [(false, true)], 279⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge278Inv : Holds level0Subgroup PresentedGroup.of representative ⟨279, [(false, false)], 198⟩ :=
  holds_reverse edge278

theorem edge279 : Holds level0Subgroup PresentedGroup.of representative ⟨199, [(false, true)], 280⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge279Inv : Holds level0Subgroup PresentedGroup.of representative ⟨280, [(false, false)], 199⟩ :=
  holds_reverse edge279

theorem edge280 : Holds level0Subgroup PresentedGroup.of representative ⟨200, [(false, true)], 281⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge280Inv : Holds level0Subgroup PresentedGroup.of representative ⟨281, [(false, false)], 200⟩ :=
  holds_reverse edge280

theorem edge281 : Holds level0Subgroup PresentedGroup.of representative ⟨201, [(false, true)], 282⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge281Inv : Holds level0Subgroup PresentedGroup.of representative ⟨282, [(false, false)], 201⟩ :=
  holds_reverse edge281

theorem edge282 : Holds level0Subgroup PresentedGroup.of representative ⟨202, [(false, true)], 283⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge282Inv : Holds level0Subgroup PresentedGroup.of representative ⟨283, [(false, false)], 202⟩ :=
  holds_reverse edge282

theorem edge283 : Holds level0Subgroup PresentedGroup.of representative ⟨203, [(false, true)], 284⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge283Inv : Holds level0Subgroup PresentedGroup.of representative ⟨284, [(false, false)], 203⟩ :=
  holds_reverse edge283

theorem edge284 : Holds level0Subgroup PresentedGroup.of representative ⟨204, [(false, true)], 285⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge284Inv : Holds level0Subgroup PresentedGroup.of representative ⟨285, [(false, false)], 204⟩ :=
  holds_reverse edge284

theorem edge285 : Holds level0Subgroup PresentedGroup.of representative ⟨205, [(false, true)], 286⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge285Inv : Holds level0Subgroup PresentedGroup.of representative ⟨286, [(false, false)], 205⟩ :=
  holds_reverse edge285

theorem edge286 : Holds level0Subgroup PresentedGroup.of representative ⟨206, [(false, true)], 287⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge286Inv : Holds level0Subgroup PresentedGroup.of representative ⟨287, [(false, false)], 206⟩ :=
  holds_reverse edge286

theorem edge287 : Holds level0Subgroup PresentedGroup.of representative ⟨207, [(false, true)], 288⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge287Inv : Holds level0Subgroup PresentedGroup.of representative ⟨288, [(false, false)], 207⟩ :=
  holds_reverse edge287

theorem edge288 : Holds level0Subgroup PresentedGroup.of representative ⟨208, [(false, true)], 289⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge288Inv : Holds level0Subgroup PresentedGroup.of representative ⟨289, [(false, false)], 208⟩ :=
  holds_reverse edge288

theorem edge289 : Holds level0Subgroup PresentedGroup.of representative ⟨210, [(false, true)], 290⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge289Inv : Holds level0Subgroup PresentedGroup.of representative ⟨290, [(false, false)], 210⟩ :=
  holds_reverse edge289

theorem edge290 : Holds level0Subgroup PresentedGroup.of representative ⟨211, [(false, true)], 291⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge290Inv : Holds level0Subgroup PresentedGroup.of representative ⟨291, [(false, false)], 211⟩ :=
  holds_reverse edge290

theorem edge291 : Holds level0Subgroup PresentedGroup.of representative ⟨212, [(false, true)], 292⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge291Inv : Holds level0Subgroup PresentedGroup.of representative ⟨292, [(false, false)], 212⟩ :=
  holds_reverse edge291

theorem edge292 : Holds level0Subgroup PresentedGroup.of representative ⟨213, [(false, true)], 293⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge292Inv : Holds level0Subgroup PresentedGroup.of representative ⟨293, [(false, false)], 213⟩ :=
  holds_reverse edge292

theorem edge293 : Holds level0Subgroup PresentedGroup.of representative ⟨214, [(false, true)], 294⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge293Inv : Holds level0Subgroup PresentedGroup.of representative ⟨294, [(false, false)], 214⟩ :=
  holds_reverse edge293

theorem edge294 : Holds level0Subgroup PresentedGroup.of representative ⟨215, [(false, true)], 295⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge294Inv : Holds level0Subgroup PresentedGroup.of representative ⟨295, [(false, false)], 215⟩ :=
  holds_reverse edge294

theorem edge295 : Holds level0Subgroup PresentedGroup.of representative ⟨216, [(false, true)], 296⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge295Inv : Holds level0Subgroup PresentedGroup.of representative ⟨296, [(false, false)], 216⟩ :=
  holds_reverse edge295

theorem edge296 : Holds level0Subgroup PresentedGroup.of representative ⟨217, [(false, true)], 297⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge296Inv : Holds level0Subgroup PresentedGroup.of representative ⟨297, [(false, false)], 217⟩ :=
  holds_reverse edge296

theorem edge297 : Holds level0Subgroup PresentedGroup.of representative ⟨218, [(false, true)], 298⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge297Inv : Holds level0Subgroup PresentedGroup.of representative ⟨298, [(false, false)], 218⟩ :=
  holds_reverse edge297

theorem edge298 : Holds level0Subgroup PresentedGroup.of representative ⟨219, [(false, true)], 299⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge298Inv : Holds level0Subgroup PresentedGroup.of representative ⟨299, [(false, false)], 219⟩ :=
  holds_reverse edge298

theorem edge299 : Holds level0Subgroup PresentedGroup.of representative ⟨220, [(false, true)], 300⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge299Inv : Holds level0Subgroup PresentedGroup.of representative ⟨300, [(false, false)], 220⟩ :=
  holds_reverse edge299

theorem edge300 : Holds level0Subgroup PresentedGroup.of representative ⟨224, [(false, true)], 301⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge300Inv : Holds level0Subgroup PresentedGroup.of representative ⟨301, [(false, false)], 224⟩ :=
  holds_reverse edge300

theorem edge301 : Holds level0Subgroup PresentedGroup.of representative ⟨225, [(false, true)], 302⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge301Inv : Holds level0Subgroup PresentedGroup.of representative ⟨302, [(false, false)], 225⟩ :=
  holds_reverse edge301

theorem edge302 : Holds level0Subgroup PresentedGroup.of representative ⟨226, [(false, true)], 303⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge302Inv : Holds level0Subgroup PresentedGroup.of representative ⟨303, [(false, false)], 226⟩ :=
  holds_reverse edge302

theorem edge303 : Holds level0Subgroup PresentedGroup.of representative ⟨227, [(false, true)], 304⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge303Inv : Holds level0Subgroup PresentedGroup.of representative ⟨304, [(false, false)], 227⟩ :=
  holds_reverse edge303

theorem edge304 : Holds level0Subgroup PresentedGroup.of representative ⟨228, [(false, true)], 305⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge304Inv : Holds level0Subgroup PresentedGroup.of representative ⟨305, [(false, false)], 228⟩ :=
  holds_reverse edge304

theorem edge305 : Holds level0Subgroup PresentedGroup.of representative ⟨229, [(false, true)], 306⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge305Inv : Holds level0Subgroup PresentedGroup.of representative ⟨306, [(false, false)], 229⟩ :=
  holds_reverse edge305

theorem edge306 : Holds level0Subgroup PresentedGroup.of representative ⟨230, [(false, true)], 307⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge306Inv : Holds level0Subgroup PresentedGroup.of representative ⟨307, [(false, false)], 230⟩ :=
  holds_reverse edge306

theorem edge307 : Holds level0Subgroup PresentedGroup.of representative ⟨231, [(false, true)], 308⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge307Inv : Holds level0Subgroup PresentedGroup.of representative ⟨308, [(false, false)], 231⟩ :=
  holds_reverse edge307

theorem edge308 : Holds level0Subgroup PresentedGroup.of representative ⟨232, [(false, true)], 309⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge308Inv : Holds level0Subgroup PresentedGroup.of representative ⟨309, [(false, false)], 232⟩ :=
  holds_reverse edge308

theorem edge309 : Holds level0Subgroup PresentedGroup.of representative ⟨233, [(false, true)], 310⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge309Inv : Holds level0Subgroup PresentedGroup.of representative ⟨310, [(false, false)], 233⟩ :=
  holds_reverse edge309

theorem edge310 : Holds level0Subgroup PresentedGroup.of representative ⟨235, [(false, true)], 311⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge310Inv : Holds level0Subgroup PresentedGroup.of representative ⟨311, [(false, false)], 235⟩ :=
  holds_reverse edge310

theorem edge311 : Holds level0Subgroup PresentedGroup.of representative ⟨236, [(false, true)], 312⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge311Inv : Holds level0Subgroup PresentedGroup.of representative ⟨312, [(false, false)], 236⟩ :=
  holds_reverse edge311

theorem edge312 : Holds level0Subgroup PresentedGroup.of representative ⟨237, [(false, true)], 313⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge312Inv : Holds level0Subgroup PresentedGroup.of representative ⟨313, [(false, false)], 237⟩ :=
  holds_reverse edge312

theorem edge313 : Holds level0Subgroup PresentedGroup.of representative ⟨238, [(false, true)], 314⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)] [(false, true)]).symm

theorem edge313Inv : Holds level0Subgroup PresentedGroup.of representative ⟨314, [(false, false)], 238⟩ :=
  holds_reverse edge313

theorem edge314 : Holds level0Subgroup PresentedGroup.of representative ⟨239, [(false, true)], 315⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge314Inv : Holds level0Subgroup PresentedGroup.of representative ⟨315, [(false, false)], 239⟩ :=
  holds_reverse edge314

theorem edge315 : Holds level0Subgroup PresentedGroup.of representative ⟨240, [(false, true)], 316⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge315Inv : Holds level0Subgroup PresentedGroup.of representative ⟨316, [(false, false)], 240⟩ :=
  holds_reverse edge315

theorem edge316 : Holds level0Subgroup PresentedGroup.of representative ⟨241, [(false, true)], 317⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge316Inv : Holds level0Subgroup PresentedGroup.of representative ⟨317, [(false, false)], 241⟩ :=
  holds_reverse edge316

theorem edge317 : Holds level0Subgroup PresentedGroup.of representative ⟨243, [(false, true)], 318⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)] [(false, true)]).symm

theorem edge317Inv : Holds level0Subgroup PresentedGroup.of representative ⟨318, [(false, false)], 243⟩ :=
  holds_reverse edge317

theorem edge318 : Holds level0Subgroup PresentedGroup.of representative ⟨244, [(false, true)], 319⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false)] [(false, true)]).symm

theorem edge318Inv : Holds level0Subgroup PresentedGroup.of representative ⟨319, [(false, false)], 244⟩ :=
  holds_reverse edge318

theorem edge319 : Holds level0Subgroup PresentedGroup.of representative ⟨245, [(false, true)], 320⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)] [(false, true)]).symm

theorem edge319Inv : Holds level0Subgroup PresentedGroup.of representative ⟨320, [(false, false)], 245⟩ :=
  holds_reverse edge319


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
