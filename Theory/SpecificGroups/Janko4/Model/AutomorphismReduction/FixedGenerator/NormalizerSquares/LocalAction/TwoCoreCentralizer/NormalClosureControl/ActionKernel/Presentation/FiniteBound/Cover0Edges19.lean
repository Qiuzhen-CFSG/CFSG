module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges18

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

theorem edge1216 : Holds level0Subgroup PresentedGroup.of representative ⟨433, [(false, true)], 386⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨207, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 433⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge287 edge375) (appendFacts edge1057 (appendFacts edge446Inv edge960))) (appendFacts (appendFacts edge258Inv edge843) (appendFacts edge138Inv (appendFacts edge780 edge73Inv)))) (appendFacts (appendFacts (appendFacts edge747 edge735Inv) (appendFacts edge49 (appendFacts edge71 edge93))) (appendFacts (appendFacts edge134 edge176) (appendFacts edge251 (appendFacts edge325 edge432)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨386, [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 207⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge385Inv edge917) (appendFacts edge212Inv (appendFacts edge819 edge114Inv))) (appendFacts (appendFacts edge768 edge60Inv) (appendFacts edge740 (appendFacts edge31Inv edge726)))) (appendFacts (appendFacts (appendFacts edge16Inv edge716) (appendFacts edge6Inv (appendFacts edge711 edge710))) (appendFacts (appendFacts edge4 (appendFacts edge7 edge11)) (appendFacts edge17 (appendFacts edge24 edge33))))) (appendFacts (appendFacts (appendFacts (appendFacts edge45 edge64) (appendFacts edge695 (appendFacts edge64Inv edge742))) (appendFacts (appendFacts edge33Inv (appendFacts edge727 edge721)) (appendFacts edge25 (appendFacts edge36 edge48)))) (appendFacts (appendFacts (appendFacts edge69 edge91) (appendFacts edge129 (appendFacts edge171 edge241))) (appendFacts (appendFacts edge913 (appendFacts edge208Inv edge817)) (appendFacts edge789Inv (appendFacts edge153 edge206))))))
  exact scanFacts hp hs (holds_relator 207 (level0Relator 3) (level0_relator 3))

theorem edge1216Inv : Holds level0Subgroup PresentedGroup.of representative ⟨386, [(false, false)], 433⟩ :=
  holds_reverse edge1216

theorem edge1217 : Holds level0Subgroup PresentedGroup.of representative ⟨662, [(true, false)], 661⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨339, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)], 662⟩ :=
    (appendFacts (appendFacts (appendFacts edge451 edge531) (appendFacts edge1150 edge623Inv)) (appendFacts (appendFacts edge1107 edge1024Inv) (appendFacts edge529 (appendFacts edge620 edge661))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨661, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 339⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1189 (appendFacts edge618Inv edge1105)) (appendFacts edge448Inv (appendFacts edge962 edge260Inv))) (appendFacts (appendFacts edge844 (appendFacts edge139Inv edge781)) (appendFacts (appendFacts edge74Inv edge747) (appendFacts edge38Inv edge729)))) (appendFacts (appendFacts (appendFacts edge19Inv (appendFacts edge718 edge8Inv)) (appendFacts (appendFacts edge712 edge2Inv) (appendFacts edge709 edge692Inv))) (appendFacts (appendFacts edge0 (appendFacts edge1 edge3)) (appendFacts (appendFacts edge5 edge9) (appendFacts edge13 edge693))))) (appendFacts (appendFacts (appendFacts (appendFacts edge20Inv (appendFacts edge718 edge8Inv)) (appendFacts edge712 (appendFacts edge2Inv edge709))) (appendFacts (appendFacts edge692Inv (appendFacts edge0 edge1)) (appendFacts (appendFacts edge3 edge6) (appendFacts edge10 edge15)))) (appendFacts (appendFacts (appendFacts edge22 (appendFacts edge30 edge42)) (appendFacts (appendFacts edge57 edge80) (appendFacts edge107 edge150))) (appendFacts (appendFacts edge202 (appendFacts edge283 edge702Inv)) (appendFacts (appendFacts edge889 edge846Inv) (appendFacts edge264 edge338))))))
  exact scanFacts hp hs (holds_relator 339 (level0Relator 3) (level0_relator 3))

theorem edge1217Inv : Holds level0Subgroup PresentedGroup.of representative ⟨661, [(true, true)], 662⟩ :=
  holds_reverse edge1217

theorem edge1218 : Holds level0Subgroup PresentedGroup.of representative ⟨379, [(false, true)], 343⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨343, [(false, true)], 379⟩ :=
    edge1212
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨343, [], 343⟩ :=
    (holds_refl 343)
  exact scanFacts hp hs (holds_relator 343 (level0Relator 0) (level0_relator 0))

theorem edge1218Inv : Holds level0Subgroup PresentedGroup.of representative ⟨343, [(false, false)], 379⟩ :=
  holds_reverse edge1218

theorem edge1219 : Holds level0Subgroup PresentedGroup.of representative ⟨388, [(false, true)], 354⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨354, [(false, true)], 388⟩ :=
    edge1210
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨354, [], 354⟩ :=
    (holds_refl 354)
  exact scanFacts hp hs (holds_relator 354 (level0Relator 0) (level0_relator 0))

theorem edge1219Inv : Holds level0Subgroup PresentedGroup.of representative ⟨354, [(false, false)], 388⟩ :=
  holds_reverse edge1219

theorem edge1220 : Holds level0Subgroup PresentedGroup.of representative ⟨386, [(false, true)], 433⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨386, [], 386⟩ :=
    (holds_refl 386)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨433, [(false, true)], 386⟩ :=
    edge1216
  exact scanFacts hp hs (holds_relator 386 (level0Relator 0) (level0_relator 0))

theorem edge1220Inv : Holds level0Subgroup PresentedGroup.of representative ⟨433, [(false, false)], 386⟩ :=
  holds_reverse edge1220

theorem edge1221 : Holds level0Subgroup PresentedGroup.of representative ⟨437, [(false, true)], 423⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨423, [(false, true)], 437⟩ :=
    edge1213
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨423, [], 423⟩ :=
    (holds_refl 423)
  exact scanFacts hp hs (holds_relator 423 (level0Relator 0) (level0_relator 0))

theorem edge1221Inv : Holds level0Subgroup PresentedGroup.of representative ⟨423, [(false, false)], 437⟩ :=
  holds_reverse edge1221

theorem edge1222 : Holds level0Subgroup PresentedGroup.of representative ⟨602, [(false, true)], 611⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨437, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 602⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1221 edge422Inv) (appendFacts edge946 edge244Inv)) (appendFacts (appendFacts edge836 edge131Inv) (appendFacts edge777 edge757Inv))) (appendFacts (appendFacts (appendFacts edge91 edge130) (appendFacts edge172 edge243)) (appendFacts (appendFacts edge318 edge421) (appendFacts edge511 edge601))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨611, [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 437⟩ :=
    (appendFacts (appendFacts (appendFacts edge610Inv edge1098) (appendFacts edge437Inv (appendFacts edge956 edge254Inv))) (appendFacts (appendFacts edge841 (appendFacts edge801Inv edge177)) (appendFacts edge253 (appendFacts edge327 edge436))))
  exact scanFacts hp hs (holds_relator 437 (level0Relator 2) (level0_relator 2))

theorem edge1222Inv : Holds level0Subgroup PresentedGroup.of representative ⟨611, [(false, false)], 602⟩ :=
  holds_reverse edge1222

theorem edge1223 : Holds level0Subgroup PresentedGroup.of representative ⟨462, [(true, true)], 482⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨462, [], 462⟩ :=
    (holds_refl 462)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨482, [(true, true), (true, true)], 462⟩ :=
    (appendFacts edge1214Inv edge1208)
  exact scanFacts hp hs (holds_relator 462 (level0Relator 1) (level0_relator 1))

theorem edge1223Inv : Holds level0Subgroup PresentedGroup.of representative ⟨482, [(true, false)], 462⟩ :=
  holds_reverse edge1223

theorem edge1224 : Holds level0Subgroup PresentedGroup.of representative ⟨461, [(true, false)], 528⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨462, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)], 461⟩ :=
    (appendFacts (appendFacts (appendFacts edge1035 edge351Inv) (appendFacts edge896 (appendFacts edge191Inv edge808))) (appendFacts (appendFacts edge784Inv (appendFacts edge144 edge190)) (appendFacts edge271 (appendFacts edge350 edge460))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨528, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 462⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1104 edge447Inv) (appendFacts edge962 edge260Inv)) (appendFacts (appendFacts edge844 edge139Inv) (appendFacts edge781 edge759Inv))) (appendFacts (appendFacts (appendFacts edge95 edge138) (appendFacts edge180 edge259)) (appendFacts (appendFacts edge333 edge987Inv) (appendFacts edge481 edge1223Inv))))
  exact scanFacts hp hs (holds_relator 462 (level0Relator 2) (level0_relator 2))

theorem edge1224Inv : Holds level0Subgroup PresentedGroup.of representative ⟨528, [(true, true)], 461⟩ :=
  holds_reverse edge1224

theorem edge1225 : Holds level0Subgroup PresentedGroup.of representative ⟨492, [(true, true)], 545⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨465, [(true, true)], 492⟩ :=
    edge1205
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨545, [(true, true)], 465⟩ :=
    edge544Inv
  exact scanFacts hp hs (holds_relator 465 (level0Relator 1) (level0_relator 1))

theorem edge1225Inv : Holds level0Subgroup PresentedGroup.of representative ⟨545, [(true, false)], 492⟩ :=
  holds_reverse edge1225

theorem edge1226 : Holds level0Subgroup PresentedGroup.of representative ⟨551, [(true, true)], 508⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨470, [(true, true)], 551⟩ :=
    edge550
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨508, [(true, true)], 470⟩ :=
    edge1211Inv
  exact scanFacts hp hs (holds_relator 470 (level0Relator 1) (level0_relator 1))

theorem edge1226Inv : Holds level0Subgroup PresentedGroup.of representative ⟨508, [(true, false)], 551⟩ :=
  holds_reverse edge1226

theorem edge1227 : Holds level0Subgroup PresentedGroup.of representative ⟨507, [(true, true)], 552⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨471, [(true, true)], 507⟩ :=
    edge1207
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨552, [(true, true)], 471⟩ :=
    edge551Inv
  exact scanFacts hp hs (holds_relator 471 (level0Relator 1) (level0_relator 1))

theorem edge1227Inv : Holds level0Subgroup PresentedGroup.of representative ⟨552, [(true, false)], 507⟩ :=
  holds_reverse edge1227

theorem edge1228 : Holds level0Subgroup PresentedGroup.of representative ⟨514, [(true, true)], 572⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨485, [(true, true)], 514⟩ :=
    edge1206
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨572, [(true, true)], 485⟩ :=
    edge571Inv
  exact scanFacts hp hs (holds_relator 485 (level0Relator 1) (level0_relator 1))

theorem edge1228Inv : Holds level0Subgroup PresentedGroup.of representative ⟨572, [(true, false)], 514⟩ :=
  holds_reverse edge1228

theorem edge1229 : Holds level0Subgroup PresentedGroup.of representative ⟨536, [(false, true)], 553⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨507, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 536⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1083 (appendFacts edge413Inv edge940)) (appendFacts (appendFacts edge237Inv edge832) (appendFacts edge127Inv edge775))) (appendFacts (appendFacts edge68Inv (appendFacts edge744 edge35Inv)) (appendFacts (appendFacts edge728 edge721Inv) (appendFacts edge24 edge33)))) (appendFacts (appendFacts (appendFacts edge45 (appendFacts edge64 edge695)) (appendFacts (appendFacts edge754Inv edge86) (appendFacts edge119 edge161))) (appendFacts (appendFacts (appendFacts edge222 edge925) (appendFacts edge220Inv edge823)) (appendFacts (appendFacts edge118Inv edge770) (appendFacts edge62Inv edge741))))) (appendFacts (appendFacts (appendFacts (appendFacts edge732Inv (appendFacts edge43 edge59)) (appendFacts (appendFacts edge82 edge111) (appendFacts edge153 edge206))) (appendFacts (appendFacts edge287 (appendFacts edge375 edge1057)) (appendFacts (appendFacts edge446Inv edge960) (appendFacts edge885 edge333)))) (appendFacts (appendFacts (appendFacts edge987Inv (appendFacts edge481 edge1214Inv)) (appendFacts (appendFacts edge1041 edge978Inv) (appendFacts edge466 edge1052Inv))) (appendFacts (appendFacts (appendFacts edge1051 edge369Inv) (appendFacts edge906 edge855)) (appendFacts (appendFacts edge283 edge967) (appendFacts edge453 edge535))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨553, [(true, false), (false, true), (true, false), (false, true), (true, true)], 507⟩ :=
    (appendFacts (appendFacts edge552Inv edge1045) (appendFacts edge980Inv (appendFacts edge470 edge1207)))
  exact scanFacts hp hs (holds_relator 507 (level0Relator 3) (level0_relator 3))

theorem edge1229Inv : Holds level0Subgroup PresentedGroup.of representative ⟨553, [(false, false)], 536⟩ :=
  holds_reverse edge1229

theorem edge1230 : Holds level0Subgroup PresentedGroup.of representative ⟨543, [(true, true)], 528⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨528, [(true, true), (true, true)], 543⟩ :=
    (appendFacts edge1224Inv edge542)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨528, [], 528⟩ :=
    (holds_refl 528)
  exact scanFacts hp hs (holds_relator 528 (level0Relator 1) (level0_relator 1))

theorem edge1230Inv : Holds level0Subgroup PresentedGroup.of representative ⟨528, [(true, false)], 543⟩ :=
  holds_reverse edge1230

theorem edge1231 : Holds level0Subgroup PresentedGroup.of representative ⟨553, [(false, true)], 536⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨536, [(false, true)], 553⟩ :=
    edge1229
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨536, [], 536⟩ :=
    (holds_refl 536)
  exact scanFacts hp hs (holds_relator 536 (level0Relator 0) (level0_relator 0))

theorem edge1231Inv : Holds level0Subgroup PresentedGroup.of representative ⟨536, [(false, false)], 553⟩ :=
  holds_reverse edge1231

theorem edge1232 : Holds level0Subgroup PresentedGroup.of representative ⟨552, [(false, true)], 581⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨536, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 552⟩ :=
    (appendFacts (appendFacts edge1229 (appendFacts edge552Inv edge1045)) (appendFacts edge980Inv (appendFacts edge470 edge551)))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨581, [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 536⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1128Inv edge1209) (appendFacts edge536Inv (appendFacts edge1028 edge341Inv))) (appendFacts (appendFacts edge890 edge185Inv) (appendFacts edge805 (appendFacts edge99Inv edge761)))) (appendFacts (appendFacts (appendFacts edge748Inv edge75) (appendFacts edge98 (appendFacts edge696 edge782Inv))) (appendFacts (appendFacts edge141 (appendFacts edge184 edge265)) (appendFacts edge340 (appendFacts edge453 edge535)))))
  exact scanFacts hp hs (holds_relator 536 (level0Relator 2) (level0_relator 2))

theorem edge1232Inv : Holds level0Subgroup PresentedGroup.of representative ⟨581, [(false, false)], 552⟩ :=
  holds_reverse edge1232

theorem edge1233 : Holds level0Subgroup PresentedGroup.of representative ⟨537, [(false, true)], 580⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨537, [], 537⟩ :=
    (holds_refl 537)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨580, [(false, true)], 537⟩ :=
    edge1209
  exact scanFacts hp hs (holds_relator 537 (level0Relator 0) (level0_relator 0))

theorem edge1233Inv : Holds level0Subgroup PresentedGroup.of representative ⟨580, [(false, false)], 537⟩ :=
  holds_reverse edge1233

theorem edge1234 : Holds level0Subgroup PresentedGroup.of representative ⟨581, [(false, true)], 552⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨552, [(false, true)], 581⟩ :=
    edge1232
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨552, [], 552⟩ :=
    (holds_refl 552)
  exact scanFacts hp hs (holds_relator 552 (level0Relator 0) (level0_relator 0))

theorem edge1234Inv : Holds level0Subgroup PresentedGroup.of representative ⟨552, [(false, false)], 581⟩ :=
  holds_reverse edge1234

theorem edge1235 : Holds level0Subgroup PresentedGroup.of representative ⟨611, [(false, true)], 602⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨602, [(false, true)], 611⟩ :=
    edge1222
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨602, [], 602⟩ :=
    (holds_refl 602)
  exact scanFacts hp hs (holds_relator 602 (level0Relator 0) (level0_relator 0))

theorem edge1235Inv : Holds level0Subgroup PresentedGroup.of representative ⟨602, [(false, false)], 611⟩ :=
  holds_reverse edge1235

theorem edge1236 : Holds level0Subgroup PresentedGroup.of representative ⟨688, [(true, false)], 685⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨685, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)], 688⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1198 edge664Inv) (appendFacts edge1154 edge546Inv)) (appendFacts (appendFacts edge1039 edge357Inv) (appendFacts edge899 edge851Inv))) (appendFacts (appendFacts (appendFacts edge274 edge356) (appendFacts edge464 edge1205)) (appendFacts (appendFacts edge1067 edge997) (appendFacts edge492 (appendFacts edge579 edge1209))))) (appendFacts (appendFacts (appendFacts (appendFacts edge536Inv edge1028) (appendFacts edge968 edge951)) (appendFacts (appendFacts edge249Inv edge838) (appendFacts edge133Inv (appendFacts edge778 edge71Inv)))) (appendFacts (appendFacts (appendFacts edge746 edge37Inv) (appendFacts edge729 edge19Inv)) (appendFacts (appendFacts edge718 edge714Inv) (appendFacts edge11 (appendFacts edge17 edge24)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge33 edge45) (appendFacts edge64 edge695)) (appendFacts (appendFacts edge64Inv edge742) (appendFacts edge33Inv (appendFacts edge727 edge17Inv)))) (appendFacts (appendFacts (appendFacts edge717 edge7Inv) (appendFacts edge712 edge2Inv)) (appendFacts (appendFacts edge709 edge692) (appendFacts edge0 (appendFacts edge1 edge3))))) (appendFacts (appendFacts (appendFacts (appendFacts edge6 edge10) (appendFacts edge15 edge22)) (appendFacts (appendFacts edge30 edge42) (appendFacts edge58 (appendFacts edge81 edge109)))) (appendFacts (appendFacts (appendFacts edge152 edge204) (appendFacts edge285 edge372)) (appendFacts (appendFacts edge479 edge565) (appendFacts edge637 (appendFacts edge670 edge687)))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨685, [], 685⟩ :=
    (holds_refl 685)
  exact scanFacts hp hs (holds_relator 685 (level0Relator 4) (level0_relator 4))

theorem edge1236Inv : Holds level0Subgroup PresentedGroup.of representative ⟨685, [(true, true)], 688⟩ :=
  holds_reverse edge1236

theorem edge1237 : Holds level0Subgroup PresentedGroup.of representative ⟨658, [(true, true)], 643⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨9, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true)], 658⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge12 (appendFacts edge20 edge723)) (appendFacts edge719 (appendFacts edge21 edge28))) (appendFacts (appendFacts edge40 (appendFacts edge54 edge77)) (appendFacts edge102 (appendFacts edge145 edge191)))) (appendFacts (appendFacts (appendFacts edge272 (appendFacts edge351 edge461)) (appendFacts edge1223 (appendFacts edge1056 edge374Inv))) (appendFacts (appendFacts edge910 (appendFacts edge205Inv edge815)) (appendFacts (appendFacts edge788 edge697) (appendFacts edge788Inv edge152))))) (appendFacts (appendFacts (appendFacts (appendFacts edge205 (appendFacts edge286 edge708)) (appendFacts edge961 (appendFacts edge885Inv edge332))) (appendFacts (appendFacts edge446 (appendFacts edge989 edge988)) (appendFacts (appendFacts edge482 edge1215) (appendFacts edge1058 edge988Inv)))) (appendFacts (appendFacts (appendFacts edge1057 (appendFacts edge446Inv edge960)) (appendFacts edge258Inv (appendFacts edge843 edge802Inv))) (appendFacts (appendFacts edge179 (appendFacts edge257 edge331)) (appendFacts (appendFacts edge443 edge524) (appendFacts edge614 edge657))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨643, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 9⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1170 edge575Inv) (appendFacts edge1065 (appendFacts edge390Inv edge923))) (appendFacts (appendFacts edge218Inv edge822) (appendFacts edge117Inv (appendFacts edge770 edge62Inv)))) (appendFacts (appendFacts (appendFacts edge741 edge32Inv) (appendFacts edge726 (appendFacts edge16Inv edge716))) (appendFacts (appendFacts edge6Inv edge711) (appendFacts edge710 (appendFacts edge4 edge8)))))
  exact scanFacts hp hs (holds_relator 9 (level0Relator 4) (level0_relator 4))

theorem edge1237Inv : Holds level0Subgroup PresentedGroup.of representative ⟨643, [(true, false)], 658⟩ :=
  holds_reverse edge1237

theorem edge1238 : Holds level0Subgroup PresentedGroup.of representative ⟨665, [(true, true)], 634⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨14, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)], 665⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge693 edge20Inv) (appendFacts edge718 (appendFacts edge8Inv edge712))) (appendFacts (appendFacts edge710Inv (appendFacts edge3 edge5)) (appendFacts edge9 (appendFacts edge14 edge21)))) (appendFacts (appendFacts (appendFacts edge28 edge40) (appendFacts edge53 (appendFacts edge694 edge53Inv))) (appendFacts (appendFacts edge737 (appendFacts edge730Inv edge39)) (appendFacts edge51 (appendFacts edge75 edge97))))) (appendFacts (appendFacts (appendFacts (appendFacts edge141 edge184) (appendFacts edge265 (appendFacts edge702 edge907))) (appendFacts (appendFacts edge202Inv (appendFacts edge813 edge107Inv)) (appendFacts edge765 (appendFacts edge751 edge81)))) (appendFacts (appendFacts (appendFacts edge109 (appendFacts edge152 edge204)) (appendFacts edge285 (appendFacts edge372 edge479))) (appendFacts (appendFacts edge565 (appendFacts edge637 edge670)) (appendFacts edge687 (appendFacts edge1236 edge1198))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨634, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 14⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1161 edge558Inv) (appendFacts edge1048 edge366Inv)) (appendFacts (appendFacts edge904 edge199Inv) (appendFacts edge812 (appendFacts edge106Inv edge764)))) (appendFacts (appendFacts (appendFacts edge56Inv edge738) (appendFacts edge29Inv edge725)) (appendFacts (appendFacts edge15Inv edge716) (appendFacts edge713Inv (appendFacts edge9 edge13)))))
  exact scanFacts hp hs (holds_relator 14 (level0Relator 3) (level0_relator 3))

theorem edge1238Inv : Holds level0Subgroup PresentedGroup.of representative ⟨634, [(true, false)], 665⟩ :=
  holds_reverse edge1238

theorem edge1239 : Holds level0Subgroup PresentedGroup.of representative ⟨618, [(false, true)], 608⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨33, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 618⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge44 (appendFacts edge61 edge84)) (appendFacts (appendFacts edge115 edge157) (appendFacts edge215 edge295))) (appendFacts (appendFacts (appendFacts edge704Inv edge891) (appendFacts edge847Inv edge266)) (appendFacts (appendFacts edge703 edge951) (appendFacts edge249Inv edge838)))) (appendFacts (appendFacts (appendFacts edge133Inv (appendFacts edge778 edge71Inv)) (appendFacts (appendFacts edge746 edge735) (appendFacts edge50 edge73))) (appendFacts (appendFacts (appendFacts edge95 edge138) (appendFacts edge180 edge258)) (appendFacts (appendFacts edge332 edge445) (appendFacts edge526 edge617)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨608, [(true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 33⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge607Inv edge1094) (appendFacts edge429Inv edge950)) (appendFacts (appendFacts edge880 edge323) (appendFacts edge703Inv edge890))) (appendFacts (appendFacts (appendFacts edge847 edge267) (appendFacts edge342 edge1212)) (appendFacts (appendFacts edge378Inv edge914) (appendFacts edge209Inv edge817)))) (appendFacts (appendFacts (appendFacts (appendFacts edge789Inv edge153) (appendFacts edge206 edge287)) (appendFacts (appendFacts edge376 edge482) (appendFacts edge1215 edge1058))) (appendFacts (appendFacts (appendFacts edge376Inv edge911) (appendFacts edge206Inv edge816)) (appendFacts (appendFacts edge111Inv edge767) (appendFacts edge59Inv (appendFacts edge740 edge732))))))
  exact scanFacts hp hs (holds_relator 33 (level0Relator 3) (level0_relator 3))

theorem edge1239Inv : Holds level0Subgroup PresentedGroup.of representative ⟨608, [(false, false)], 618⟩ :=
  holds_reverse edge1239

theorem edge1240 : Holds level0Subgroup PresentedGroup.of representative ⟨515, [(true, true)], 523⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨64, [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)], 515⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge86 edge119) (appendFacts edge161 (appendFacts edge223 edge300))) (appendFacts (appendFacts edge393 (appendFacts edge491 edge1205Inv)) (appendFacts edge1038 (appendFacts edge976Inv edge463)))) (appendFacts (appendFacts (appendFacts edge1112Inv edge1036) (appendFacts edge354Inv (appendFacts edge897 edge192Inv))) (appendFacts (appendFacts edge808 (appendFacts edge102Inv edge762)) (appendFacts edge54Inv (appendFacts edge737 edge28Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge724 edge719Inv) (appendFacts edge693 (appendFacts edge20Inv edge718))) (appendFacts (appendFacts edge8Inv (appendFacts edge712 edge710Inv)) (appendFacts edge3 (appendFacts edge6 edge10)))) (appendFacts (appendFacts (appendFacts edge15 edge22) (appendFacts edge29 (appendFacts edge41 edge55))) (appendFacts (appendFacts edge78 (appendFacts edge104 edge147)) (appendFacts edge195 (appendFacts edge276 edge359)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge467 edge1214) (appendFacts edge1056 (appendFacts edge374Inv edge910))) (appendFacts (appendFacts edge205Inv (appendFacts edge815 edge788)) (appendFacts edge697 (appendFacts edge110Inv edge766)))) (appendFacts (appendFacts (appendFacts edge751Inv edge80) (appendFacts edge107 (appendFacts edge150 edge202))) (appendFacts (appendFacts edge283 (appendFacts edge967 edge453)) (appendFacts edge535 (appendFacts edge1229 edge552Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge1045 edge980Inv) (appendFacts edge470 (appendFacts edge1207 edge1083))) (appendFacts (appendFacts edge413Inv (appendFacts edge940 edge237Inv)) (appendFacts edge832 (appendFacts edge127Inv edge775)))) (appendFacts (appendFacts (appendFacts edge68Inv (appendFacts edge744 edge734)) (appendFacts edge48 (appendFacts edge70 edge92))) (appendFacts (appendFacts edge132 (appendFacts edge174 edge247)) (appendFacts edge321 (appendFacts edge426 edge514)))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨523, [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)], 64⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1099 (appendFacts edge440Inv edge957)) (appendFacts edge883Inv (appendFacts edge328 edge437))) (appendFacts (appendFacts edge521 (appendFacts edge610 edge1235)) (appendFacts (appendFacts edge601Inv edge1088) (appendFacts edge421Inv edge945)))) (appendFacts (appendFacts (appendFacts edge243Inv (appendFacts edge835 edge130Inv)) (appendFacts edge776 (appendFacts edge69Inv edge745))) (appendFacts (appendFacts edge36Inv (appendFacts edge728 edge721Inv)) (appendFacts (appendFacts edge24 edge33) (appendFacts edge45 edge63)))))
  exact scanFacts hp hs (holds_relator 64 (level0Relator 6) (level0_relator 6))

theorem edge1240Inv : Holds level0Subgroup PresentedGroup.of representative ⟨523, [(true, false)], 515⟩ :=
  holds_reverse edge1240

theorem edge1241 : Holds level0Subgroup PresentedGroup.of representative ⟨406, [(false, true)], 442⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨73, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 406⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge94 edge136) (appendFacts edge178 edge255)) (appendFacts (appendFacts edge329 edge440) (appendFacts edge522 edge1240Inv))) (appendFacts (appendFacts (appendFacts edge1091 edge426Inv) (appendFacts edge949 edge879Inv)) (appendFacts (appendFacts edge936 edge872Inv) (appendFacts edge309 edge405))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨442, [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 73⟩ :=
    (appendFacts (appendFacts (appendFacts edge441Inv edge958) (appendFacts edge256Inv (appendFacts edge842 edge137Inv))) (appendFacts (appendFacts edge780 (appendFacts edge73Inv edge747)) (appendFacts edge735Inv (appendFacts edge49 edge72))))
  exact scanFacts hp hs (holds_relator 73 (level0Relator 2) (level0_relator 2))

theorem edge1241Inv : Holds level0Subgroup PresentedGroup.of representative ⟨442, [(false, false)], 406⟩ :=
  holds_reverse edge1241

theorem edge1242 : Holds level0Subgroup PresentedGroup.of representative ⟨672, [(false, true)], 673⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨108, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)], 672⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge150 (appendFacts edge201 edge282)) (appendFacts edge369 (appendFacts edge477 edge1052))) (appendFacts (appendFacts edge1040 (appendFacts edge978 edge467)) (appendFacts edge1214 (appendFacts edge1056 edge374Inv)))) (appendFacts (appendFacts (appendFacts edge910 (appendFacts edge205Inv edge815)) (appendFacts edge109Inv (appendFacts edge766 edge751Inv))) (appendFacts (appendFacts edge80 (appendFacts edge107 edge150)) (appendFacts (appendFacts edge201 edge282) (appendFacts edge707 edge918))))) (appendFacts (appendFacts (appendFacts (appendFacts edge213Inv (appendFacts edge819 edge114Inv)) (appendFacts edge768 (appendFacts edge752Inv edge82))) (appendFacts (appendFacts edge111 (appendFacts edge153 edge206)) (appendFacts edge287 (appendFacts edge375 edge1057)))) (appendFacts (appendFacts (appendFacts edge446Inv (appendFacts edge960 edge885)) (appendFacts edge333 (appendFacts edge708Inv edge910))) (appendFacts (appendFacts edge857Inv (appendFacts edge285 edge372)) (appendFacts (appendFacts edge479 edge566) (appendFacts edge638 edge671))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨673, [(true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 108⟩ :=
    (appendFacts (appendFacts (appendFacts edge672Inv (appendFacts edge1167 edge568Inv)) (appendFacts edge1055 (appendFacts edge373Inv edge909))) (appendFacts (appendFacts edge204Inv (appendFacts edge815 edge109Inv)) (appendFacts (appendFacts edge766 edge751Inv) (appendFacts edge80 edge107))))
  exact scanFacts hp hs (holds_relator 108 (level0Relator 3) (level0_relator 3))

theorem edge1242Inv : Holds level0Subgroup PresentedGroup.of representative ⟨673, [(false, false)], 672⟩ :=
  holds_reverse edge1242

theorem edge1243 : Holds level0Subgroup PresentedGroup.of representative ⟨544, [(false, true)], 558⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨155, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)], 544⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge817 edge112Inv) (appendFacts edge767 edge752)) (appendFacts (appendFacts edge83 edge114) (appendFacts edge156 (appendFacts edge212 edge292)))) (appendFacts (appendFacts (appendFacts edge385 edge1220) (appendFacts edge432Inv edge953)) (appendFacts (appendFacts edge251Inv edge839) (appendFacts edge800Inv (appendFacts edge175 edge249))))) (appendFacts (appendFacts (appendFacts (appendFacts edge323 edge703Inv) (appendFacts edge890 edge847)) (appendFacts (appendFacts edge267 edge704) (appendFacts edge920 (appendFacts edge215Inv edge820)))) (appendFacts (appendFacts (appendFacts edge791 edge158) (appendFacts edge217 edge297)) (appendFacts (appendFacts edge387 edge1219) (appendFacts edge975 (appendFacts edge462 edge543))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨558, [(true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 155⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge557Inv (appendFacts edge1047 edge365Inv)) (appendFacts edge903 (appendFacts edge198Inv edge811))) (appendFacts (appendFacts edge105Inv (appendFacts edge764 edge56Inv)) (appendFacts (appendFacts edge738 edge29Inv) (appendFacts edge725 edge720)))) (appendFacts (appendFacts (appendFacts edge23 (appendFacts edge32 edge44)) (appendFacts (appendFacts edge61 edge84) (appendFacts edge115 edge157))) (appendFacts (appendFacts edge215 (appendFacts edge295 edge969Inv)) (appendFacts (appendFacts edge1212 edge378Inv) (appendFacts edge914 edge209Inv)))))
  exact scanFacts hp hs (holds_relator 155 (level0Relator 3) (level0_relator 3))

theorem edge1243Inv : Holds level0Subgroup PresentedGroup.of representative ⟨558, [(false, false)], 544⟩ :=
  holds_reverse edge1243

theorem edge1244 : Holds level0Subgroup PresentedGroup.of representative ⟨497, [(true, true)], 487⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨161, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)], 497⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge823 edge118Inv) (appendFacts edge770 (appendFacts edge62Inv edge741))) (appendFacts (appendFacts edge732Inv (appendFacts edge43 edge59)) (appendFacts edge82 (appendFacts edge112 edge154)))) (appendFacts (appendFacts (appendFacts edge209 edge289) (appendFacts edge378 (appendFacts edge1218 edge342Inv))) (appendFacts (appendFacts edge891 (appendFacts edge847Inv edge266)) (appendFacts edge341 (appendFacts edge454 edge536))))) (appendFacts (appendFacts (appendFacts (appendFacts edge1233 edge579Inv) (appendFacts edge1068 (appendFacts edge394Inv edge926))) (appendFacts (appendFacts edge223Inv (appendFacts edge824 edge119Inv)) (appendFacts edge771 (appendFacts edge754 edge695)))) (appendFacts (appendFacts (appendFacts edge64Inv (appendFacts edge742 edge733)) (appendFacts edge46 (appendFacts edge65 edge87))) (appendFacts (appendFacts edge121 (appendFacts edge163 edge226)) (appendFacts edge303 (appendFacts edge399 edge496))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨487, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 161⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1062 edge382Inv) (appendFacts edge916 edge211Inv)) (appendFacts (appendFacts edge818 edge113Inv) (appendFacts edge768 (appendFacts edge60Inv edge740)))) (appendFacts (appendFacts (appendFacts edge732 edge44) (appendFacts edge62 edge85)) (appendFacts (appendFacts edge118 edge160) (appendFacts edge221 (appendFacts edge867 edge221Inv)))))
  exact scanFacts hp hs (holds_relator 161 (level0Relator 3) (level0_relator 3))

theorem edge1244Inv : Holds level0Subgroup PresentedGroup.of representative ⟨487, [(true, false)], 497⟩ :=
  holds_reverse edge1244

theorem edge1245 : Holds level0Subgroup PresentedGroup.of representative ⟨607, [(false, true)], 607⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨200, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)], 607⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge280 edge706) (appendFacts edge930 (appendFacts edge227Inv edge826))) (appendFacts (appendFacts edge121Inv (appendFacts edge772 edge755)) (appendFacts edge88 (appendFacts edge124 edge166)))) (appendFacts (appendFacts (appendFacts edge233 edge701) (appendFacts edge879 (appendFacts edge321 edge427))) (appendFacts (appendFacts edge515 (appendFacts edge1140 edge1093)) (appendFacts edge1014 (appendFacts edge517 edge606)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨607, [(true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 200⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge606Inv edge1094) (appendFacts edge429Inv (appendFacts edge950 edge880))) (appendFacts (appendFacts edge323 edge968Inv) (appendFacts edge454 (appendFacts edge536 edge1233)))) (appendFacts (appendFacts (appendFacts edge1128 edge1234) (appendFacts edge551Inv (appendFacts edge1044 edge980))) (appendFacts (appendFacts edge471 edge552) (appendFacts edge1231 (appendFacts edge535Inv edge1027))))) (appendFacts (appendFacts (appendFacts (appendFacts edge967Inv edge907) (appendFacts edge202Inv (appendFacts edge813 edge107Inv))) (appendFacts (appendFacts edge765 edge751) (appendFacts edge81 (appendFacts edge110 edge697)))) (appendFacts (appendFacts (appendFacts edge110Inv edge766) (appendFacts edge58Inv (appendFacts edge739 edge731Inv))) (appendFacts (appendFacts edge41 (appendFacts edge56 edge79)) (appendFacts edge106 (appendFacts edge149 edge199))))))
  exact scanFacts hp hs (holds_relator 200 (level0Relator 3) (level0_relator 3))

theorem edge1245Inv : Holds level0Subgroup PresentedGroup.of representative ⟨607, [(false, false)], 607⟩ :=
  holds_reverse edge1245

theorem edge1246 : Holds level0Subgroup PresentedGroup.of representative ⟨440, [(false, true)], 345⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨248, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 440⟩ :=
    (appendFacts (appendFacts edge321 (appendFacts edge426 edge514)) (appendFacts edge1240 (appendFacts edge1099 edge1019Inv)))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨345, [(true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 248⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge344Inv (appendFacts edge892 edge187Inv)) (appendFacts (appendFacts edge806 edge783Inv) (appendFacts edge142 edge185))) (appendFacts (appendFacts edge266 (appendFacts edge703 edge951)) (appendFacts (appendFacts edge880Inv edge322) (appendFacts edge428 edge516)))) (appendFacts (appendFacts (appendFacts edge1140Inv (appendFacts edge1092 edge1013Inv)) (appendFacts (appendFacts edge514 edge1240) (appendFacts edge1099 edge440Inv))) (appendFacts (appendFacts edge957 (appendFacts edge883Inv edge328)) (appendFacts (appendFacts edge437 edge521) (appendFacts edge610 edge1235))))) (appendFacts (appendFacts (appendFacts (appendFacts edge601Inv (appendFacts edge1088 edge421Inv)) (appendFacts (appendFacts edge945 edge243Inv) (appendFacts edge835 edge130Inv))) (appendFacts (appendFacts edge776 (appendFacts edge69Inv edge745)) (appendFacts (appendFacts edge36Inv edge728) (appendFacts edge721Inv edge24)))) (appendFacts (appendFacts (appendFacts edge33 (appendFacts edge45 edge64)) (appendFacts (appendFacts edge695 edge64Inv) (appendFacts edge742 edge733))) (appendFacts (appendFacts (appendFacts edge46 edge66) (appendFacts edge88 edge124)) (appendFacts (appendFacts edge166 edge233) (appendFacts edge701 edge879))))))
  exact scanFacts hp hs (holds_relator 248 (level0Relator 3) (level0_relator 3))

theorem edge1246Inv : Holds level0Subgroup PresentedGroup.of representative ⟨345, [(false, false)], 440⟩ :=
  holds_reverse edge1246

theorem edge1247 : Holds level0Subgroup PresentedGroup.of representative ⟨385, [(false, true)], 353⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨296, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)], 385⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge920 (appendFacts edge215Inv edge820)) (appendFacts edge791 (appendFacts edge158 edge217))) (appendFacts (appendFacts edge297 (appendFacts edge387 edge1219)) (appendFacts (appendFacts edge353Inv edge897) (appendFacts edge850Inv edge272)))) (appendFacts (appendFacts (appendFacts edge351 (appendFacts edge461 edge1208Inv)) (appendFacts edge1041 (appendFacts edge978Inv edge466))) (appendFacts (appendFacts edge1052Inv (appendFacts edge1051 edge984)) (appendFacts (appendFacts edge918 edge861Inv) (appendFacts edge292 edge384)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨353, [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 296⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge352Inv edge896) (appendFacts edge191Inv edge808)) (appendFacts (appendFacts edge102Inv edge762) (appendFacts edge54Inv (appendFacts edge737 edge28Inv)))) (appendFacts (appendFacts (appendFacts edge724 edge14Inv) (appendFacts edge715 edge713)) (appendFacts (appendFacts edge10 edge15) (appendFacts edge22 (appendFacts edge30 edge42))))) (appendFacts (appendFacts (appendFacts (appendFacts edge57 edge80) (appendFacts edge108 edge151)) (appendFacts (appendFacts edge698 edge831) (appendFacts edge796Inv (appendFacts edge167 edge234)))) (appendFacts (appendFacts (appendFacts edge310 edge406) (appendFacts edge1077 (appendFacts edge1012Inv edge513))) (appendFacts (appendFacts edge1206Inv edge1060) (appendFacts edge990Inv (appendFacts edge1218 edge969))))))
  exact scanFacts hp hs (holds_relator 296 (level0Relator 3) (level0_relator 3))

theorem edge1247Inv : Holds level0Subgroup PresentedGroup.of representative ⟨353, [(false, false)], 385⟩ :=
  holds_reverse edge1247

theorem edge1248 : Holds level0Subgroup PresentedGroup.of representative ⟨458, [(true, true)], 494⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨323, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true)], 458⟩ :=
    (appendFacts (appendFacts (appendFacts edge950 (appendFacts edge880 edge323)) (appendFacts edge703Inv (appendFacts edge890 edge185Inv))) (appendFacts (appendFacts edge805 (appendFacts edge783 edge143)) (appendFacts (appendFacts edge188 edge269) (appendFacts edge346 edge457))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨494, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 323⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1069 (appendFacts edge395Inv edge927)) (appendFacts edge224Inv (appendFacts edge825 edge120Inv))) (appendFacts (appendFacts edge771 (appendFacts edge754 edge695)) (appendFacts edge754Inv (appendFacts edge86 edge119)))) (appendFacts (appendFacts (appendFacts edge161 (appendFacts edge222 edge925)) (appendFacts edge220Inv (appendFacts edge823 edge118Inv))) (appendFacts (appendFacts edge770 (appendFacts edge62Inv edge741)) (appendFacts (appendFacts edge32Inv edge726) (appendFacts edge16Inv edge716))))) (appendFacts (appendFacts (appendFacts (appendFacts edge6Inv (appendFacts edge711 edge710)) (appendFacts edge4 (appendFacts edge8 edge12))) (appendFacts (appendFacts edge19 (appendFacts edge26 edge38)) (appendFacts edge50 (appendFacts edge73 edge95)))) (appendFacts (appendFacts (appendFacts edge138 (appendFacts edge180 edge258)) (appendFacts edge332 (appendFacts edge445 edge526))) (appendFacts (appendFacts edge617 (appendFacts edge1239 edge1141Inv)) (appendFacts (appendFacts edge1245 edge606Inv) (appendFacts edge1094 edge429Inv))))))
  exact scanFacts hp hs (holds_relator 323 (level0Relator 3) (level0_relator 3))

theorem edge1248Inv : Holds level0Subgroup PresentedGroup.of representative ⟨494, [(true, false)], 458⟩ :=
  holds_reverse edge1248

theorem edge1249 : Holds level0Subgroup PresentedGroup.of representative ⟨336, [(true, true)], 327⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨343, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true)], 336⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1212 edge990) (appendFacts edge484 (appendFacts edge1206 edge1090))) (appendFacts (appendFacts edge424Inv (appendFacts edge947 edge245Inv)) (appendFacts edge836 (appendFacts edge131Inv edge777)))) (appendFacts (appendFacts (appendFacts edge757Inv edge91) (appendFacts edge129 (appendFacts edge171 edge241))) (appendFacts (appendFacts edge913 (appendFacts edge208Inv edge817)) (appendFacts edge112Inv (appendFacts edge767 edge752))))) (appendFacts (appendFacts (appendFacts (appendFacts edge83 edge114) (appendFacts edge156 (appendFacts edge212 edge292))) (appendFacts (appendFacts edge384 (appendFacts edge1247 edge974Inv)) (appendFacts edge461 (appendFacts edge1223 edge1056)))) (appendFacts (appendFacts (appendFacts edge987 (appendFacts edge961 edge259Inv)) (appendFacts edge843 (appendFacts edge138Inv edge780))) (appendFacts (appendFacts edge759 (appendFacts edge96 edge139)) (appendFacts edge181 (appendFacts edge261 edge335))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨327, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 343⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge954 edge252Inv) (appendFacts edge840 edge801)) (appendFacts (appendFacts edge178 edge255) (appendFacts edge329 (appendFacts edge439 edge1246)))) (appendFacts (appendFacts (appendFacts edge344Inv edge892) (appendFacts edge187Inv edge806)) (appendFacts (appendFacts edge783Inv edge142) (appendFacts edge186 (appendFacts edge267 edge342)))))
  exact scanFacts hp hs (holds_relator 343 (level0Relator 3) (level0_relator 3))

theorem edge1249Inv : Holds level0Subgroup PresentedGroup.of representative ⟨327, [(true, false)], 336⟩ :=
  holds_reverse edge1249

theorem edge1250 : Holds level0Subgroup PresentedGroup.of representative ⟨345, [(false, true)], 440⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨345, [], 345⟩ :=
    (holds_refl 345)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨440, [(false, true)], 345⟩ :=
    edge1246
  exact scanFacts hp hs (holds_relator 345 (level0Relator 0) (level0_relator 0))

theorem edge1250Inv : Holds level0Subgroup PresentedGroup.of representative ⟨440, [(false, false)], 345⟩ :=
  holds_reverse edge1250

theorem edge1251 : Holds level0Subgroup PresentedGroup.of representative ⟨353, [(false, true)], 385⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨353, [], 353⟩ :=
    (holds_refl 353)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨385, [(false, true)], 353⟩ :=
    edge1247
  exact scanFacts hp hs (holds_relator 353 (level0Relator 0) (level0_relator 0))

theorem edge1251Inv : Holds level0Subgroup PresentedGroup.of representative ⟨385, [(false, false)], 353⟩ :=
  holds_reverse edge1251

theorem edge1252 : Holds level0Subgroup PresentedGroup.of representative ⟨585, [(false, true)], 595⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨364, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 585⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge471 edge552) (appendFacts edge1231 (appendFacts edge535Inv edge1027))) (appendFacts (appendFacts edge967Inv (appendFacts edge907 edge202Inv)) (appendFacts edge813 (appendFacts edge107Inv edge765)))) (appendFacts (appendFacts (appendFacts edge57Inv edge739) (appendFacts edge30Inv (appendFacts edge725 edge15Inv))) (appendFacts (appendFacts edge716 (appendFacts edge713Inv edge9)) (appendFacts edge13 (appendFacts edge693 edge20Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge718 edge714Inv) (appendFacts edge11 (appendFacts edge17 edge24))) (appendFacts (appendFacts edge33 (appendFacts edge45 edge64)) (appendFacts edge695 (appendFacts edge64Inv edge742)))) (appendFacts (appendFacts (appendFacts edge733 edge46) (appendFacts edge65 (appendFacts edge87 edge121))) (appendFacts (appendFacts edge163 (appendFacts edge226 edge303)) (appendFacts edge398 (appendFacts edge495 edge584))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨595, [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 364⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge594Inv edge1078) (appendFacts edge408Inv edge938)) (appendFacts (appendFacts edge235Inv edge830) (appendFacts edge125Inv (appendFacts edge774 edge756)))) (appendFacts (appendFacts (appendFacts edge90 edge127) (appendFacts edge169 (appendFacts edge237 edge313))) (appendFacts (appendFacts edge413 edge506) (appendFacts edge1207Inv (appendFacts edge1044 edge980)))))
  exact scanFacts hp hs (holds_relator 364 (level0Relator 3) (level0_relator 3))

theorem edge1252Inv : Holds level0Subgroup PresentedGroup.of representative ⟨595, [(false, false)], 585⟩ :=
  holds_reverse edge1252

theorem edge1253 : Holds level0Subgroup PresentedGroup.of representative ⟨442, [(false, true)], 406⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨406, [(false, true)], 442⟩ :=
    edge1241
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨406, [], 406⟩ :=
    (holds_refl 406)
  exact scanFacts hp hs (holds_relator 406 (level0Relator 0) (level0_relator 0))

theorem edge1253Inv : Holds level0Subgroup PresentedGroup.of representative ⟨406, [(false, false)], 442⟩ :=
  holds_reverse edge1253

theorem edge1254 : Holds level0Subgroup PresentedGroup.of representative ⟨542, [(false, true)], 572⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨423, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)], 542⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1213 (appendFacts edge436Inv edge955)) (appendFacts (appendFacts edge253Inv edge840) (appendFacts edge135Inv edge779))) (appendFacts (appendFacts edge72Inv (appendFacts edge746 edge37Inv)) (appendFacts (appendFacts edge729 edge19Inv) (appendFacts edge718 edge8Inv)))) (appendFacts (appendFacts (appendFacts edge712 (appendFacts edge710Inv edge3)) (appendFacts (appendFacts edge6 edge10) (appendFacts edge15 edge22))) (appendFacts (appendFacts edge29 (appendFacts edge41 edge56)) (appendFacts (appendFacts edge79 edge105) (appendFacts edge148 edge197))))) (appendFacts (appendFacts (appendFacts (appendFacts edge278 (appendFacts edge363 edge471)) (appendFacts (appendFacts edge552 edge1231) (appendFacts edge535Inv edge1027))) (appendFacts (appendFacts edge340Inv (appendFacts edge889 edge184Inv)) (appendFacts (appendFacts edge804 edge782) (appendFacts edge696 edge98Inv)))) (appendFacts (appendFacts (appendFacts edge760 (appendFacts edge51Inv edge736)) (appendFacts (appendFacts edge730 edge40) (appendFacts edge54 edge77))) (appendFacts (appendFacts edge101 (appendFacts edge144 edge190)) (appendFacts (appendFacts edge271 edge349) (appendFacts edge459 edge541))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨572, [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 423⟩ :=
    (appendFacts (appendFacts edge1228Inv (appendFacts edge1090 edge424Inv)) (appendFacts (appendFacts edge947 edge878Inv) (appendFacts edge319 edge422)))
  exact scanFacts hp hs (holds_relator 423 (level0Relator 3) (level0_relator 3))

theorem edge1254Inv : Holds level0Subgroup PresentedGroup.of representative ⟨572, [(false, false)], 542⟩ :=
  holds_reverse edge1254

theorem edge1255 : Holds level0Subgroup PresentedGroup.of representative ⟨435, [(true, true)], 336⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨435, [], 435⟩ :=
    (holds_refl 435)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨336, [(true, true), (true, true)], 435⟩ :=
    (appendFacts edge1249 edge434)
  exact scanFacts hp hs (holds_relator 435 (level0Relator 1) (level0_relator 1))

theorem edge1255Inv : Holds level0Subgroup PresentedGroup.of representative ⟨336, [(true, false)], 435⟩ :=
  holds_reverse edge1255

theorem edge1256 : Holds level0Subgroup PresentedGroup.of representative ⟨596, [(false, true)], 540⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨440, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)], 596⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1246 edge344Inv) (appendFacts edge892 edge848)) (appendFacts (appendFacts edge269 edge346) (appendFacts edge457 edge1248))) (appendFacts (appendFacts (appendFacts edge1069 edge395Inv) (appendFacts edge927 edge224Inv)) (appendFacts (appendFacts edge825 edge120Inv) (appendFacts edge771 edge63Inv)))) (appendFacts (appendFacts (appendFacts (appendFacts edge742 edge33Inv) (appendFacts edge727 edge721)) (appendFacts (appendFacts edge25 edge35) (appendFacts edge47 edge68))) (appendFacts (appendFacts (appendFacts edge90 edge127) (appendFacts edge169 edge236)) (appendFacts (appendFacts edge312 edge411) (appendFacts edge504 edge595)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨540, [(true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 440⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge539Inv (appendFacts edge1031 edge346Inv)) (appendFacts (appendFacts edge893 edge188Inv) (appendFacts edge806 edge100Inv))) (appendFacts (appendFacts (appendFacts edge761 edge52Inv) (appendFacts edge736 edge27Inv)) (appendFacts (appendFacts edge724 edge14Inv) (appendFacts edge715 edge5Inv)))) (appendFacts (appendFacts (appendFacts (appendFacts edge711 edge710) (appendFacts edge4 edge8)) (appendFacts (appendFacts edge12 edge19) (appendFacts edge26 edge37))) (appendFacts (appendFacts (appendFacts edge49 edge72) (appendFacts edge94 edge136)) (appendFacts (appendFacts edge178 edge255) (appendFacts edge329 edge439)))))
  exact scanFacts hp hs (holds_relator 440 (level0Relator 3) (level0_relator 3))

theorem edge1256Inv : Holds level0Subgroup PresentedGroup.of representative ⟨540, [(false, false)], 596⟩ :=
  holds_reverse edge1256

theorem edge1257 : Holds level0Subgroup PresentedGroup.of representative ⟨494, [(true, true)], 540⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨458, [(true, true)], 494⟩ :=
    edge1248
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨540, [(true, true)], 458⟩ :=
    edge539Inv
  exact scanFacts hp hs (holds_relator 458 (level0Relator 1) (level0_relator 1))

theorem edge1257Inv : Holds level0Subgroup PresentedGroup.of representative ⟨540, [(true, false)], 494⟩ :=
  holds_reverse edge1257

theorem edge1258 : Holds level0Subgroup PresentedGroup.of representative ⟨625, [(true, true)], 661⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨461, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true)], 625⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1034 edge350Inv) (appendFacts edge895 (appendFacts edge190Inv edge807))) (appendFacts (appendFacts edge101Inv edge762) (appendFacts edge54Inv (appendFacts edge737 edge730Inv)))) (appendFacts (appendFacts (appendFacts edge39 edge52) (appendFacts edge76 (appendFacts edge99 edge142))) (appendFacts (appendFacts edge186 edge267) (appendFacts edge704 (appendFacts edge920 edge215Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge820 edge791) (appendFacts edge158 (appendFacts edge217 edge297))) (appendFacts (appendFacts edge387 edge1219) (appendFacts edge975 (appendFacts edge462 edge1112)))) (appendFacts (appendFacts (appendFacts edge1037 edge976) (appendFacts edge464 (appendFacts edge1205 edge1067))) (appendFacts (appendFacts edge997 (appendFacts edge492 edge579)) (appendFacts edge1209 (appendFacts edge1111 edge624))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨661, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 461⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1189 edge618Inv) (appendFacts edge1105 (appendFacts edge448Inv edge962))) (appendFacts (appendFacts edge260Inv (appendFacts edge844 edge803)) (appendFacts edge182 (appendFacts edge263 edge337)))) (appendFacts (appendFacts (appendFacts edge449 edge529) (appendFacts edge620 (appendFacts edge661 edge1217))) (appendFacts (appendFacts edge1189 (appendFacts edge618Inv edge1105)) (appendFacts edge1023Inv (appendFacts edge527 edge1224Inv)))))
  exact scanFacts hp hs (holds_relator 461 (level0Relator 3) (level0_relator 3))

theorem edge1258Inv : Holds level0Subgroup PresentedGroup.of representative ⟨661, [(true, false)], 625⟩ :=
  holds_reverse edge1258

theorem edge1259 : Holds level0Subgroup PresentedGroup.of representative ⟨408, [(false, true)], 392⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨514, [(false, true), (true, true), (false, true), (true, true)], 408⟩ :=
    (appendFacts (appendFacts edge1090 edge1012) (appendFacts edge948 edge1003))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨392, [(true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 514⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge391Inv (appendFacts edge924 edge219Inv)) (appendFacts (appendFacts edge822 edge117Inv) (appendFacts edge770 edge753Inv))) (appendFacts (appendFacts edge84 (appendFacts edge115 edge157)) (appendFacts (appendFacts edge215 edge295) (appendFacts edge969Inv edge1212)))) (appendFacts (appendFacts (appendFacts edge990 (appendFacts edge484 edge1206)) (appendFacts (appendFacts edge1090 edge424Inv) (appendFacts edge947 edge245Inv))) (appendFacts (appendFacts (appendFacts edge836 edge799) (appendFacts edge174 edge247)) (appendFacts (appendFacts edge321 edge426) (appendFacts edge514 edge1240))))) (appendFacts (appendFacts (appendFacts (appendFacts edge1099 (appendFacts edge440Inv edge957)) (appendFacts (appendFacts edge255Inv edge841) (appendFacts edge136Inv edge779))) (appendFacts (appendFacts (appendFacts edge72Inv edge746) (appendFacts edge37Inv edge729)) (appendFacts (appendFacts edge722 edge723) (appendFacts edge13Inv edge715)))) (appendFacts (appendFacts (appendFacts edge713 (appendFacts edge10 edge16)) (appendFacts (appendFacts edge23 edge31) (appendFacts edge43 edge59))) (appendFacts (appendFacts (appendFacts edge82 edge112) (appendFacts edge154 edge209)) (appendFacts (appendFacts edge289 edge379) (appendFacts edge484 edge1206))))))
  exact scanFacts hp hs (holds_relator 514 (level0Relator 3) (level0_relator 3))

theorem edge1259Inv : Holds level0Subgroup PresentedGroup.of representative ⟨392, [(false, false)], 408⟩ :=
  holds_reverse edge1259

theorem edge1260 : Holds level0Subgroup PresentedGroup.of representative ⟨523, [(true, true)], 605⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨515, [(true, true)], 523⟩ :=
    edge1240
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨605, [(true, true)], 515⟩ :=
    edge604Inv
  exact scanFacts hp hs (holds_relator 515 (level0Relator 1) (level0_relator 1))

theorem edge1260Inv : Holds level0Subgroup PresentedGroup.of representative ⟨605, [(true, false)], 523⟩ :=
  holds_reverse edge1260

theorem edge1261 : Holds level0Subgroup PresentedGroup.of representative ⟨608, [(false, true)], 618⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨527, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 608⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1103 (appendFacts edge1022 edge989)) (appendFacts (appendFacts edge988 edge482) (appendFacts edge1215Inv edge1058))) (appendFacts (appendFacts (appendFacts edge376Inv edge911) (appendFacts edge206Inv edge816)) (appendFacts (appendFacts edge111Inv edge767) (appendFacts edge752 edge83)))) (appendFacts (appendFacts (appendFacts (appendFacts edge114 edge156) (appendFacts edge213 edge293)) (appendFacts (appendFacts edge707Inv edge906) (appendFacts edge855 edge283))) (appendFacts (appendFacts (appendFacts edge702Inv edge889) (appendFacts edge184Inv edge804)) (appendFacts (appendFacts edge782 edge696) (appendFacts edge782Inv edge141))))) (appendFacts (appendFacts (appendFacts (appendFacts edge183 (appendFacts edge264 edge338)) (appendFacts (appendFacts edge451 edge531) (appendFacts edge1150 edge623Inv))) (appendFacts (appendFacts (appendFacts edge1107 edge450Inv) (appendFacts edge965 edge263Inv)) (appendFacts (appendFacts edge845 edge803Inv) (appendFacts edge181 edge260)))) (appendFacts (appendFacts (appendFacts (appendFacts edge334 edge448) (appendFacts edge528 edge618)) (appendFacts (appendFacts edge660 edge1258Inv) (appendFacts edge1151 edge537Inv))) (appendFacts (appendFacts (appendFacts edge1028 edge968) (appendFacts edge951 edge880Inv)) (appendFacts (appendFacts edge322 edge429) (appendFacts edge517 edge607))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨618, [(true, true)], 527⟩ :=
    edge617Inv
  exact scanFacts hp hs (holds_relator 527 (level0Relator 3) (level0_relator 3))

theorem edge1261Inv : Holds level0Subgroup PresentedGroup.of representative ⟨618, [(false, false)], 608⟩ :=
  holds_reverse edge1261

theorem edge1262 : Holds level0Subgroup PresentedGroup.of representative ⟨540, [(false, true)], 596⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨540, [], 540⟩ :=
    (holds_refl 540)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨596, [(false, true)], 540⟩ :=
    edge1256
  exact scanFacts hp hs (holds_relator 540 (level0Relator 0) (level0_relator 0))

theorem edge1262Inv : Holds level0Subgroup PresentedGroup.of representative ⟨596, [(false, false)], 540⟩ :=
  holds_reverse edge1262

theorem edge1263 : Holds level0Subgroup PresentedGroup.of representative ⟨504, [(true, false)], 459⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨540, [(false, true), (true, false), (false, true), (true, false), (false, true)], 504⟩ :=
    (appendFacts (appendFacts edge1262 edge595Inv) (appendFacts edge1081 (appendFacts edge1005Inv edge503)))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨459, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 540⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1032 edge347Inv) (appendFacts edge894 (appendFacts edge189Inv edge807))) (appendFacts (appendFacts edge101Inv (appendFacts edge762 edge749Inv)) (appendFacts edge694 (appendFacts edge53Inv edge737)))) (appendFacts (appendFacts (appendFacts edge730Inv edge39) (appendFacts edge52 (appendFacts edge76 edge100))) (appendFacts (appendFacts edge143 (appendFacts edge188 edge269)) (appendFacts edge346 (appendFacts edge457 edge539)))))
  exact scanFacts hp hs (holds_relator 540 (level0Relator 2) (level0_relator 2))

theorem edge1263Inv : Holds level0Subgroup PresentedGroup.of representative ⟨459, [(true, true)], 504⟩ :=
  holds_reverse edge1263

theorem edge1264 : Holds level0Subgroup PresentedGroup.of representative ⟨504, [(true, true)], 541⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨541, [(true, true), (true, true)], 504⟩ :=
    (appendFacts edge540Inv edge1263Inv)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨541, [], 541⟩ :=
    (holds_refl 541)
  exact scanFacts hp hs (holds_relator 541 (level0Relator 1) (level0_relator 1))

theorem edge1264Inv : Holds level0Subgroup PresentedGroup.of representative ⟨541, [(true, false)], 504⟩ :=
  holds_reverse edge1264

theorem edge1265 : Holds level0Subgroup PresentedGroup.of representative ⟨572, [(false, true)], 542⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨542, [(false, true)], 572⟩ :=
    edge1254
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨542, [], 542⟩ :=
    (holds_refl 542)
  exact scanFacts hp hs (holds_relator 542 (level0Relator 0) (level0_relator 0))

theorem edge1265Inv : Holds level0Subgroup PresentedGroup.of representative ⟨542, [(false, false)], 572⟩ :=
  holds_reverse edge1265

theorem edge1266 : Holds level0Subgroup PresentedGroup.of representative ⟨558, [(false, true)], 544⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨544, [(false, true)], 558⟩ :=
    edge1243
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨544, [], 544⟩ :=
    (holds_refl 544)
  exact scanFacts hp hs (holds_relator 544 (level0Relator 0) (level0_relator 0))

theorem edge1266Inv : Holds level0Subgroup PresentedGroup.of representative ⟨544, [(false, false)], 558⟩ :=
  holds_reverse edge1266

theorem edge1267 : Holds level0Subgroup PresentedGroup.of representative ⟨297, [(true, false)], 306⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨558, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)], 297⟩ :=
    (appendFacts (appendFacts (appendFacts edge1266 edge543Inv) (appendFacts edge1036 edge975Inv)) (appendFacts (appendFacts edge1210 edge387Inv) (appendFacts edge922 (appendFacts edge863Inv edge296))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨306, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 558⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge931 edge228Inv) (appendFacts edge827 edge794Inv)) (appendFacts (appendFacts edge163 edge227) (appendFacts edge304 (appendFacts edge706Inv edge904)))) (appendFacts (appendFacts (appendFacts edge199Inv edge812) (appendFacts edge786Inv edge148)) (appendFacts (appendFacts edge198 edge279) (appendFacts edge365 (appendFacts edge473 edge557)))))
  exact scanFacts hp hs (holds_relator 558 (level0Relator 2) (level0_relator 2))

theorem edge1267Inv : Holds level0Subgroup PresentedGroup.of representative ⟨306, [(true, true)], 297⟩ :=
  holds_reverse edge1267

theorem edge1268 : Holds level0Subgroup PresentedGroup.of representative ⟨595, [(false, true)], 585⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨585, [(false, true)], 595⟩ :=
    edge1252
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨585, [], 585⟩ :=
    (holds_refl 585)
  exact scanFacts hp hs (holds_relator 585 (level0Relator 0) (level0_relator 0))

theorem edge1268Inv : Holds level0Subgroup PresentedGroup.of representative ⟨585, [(false, false)], 595⟩ :=
  holds_reverse edge1268

theorem edge1269 : Holds level0Subgroup PresentedGroup.of representative ⟨594, [(false, true)], 535⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨585, [(false, true), (true, false)], 594⟩ :=
    (appendFacts edge1252 edge1135Inv)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨535, [(true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 585⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1110 edge1229) (appendFacts edge552Inv edge1045)) (appendFacts (appendFacts edge980Inv edge470) (appendFacts edge551 edge1232))) (appendFacts (appendFacts (appendFacts edge580Inv edge1068) (appendFacts edge394Inv edge926)) (appendFacts (appendFacts edge223Inv edge824) (appendFacts edge119Inv (appendFacts edge771 edge754))))) (appendFacts (appendFacts (appendFacts (appendFacts edge695 edge64Inv) (appendFacts edge742 edge33Inv)) (appendFacts (appendFacts edge727 edge17Inv) (appendFacts edge717 edge7Inv))) (appendFacts (appendFacts (appendFacts edge712 edge710Inv) (appendFacts edge3 edge6)) (appendFacts (appendFacts edge10 edge15) (appendFacts edge22 (appendFacts edge29 edge41)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge56 edge79) (appendFacts edge105 edge148)) (appendFacts (appendFacts edge198 edge279) (appendFacts edge365 edge473))) (appendFacts (appendFacts (appendFacts edge557 edge1266) (appendFacts edge1152 edge1037)) (appendFacts (appendFacts edge976 edge464) (appendFacts edge1205 (appendFacts edge1067 edge393Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge926 edge223Inv) (appendFacts edge824 edge119Inv)) (appendFacts (appendFacts edge771 edge63Inv) (appendFacts edge742 (appendFacts edge733 edge46)))) (appendFacts (appendFacts (appendFacts edge65 edge87) (appendFacts edge121 edge163)) (appendFacts (appendFacts edge226 edge303) (appendFacts edge398 (appendFacts edge495 edge584)))))))
  exact scanFacts hp hs (holds_relator 585 (level0Relator 4) (level0_relator 4))

theorem edge1269Inv : Holds level0Subgroup PresentedGroup.of representative ⟨535, [(false, false)], 594⟩ :=
  holds_reverse edge1269

theorem edge1270 : Holds level0Subgroup PresentedGroup.of representative ⟨535, [(false, true)], 594⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨594, [(false, true)], 535⟩ :=
    edge1269
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨594, [], 594⟩ :=
    (holds_refl 594)
  exact scanFacts hp hs (holds_relator 594 (level0Relator 0) (level0_relator 0))

theorem edge1270Inv : Holds level0Subgroup PresentedGroup.of representative ⟨594, [(false, false)], 535⟩ :=
  holds_reverse edge1270

theorem edge1271 : Holds level0Subgroup PresentedGroup.of representative ⟨432, [(false, true)], 384⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨594, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 432⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1269 edge534Inv) (appendFacts edge1027 edge967Inv)) (appendFacts (appendFacts edge907 edge855Inv) (appendFacts edge282 (appendFacts edge707 edge918)))) (appendFacts (appendFacts (appendFacts edge861Inv edge292) (appendFacts edge385 edge1220)) (appendFacts (appendFacts edge432Inv edge953) (appendFacts edge881Inv (appendFacts edge324 edge431)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨384, [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 594⟩ :=
    (appendFacts (appendFacts (appendFacts edge992Inv edge486) (appendFacts edge1244Inv edge1072)) (appendFacts (appendFacts edge999Inv edge495) (appendFacts edge584 (appendFacts edge1252 edge1135Inv))))
  exact scanFacts hp hs (holds_relator 594 (level0Relator 2) (level0_relator 2))

theorem edge1271Inv : Holds level0Subgroup PresentedGroup.of representative ⟨384, [(false, false)], 432⟩ :=
  holds_reverse edge1271

theorem edge1272 : Holds level0Subgroup PresentedGroup.of representative ⟨681, [(false, true)], 666⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨606, [(false, true), (true, false)], 681⟩ :=
    (appendFacts edge654 edge680)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨666, [(true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false)], 606⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge665Inv edge1156) (appendFacts edge548Inv edge1042)) (appendFacts (appendFacts edge360Inv edge901) (appendFacts edge852Inv edge276))) (appendFacts (appendFacts (appendFacts edge358 edge466) (appendFacts edge1052Inv edge1051)) (appendFacts (appendFacts edge984 edge918) (appendFacts edge861Inv (appendFacts edge292 edge384))))) (appendFacts (appendFacts (appendFacts (appendFacts edge1247 edge352Inv) (appendFacts edge896 edge191Inv)) (appendFacts (appendFacts edge808 edge784Inv) (appendFacts edge144 edge190))) (appendFacts (appendFacts (appendFacts edge271 edge350) (appendFacts edge460 edge1224)) (appendFacts (appendFacts edge1104 edge1023) (appendFacts edge528 (appendFacts edge618 edge660)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge1258Inv edge1151) (appendFacts edge537Inv edge1028)) (appendFacts (appendFacts edge341Inv edge890) (appendFacts edge185Inv edge805))) (appendFacts (appendFacts (appendFacts edge99Inv edge761) (appendFacts edge52Inv edge736)) (appendFacts (appendFacts edge730 edge40) (appendFacts edge53 (appendFacts edge694 edge53Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge737 edge28Inv) (appendFacts edge724 edge719Inv)) (appendFacts (appendFacts edge693 edge722Inv) (appendFacts edge26 (appendFacts edge37 edge49)))) (appendFacts (appendFacts (appendFacts edge71 edge93) (appendFacts edge133 edge175)) (appendFacts (appendFacts edge248 edge322) (appendFacts edge428 (appendFacts edge516 edge1183Inv)))))))
  exact scanFacts hp hs (holds_relator 606 (level0Relator 4) (level0_relator 4))

theorem edge1272Inv : Holds level0Subgroup PresentedGroup.of representative ⟨666, [(false, false)], 681⟩ :=
  holds_reverse edge1272

theorem edge1273 : Holds level0Subgroup PresentedGroup.of representative ⟨666, [(true, false)], 641⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨607, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true)], 666⟩ :=
    (appendFacts (appendFacts (appendFacts edge1245 edge606Inv) (appendFacts edge1094 edge1014Inv)) (appendFacts (appendFacts edge516 edge1183Inv) (appendFacts edge654 (appendFacts edge680 edge1272))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨641, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 607⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge1168 edge569Inv) (appendFacts edge1059 edge377Inv)) (appendFacts (appendFacts edge912 edge858Inv) (appendFacts edge287 (appendFacts edge376 edge482)))) (appendFacts (appendFacts (appendFacts edge1215Inv edge1058) (appendFacts edge988Inv edge1057)) (appendFacts (appendFacts edge1022Inv edge526) (appendFacts edge617 (appendFacts edge1239 edge1141Inv)))))
  exact scanFacts hp hs (holds_relator 607 (level0Relator 2) (level0_relator 2))

theorem edge1273Inv : Holds level0Subgroup PresentedGroup.of representative ⟨641, [(true, true)], 666⟩ :=
  holds_reverse edge1273

theorem edge1274 : Holds level0Subgroup PresentedGroup.of representative ⟨289, [(true, false)], 318⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨608, [(false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)], 289⟩ :=
    (appendFacts (appendFacts (appendFacts edge1261 edge617Inv) (appendFacts edge1103 edge1022)) (appendFacts (appendFacts edge989 edge375Inv) (appendFacts edge911 (appendFacts edge858 edge288))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨318, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true)], 608⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge944 (appendFacts edge242Inv edge835)) (appendFacts edge130Inv (appendFacts edge776 edge69Inv))) (appendFacts (appendFacts edge745 (appendFacts edge734Inv edge47)) (appendFacts (appendFacts edge67 edge89) (appendFacts edge125 edge167)))) (appendFacts (appendFacts (appendFacts edge235 (appendFacts edge311 edge408)) (appendFacts (appendFacts edge501 edge593) (appendFacts edge1269 edge534Inv))) (appendFacts (appendFacts edge1027 (appendFacts edge340Inv edge889)) (appendFacts (appendFacts edge184Inv edge804) (appendFacts edge782 edge696))))) (appendFacts (appendFacts (appendFacts (appendFacts edge98Inv (appendFacts edge760 edge748)) (appendFacts edge76 (appendFacts edge99 edge142))) (appendFacts (appendFacts edge186 (appendFacts edge267 edge342)) (appendFacts (appendFacts edge1212 edge378Inv) (appendFacts edge914 edge209Inv)))) (appendFacts (appendFacts (appendFacts edge817 (appendFacts edge789Inv edge153)) (appendFacts (appendFacts edge206 edge287) (appendFacts edge375 edge1057))) (appendFacts (appendFacts edge1022Inv (appendFacts edge526 edge617)) (appendFacts (appendFacts edge1239 edge1141Inv) (appendFacts edge1245 edge1141))))))
  exact scanFacts hp hs (holds_relator 608 (level0Relator 3) (level0_relator 3))

theorem edge1274Inv : Holds level0Subgroup PresentedGroup.of representative ⟨318, [(true, true)], 289⟩ :=
  holds_reverse edge1274

theorem edge1275 : Holds level0Subgroup PresentedGroup.of representative ⟨609, [(false, true)], 620⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨619, [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)], 609⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge660 edge1258Inv) (appendFacts edge1151 edge537Inv)) (appendFacts (appendFacts edge1028 edge341Inv) (appendFacts edge890 edge185Inv))) (appendFacts (appendFacts (appendFacts edge805 edge99Inv) (appendFacts edge761 edge52Inv)) (appendFacts (appendFacts edge736 edge730) (appendFacts edge40 (appendFacts edge53 edge694))))) (appendFacts (appendFacts (appendFacts (appendFacts edge53Inv edge737) (appendFacts edge28Inv edge724)) (appendFacts (appendFacts edge14Inv edge715) (appendFacts edge5Inv (appendFacts edge711 edge1Inv)))) (appendFacts (appendFacts (appendFacts edge709 edge692Inv) (appendFacts edge0 edge2)) (appendFacts (appendFacts edge4 edge8) (appendFacts edge12 (appendFacts edge19 edge26)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge37 edge49) (appendFacts edge72 edge94)) (appendFacts (appendFacts edge135 edge177) (appendFacts edge253 edge327))) (appendFacts (appendFacts (appendFacts edge436 edge1221) (appendFacts edge422Inv edge946)) (appendFacts (appendFacts edge878 edge320) (appendFacts edge424 (appendFacts edge513 edge1228))))) (appendFacts (appendFacts (appendFacts (appendFacts edge1265 edge541Inv) (appendFacts edge1033 edge973)) (appendFacts (appendFacts edge460 edge1224) (appendFacts edge1104 (appendFacts edge447Inv edge962)))) (appendFacts (appendFacts (appendFacts edge886 edge335) (appendFacts edge1249 edge954)) (appendFacts (appendFacts edge882 edge327) (appendFacts edge435 (appendFacts edge520 edge608)))))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨620, [(true, false)], 619⟩ :=
    edge1147Inv
  exact scanFacts hp hs (holds_relator 619 (level0Relator 4) (level0_relator 4))

theorem edge1275Inv : Holds level0Subgroup PresentedGroup.of representative ⟨620, [(false, false)], 609⟩ :=
  holds_reverse edge1275

theorem edge1276 : Holds level0Subgroup PresentedGroup.of representative ⟨620, [(false, true)], 609⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨620, [], 620⟩ :=
    (holds_refl 620)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨609, [(false, true)], 620⟩ :=
    edge1275
  exact scanFacts hp hs (holds_relator 620 (level0Relator 0) (level0_relator 0))

theorem edge1276Inv : Holds level0Subgroup PresentedGroup.of representative ⟨609, [(false, false)], 620⟩ :=
  holds_reverse edge1276

theorem edge1277 : Holds level0Subgroup PresentedGroup.of representative ⟨662, [(true, true)], 625⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨625, [(true, true), (true, true)], 662⟩ :=
    (appendFacts edge1258 edge1217Inv)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨625, [], 625⟩ :=
    (holds_refl 625)
  exact scanFacts hp hs (holds_relator 625 (level0Relator 1) (level0_relator 1))

theorem edge1277Inv : Holds level0Subgroup PresentedGroup.of representative ⟨625, [(true, false)], 662⟩ :=
  holds_reverse edge1277

theorem edge1278 : Holds level0Subgroup PresentedGroup.of representative ⟨634, [(true, true)], 627⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨627, [(true, true), (true, true)], 634⟩ :=
    (appendFacts edge664 edge1238)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨627, [], 627⟩ :=
    (holds_refl 627)
  exact scanFacts hp hs (holds_relator 627 (level0Relator 1) (level0_relator 1))

theorem edge1278Inv : Holds level0Subgroup PresentedGroup.of representative ⟨627, [(true, false)], 634⟩ :=
  holds_reverse edge1278

theorem edge1279 : Holds level0Subgroup PresentedGroup.of representative ⟨629, [(true, true)], 641⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨629, [], 629⟩ :=
    (holds_refl 629)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨641, [(true, true), (true, true)], 629⟩ :=
    (appendFacts edge1273Inv edge665Inv)
  exact scanFacts hp hs (holds_relator 629 (level0Relator 1) (level0_relator 1))

theorem edge1279Inv : Holds level0Subgroup PresentedGroup.of representative ⟨641, [(true, false)], 629⟩ :=
  holds_reverse edge1279


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
