module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.SevenSquare.Grid

/-!
# Concrete candidate words for the seven-square witness

The ATLAS `BG1-max6W1` program supplies the first pair of local words.
A second pair was found by an untrusted search. Sylow words from the ATLAS
`F42G1-p69888aB0` permutation data were then compressed into the multiplication
program below and evaluated on the actual 4370-dimensional matrices.

This module only defines group words and proves subgroup membership. It assumes
no identification with F₄(2), no element orders, and no computational results.
The two-cycle row equations are separate certification obligations.

Sources: https://brauer.maths.qmul.ac.uk/Atlas/spor/B/words/BG1-max6W1
and https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/F42G1-p69888aB0 .
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare
namespace Concrete

/-- The candidate pair as words in any group. -/
def candidateWords {G : Type*} [Group G] (a b : G) : G × G :=
  let t := (a*b*a*b*a*b*b*a*b*a*b*b)^9
  let x := (a*t)^13
  let y := (a*b)*(t*(a*b)⁻¹*t*(a*b))^5
  let n0 := (x*y^3)^16
  let n1 := wordConjugate ((x*y*x*y^3)^6) (y^3*x*y)
  let n2 := n1 * n1
  let n3 := n0 * n1
  let n4 := n0 * n2
  let n5 := n3 * n4
  let n6 := n3 * n3
  let n7 := n4 * n4
  let n8 := n3 * n5
  let n9 := n4 * n5
  let n10 := n5 * n5
  let n11 := n6 * n8
  let n12 := n7 * n9
  let n13 := n4 * n8
  let n14 := n8 * n9
  let n15 := n11 * n10
  let n16 := n5 * n13
  let n17 := n10 * n12
  let n18 := n6 * n6
  let n19 := n11 * n16
  let n20 := n15 * n14
  let n21 := n20 * n19
  let n22 := n21 * n7
  let n23 := n22 * n12
  let n24 := n23 * n8
  let n25 := n7 * n7
  let n26 := n5 * n12
  let n27 := n26 * n14
  let n28 := n27 * n17
  let n29 := n6 * n11
  let n30 := n29 * n13
  let n31 := n30 * n28
  let n32 := n4 * n18
  let n33 := n15 * n24
  let n34 := n6 * n10
  let n35 := n34 * n5
  let n36 := n32 * n35
  let n37 := n31 * n17
  let n38 := n36 * n24
  let n39 := n13 * n9
  let n40 := n25 * n7
  let n41 := n10 * n40
  let n42 := n41 * n14
  let n43 := n31 * n42
  let n44 := n13 * n7
  let n45 := n5 * n33
  let n46 := n5 * n8
  let n47 := n4 * n6
  let n48 := n16 * n9
  let n49 := n43 * n37
  let n50 := n44 * n8
  let n51 := n38 * n38
  let n52 := n39 * n37
  let n53 := n50 * n33
  let n54 := n47 * n48
  let n55 := n5 * n9
  let n56 := n43 * n49
  let n57 := n8 * n6
  let n58 := n7 * n32
  let n59 := n58 * n5
  let n60 := n59 * n25
  let n61 := n60 * n11
  let n62 := n61 * n9
  let n63 := n7 * n55
  let n64 := n12 * n11
  let n65 := n49 * n7
  let n66 := n5 * n6
  let n67 := n45 * n51
  let n68 := n13 * n46
  let n69 := n46 * n39
  let n70 := n4 * n11
  let n71 := n18 * n16
  let n72 := n13 * n52
  let n73 := n7 * n10
  let n74 := n45 * n38
  let n75 := n57 * n5
  let n78 := n46 * n52
  let n79 := n48 * n37
  let n80 := n54 * n37
  let n81 := n32 * n71
  let n82 := n81 * n28
  let n83 := n82 * n42
  let n84 := n83 * n65
  let n85 := n84 * n72
  let n86 := n2 * n67
  let n87 := n86 * n53
  let n88 := n87 * n53
  let n89 := n47 * n74
  let n90 := n89 * n53
  let n91 := n90 * n51
  let n92 := n91 * n39
  let n93 := n92 * n26
  let n94 := n93 * n64
  let n95 := n94 * n15
  let n96 := n95 * n75
  let n97 := n96 * n14
  let n98 := n97 * n33
  let n99 := n98 * n68
  let n100 := n99 * n62
  let n108 := n39 * n45
  let n109 := n46 * n6
  let n110 := n109 * n16
  let n111 := n5 * n7
  let n112 := n8 * n5
  let n113 := n8 * n52
  let n114 := n54 * n43
  let n115 := n114 * n56
  let n116 := n62 * n79
  let n117 := n116 * n14
  let n118 := n117 * n63
  let n119 := n118 * n17
  let n120 := n119 * n64
  let n121 := n120 * n11
  let n122 := n121 * n69
  let n123 := n122 * n56
  let n124 := n123 * n54
  let n125 := n124 * n65
  let n126 := n4 * n15
  let n127 := n126 * n7
  let n128 := n31 * n10
  let n129 := n44 * n55
  let n130 := n85 * n73
  let n131 := n80 * n54
  let n132 := n131 * n56
  let n133 := n132 * n3
  let n134 := n88 * n44
  let n135 := n134 * n100
  let n136 := n135 * n12
  let n144 := n5 * n11
  let n145 := n2 * n112
  let n146 := n145 * n18
  let n147 := n146 * n46
  let n148 := n147 * n29
  let n149 := n148 * n113
  let n150 := n149 * n57
  let n151 := n150 * n26
  let n152 := n151 * n12
  let n153 := n152 * n12
  let n154 := n153 * n13
  let n155 := n154 * n68
  let n156 := n155 * n52
  let n157 := n156 * n115
  let n158 := n157 * n78
  let n159 := n158 * n47
  let n160 := n159 * n46
  let n161 := n160 * n125
  let n162 := n161 * n8
  let n163 := n162 * n66
  let n164 := n163 * n26
  let n165 := n164 * n127
  let n166 := n165 * n39
  let n167 := n166 * n128
  let n168 := n167 * n63
  let n169 := n168 * n14
  let n170 := n169 * n12
  let n171 := n170 * n63
  let n172 := n171 * n115
  let n173 := n172 * n69
  let n174 := n173 * n128
  let n175 := n174 * n7
  let n176 := n175 * n47
  let n177 := n176 * n5
  let n178 := n177 * n29
  let n179 := n178 * n5
  let n180 := n179 * n70
  let n181 := n180 * n113
  let n182 := n181 * n129
  let n183 := n182 * n7
  let n184 := n183 * n66
  let n185 := n184 * n16
  let n186 := n185 * n80
  let n187 := n186 * n78
  let n188 := n187 * n78
  let n189 := n188 * n18
  let n190 := n189 * n79
  let n191 := n190 * n71
  let n192 := n191 * n130
  let n193 := n192 * n11
  let n194 := n193 * n8
  let n195 := n194 * n125
  let n196 := n195 * n11
  let n197 := n196 * n52
  let n198 := n197 * n133
  let n286 := n136 * n9
  let n287 := n286 * n33
  let n288 := n287 * n51
  let n289 := n288 * n38
  let n290 := n289 * n108
  let n291 := n290 * n47
  let n292 := n291 * n111
  let n293 := n292 * n110
  let n294 := n293 * n15
  let n295 := n294 * n6
  let n296 := n295 * n55
  let n297 := n296 * n6
  let n298 := n297 * n144
  let n299 := n298 * n3
  (n198, n299)

/-- Evaluate inside the standard subgroup, so membership is intrinsic. -/
def candidatePair (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    standardImage ha hb × standardImage ha hb :=
  candidateWords ⟨standardA ha, standardA_mem ha hb⟩ ⟨standardB hb, standardB_mem ha hb⟩

end Concrete
end BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare
