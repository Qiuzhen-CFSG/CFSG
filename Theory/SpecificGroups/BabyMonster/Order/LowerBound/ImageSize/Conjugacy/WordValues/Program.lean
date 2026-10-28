module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.Data

/-!
# The recovered-word straight-line program

This is the group interpretation of `../source/word_dag.json`, generated from
Breuer–Magaard–Wilson (2019), Table 1 and §3.4. Nodes 232 and 241 are the two
recovered words. The proofs compare binary powers with ordinary powers and
check the program against the existing `generatorWords` definition. Inverse
nodes remain genuine group inverses; no numerical inversion is assumed.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound
namespace RecoveredWordProgram
variable {G : Type*} [Group G]
def node0 (_a _b : G) : G := 1
def node1 (a _b : G) : G := a
def node2 (_a b : G) : G := b
def node3 (a b : G) : G := (node1 a b) * (node1 a b)
def node4 (a b : G) : G := (node2 a b) * (node2 a b)
def node5 (a b : G) : G := (node4 a b) * (node2 a b)
def node6 (a b : G) : G := (node1 a b) * (node2 a b)
def node7 (a b : G) : G := (node6 a b) * (node6 a b)
def node8 (a b : G) : G := (node7 a b) * (node6 a b)
def node9 (a b : G) : G := (node8 a b) * (node8 a b)
def node10 (a b : G) : G := (node9 a b) * (node6 a b)
def node11 (a b : G) : G := (node10 a b) * (node10 a b)
def node12 (a b : G) : G := (node11 a b) * (node6 a b)
def node13 (a b : G) : G := (node12 a b) * (node2 a b)
def node14 (a b : G) : G := (node13 a b) * (node13 a b)
def node15 (a b : G) : G := (node14 a b) * (node14 a b)
def node16 (a b : G) : G := (node15 a b) * (node15 a b)
def node17 (a b : G) : G := (node16 a b) * (node13 a b)
def node18 (a b : G) : G := (node17 a b) * (node17 a b)
def node19 (a b : G) : G := (node18 a b) * (node13 a b)
def node20 (a b : G) : G := (node1 a b) * (node19 a b)
def node21 (a b : G) : G := (node20 a b) * (node20 a b)
def node22 (a b : G) : G := (node21 a b) * (node20 a b)
def node23 (a b : G) : G := (node13 a b) * (node13 a b)
def node24 (a b : G) : G := (node23 a b) * (node13 a b)
def node25 (a b : G) : G := (node22 a b) * (node24 a b)
def node26 (a b : G) : G := (node25 a b) * (node25 a b)
def node27 (a b : G) : G := (node26 a b) * (node26 a b)
def node28 (a b : G) : G := (node27 a b) * (node25 a b)
def node29 (a b : G) : G := (node28 a b) * (node28 a b)
def node30 (a b : G) : G := (node13 a b)⁻¹
def node31 (a b : G) : G := (node30 a b) * (node29 a b)
def node32 (a b : G) : G := (node31 a b) * (node13 a b)
def node33 (a b : G) : G := (node32 a b) * (node22 a b)
def node34 (a b : G) : G := (node33 a b) * (node33 a b)
def node35 (a b : G) : G := (node34 a b) * (node33 a b)
def node36 (a b : G) : G := (node35 a b) * (node35 a b)
def node37 (a b : G) : G := (node36 a b) * (node22 a b)
def node38 (a b : G) : G := (node33 a b) * (node33 a b)
def node39 (a b : G) : G := (node38 a b) * (node33 a b)
def node40 (a b : G) : G := (node37 a b) * (node39 a b)
def node41 (a b : G) : G := (node40 a b) * (node40 a b)
def node42 (a b : G) : G := (node41 a b) * (node32 a b)
def node43 (a b : G) : G := (node42 a b) * (node22 a b)
def node44 (a b : G) : G := (node32 a b) * (node32 a b)
def node45 (a b : G) : G := (node43 a b) * (node44 a b)
def node46 (a b : G) : G := (node45 a b) * (node22 a b)
def node47 (a b : G) : G := (node46 a b) * (node46 a b)
def node48 (a b : G) : G := (node47 a b) * (node47 a b)
def node49 (a b : G) : G := (node48 a b) * (node46 a b)
def node50 (a b : G) : G := (node33 a b) * (node33 a b)
def node51 (a b : G) : G := (node50 a b) * (node50 a b)
def node52 (a b : G) : G := (node51 a b)⁻¹
def node53 (a b : G) : G := (node52 a b) * (node49 a b)
def node54 (a b : G) : G := (node53 a b) * (node51 a b)
def node55 (a b : G) : G := (node33 a b) * (node33 a b)
def node56 (a b : G) : G := (node55 a b) * (node55 a b)
def node57 (a b : G) : G := (node56 a b) * (node56 a b)
def node58 (a b : G) : G := (node57 a b) * (node22 a b)
def node59 (a b : G) : G := (node33 a b) * (node33 a b)
def node60 (a b : G) : G := (node59 a b) * (node33 a b)
def node61 (a b : G) : G := (node58 a b) * (node60 a b)
def node62 (a b : G) : G := (node32 a b) * (node22 a b)
def node63 (a b : G) : G := (node32 a b) * (node32 a b)
def node64 (a b : G) : G := (node62 a b) * (node63 a b)
def node65 (a b : G) : G := (node64 a b) * (node22 a b)
def node66 (a b : G) : G := (node65 a b) * (node65 a b)
def node67 (a b : G) : G := (node66 a b)⁻¹
def node68 (a b : G) : G := (node67 a b) * (node61 a b)
def node69 (a b : G) : G := (node68 a b) * (node66 a b)
def node70 (a b : G) : G := (node69 a b) * (node54 a b)
def node71 (a b : G) : G := (node70 a b) * (node0 a b)
def node72 (a b : G) : G := (node71 a b)⁻¹
def node73 (a b : G) : G := (node72 a b) * (node54 a b)
def node74 (a b : G) : G := (node73 a b) * (node71 a b)
def node75 (a b : G) : G := (node69 a b) * (node54 a b)
def node76 (a b : G) : G := (node75 a b) * (node69 a b)
def node77 (a b : G) : G := (node76 a b)⁻¹
def node78 (a b : G) : G := (node77 a b) * (node54 a b)
def node79 (a b : G) : G := (node78 a b) * (node76 a b)
def node80 (a b : G) : G := (node69 a b) * (node54 a b)
def node81 (a b : G) : G := (node69 a b) * (node69 a b)
def node82 (a b : G) : G := (node80 a b) * (node81 a b)
def node83 (a b : G) : G := (node82 a b)⁻¹
def node84 (a b : G) : G := (node83 a b) * (node54 a b)
def node85 (a b : G) : G := (node84 a b) * (node82 a b)
def node86 (a b : G) : G := (node69 a b) * (node54 a b)
def node87 (a b : G) : G := (node69 a b) * (node69 a b)
def node88 (a b : G) : G := (node87 a b) * (node69 a b)
def node89 (a b : G) : G := (node86 a b) * (node88 a b)
def node90 (a b : G) : G := (node89 a b)⁻¹
def node91 (a b : G) : G := (node90 a b) * (node54 a b)
def node92 (a b : G) : G := (node91 a b) * (node89 a b)
def node93 (a b : G) : G := (node69 a b) * (node54 a b)
def node94 (a b : G) : G := (node69 a b) * (node69 a b)
def node95 (a b : G) : G := (node94 a b) * (node94 a b)
def node96 (a b : G) : G := (node93 a b) * (node95 a b)
def node97 (a b : G) : G := (node96 a b)⁻¹
def node98 (a b : G) : G := (node97 a b) * (node54 a b)
def node99 (a b : G) : G := (node98 a b) * (node96 a b)
def node100 (a b : G) : G := (node69 a b) * (node54 a b)
def node101 (a b : G) : G := (node69 a b) * (node69 a b)
def node102 (a b : G) : G := (node101 a b) * (node101 a b)
def node103 (a b : G) : G := (node102 a b) * (node69 a b)
def node104 (a b : G) : G := (node100 a b) * (node103 a b)
def node105 (a b : G) : G := (node104 a b)⁻¹
def node106 (a b : G) : G := (node105 a b) * (node54 a b)
def node107 (a b : G) : G := (node106 a b) * (node104 a b)
def node108 (a b : G) : G := (node69 a b) * (node54 a b)
def node109 (a b : G) : G := (node69 a b) * (node69 a b)
def node110 (a b : G) : G := (node109 a b) * (node69 a b)
def node111 (a b : G) : G := (node110 a b) * (node110 a b)
def node112 (a b : G) : G := (node108 a b) * (node111 a b)
def node113 (a b : G) : G := (node112 a b)⁻¹
def node114 (a b : G) : G := (node113 a b) * (node54 a b)
def node115 (a b : G) : G := (node114 a b) * (node112 a b)
def node116 (a b : G) : G := (node6 a b) * (node6 a b)
def node117 (a b : G) : G := (node116 a b) * (node116 a b)
def node118 (a b : G) : G := (node117 a b) * (node6 a b)
def node119 (a b : G) : G := (node118 a b) * (node19 a b)
def node120 (a b : G) : G := (node118 a b)⁻¹
def node121 (a b : G) : G := (node119 a b) * (node120 a b)
def node122 (a b : G) : G := (node121 a b) * (node54 a b)
def node123 (a b : G) : G := (node122 a b) * (node118 a b)
def node124 (a b : G) : G := (node123 a b)⁻¹
def node125 (a b : G) : G := (node123 a b) * (node13 a b)
def node126 (a b : G) : G := (node125 a b) * (node124 a b)
def node127 (a b : G) : G := (node126 a b) * (node126 a b)
def node128 (a b : G) : G := (node127 a b)⁻¹
def node129 (a b : G) : G := (node128 a b) * (node92 a b)
def node130 (a b : G) : G := (node129 a b) * (node127 a b)
def node131 (a b : G) : G := (node79 a b) * (node85 a b)
def node132 (a b : G) : G := (node130 a b)⁻¹
def node133 (a b : G) : G := (node131 a b)⁻¹
def node134 (a b : G) : G := (node132 a b) * (node133 a b)
def node135 (a b : G) : G := (node134 a b) * (node130 a b)
def node136 (a b : G) : G := (node135 a b) * (node131 a b)
def node137 (a b : G) : G := (node126 a b) * (node126 a b)
def node138 (a b : G) : G := (node137 a b) * (node137 a b)
def node139 (a b : G) : G := (node138 a b) * (node126 a b)
def node140 (a b : G) : G := (node139 a b)⁻¹
def node141 (a b : G) : G := (node140 a b) * (node92 a b)
def node142 (a b : G) : G := (node141 a b) * (node139 a b)
def node143 (a b : G) : G := (node79 a b) * (node85 a b)
def node144 (a b : G) : G := (node142 a b)⁻¹
def node145 (a b : G) : G := (node143 a b)⁻¹
def node146 (a b : G) : G := (node144 a b) * (node145 a b)
def node147 (a b : G) : G := (node146 a b) * (node142 a b)
def node148 (a b : G) : G := (node147 a b) * (node143 a b)
def node149 (a b : G) : G := (node136 a b) * (node148 a b)
def node150 (a b : G) : G := (node149 a b)⁻¹
def node151 (a b : G) : G := (node150 a b) * (node115 a b)
def node152 (a b : G) : G := (node151 a b) * (node149 a b)
def node153 (a b : G) : G := (node99 a b) * (node107 a b)
def node154 (a b : G) : G := (node152 a b)⁻¹
def node155 (a b : G) : G := (node153 a b)⁻¹
def node156 (a b : G) : G := (node154 a b) * (node155 a b)
def node157 (a b : G) : G := (node156 a b) * (node152 a b)
def node158 (a b : G) : G := (node157 a b) * (node153 a b)
def node159 (a b : G) : G := (node148 a b) * (node136 a b)
def node160 (a b : G) : G := (node159 a b)⁻¹
def node161 (a b : G) : G := (node160 a b) * (node115 a b)
def node162 (a b : G) : G := (node161 a b) * (node159 a b)
def node163 (a b : G) : G := (node99 a b) * (node107 a b)
def node164 (a b : G) : G := (node162 a b)⁻¹
def node165 (a b : G) : G := (node163 a b)⁻¹
def node166 (a b : G) : G := (node164 a b) * (node165 a b)
def node167 (a b : G) : G := (node166 a b) * (node162 a b)
def node168 (a b : G) : G := (node167 a b) * (node163 a b)
def node169 (a b : G) : G := (node158 a b) * (node168 a b)
def node170 (a b : G) : G := (node136 a b) * (node148 a b)
def node171 (a b : G) : G := (node170 a b) * (node170 a b)
def node172 (a b : G) : G := (node171 a b) * (node171 a b)
def node173 (a b : G) : G := (node172 a b)⁻¹
def node174 (a b : G) : G := (node173 a b) * (node115 a b)
def node175 (a b : G) : G := (node174 a b) * (node172 a b)
def node176 (a b : G) : G := (node99 a b) * (node107 a b)
def node177 (a b : G) : G := (node175 a b)⁻¹
def node178 (a b : G) : G := (node176 a b)⁻¹
def node179 (a b : G) : G := (node177 a b) * (node178 a b)
def node180 (a b : G) : G := (node179 a b) * (node175 a b)
def node181 (a b : G) : G := (node180 a b) * (node176 a b)
def node182 (a b : G) : G := (node136 a b) * (node148 a b)
def node183 (a b : G) : G := (node182 a b) * (node182 a b)
def node184 (a b : G) : G := (node183 a b) * (node182 a b)
def node185 (a b : G) : G := (node184 a b) * (node148 a b)
def node186 (a b : G) : G := (node185 a b) * (node136 a b)
def node187 (a b : G) : G := (node186 a b)⁻¹
def node188 (a b : G) : G := (node187 a b) * (node115 a b)
def node189 (a b : G) : G := (node188 a b) * (node186 a b)
def node190 (a b : G) : G := (node169 a b) * (node181 a b)
def node191 (a b : G) : G := (node190 a b) * (node189 a b)
def node192 (a b : G) : G := (node191 a b) * (node191 a b)
def node193 (a b : G) : G := (node192 a b) * (node191 a b)
def node194 (a b : G) : G := (node193 a b) * (node181 a b)
def node195 (a b : G) : G := (node194 a b) * (node189 a b)
def node196 (a b : G) : G := (node195 a b) * (node195 a b)
def node197 (a b : G) : G := (node196 a b) * (node196 a b)
def node198 (a b : G) : G := (node197 a b)⁻¹
def node199 (a b : G) : G := (node198 a b) * (node189 a b)
def node200 (a b : G) : G := (node199 a b) * (node197 a b)
def node201 (a b : G) : G := (node195 a b)⁻¹
def node202 (a b : G) : G := (node201 a b) * (node200 a b)
def node203 (a b : G) : G := (node202 a b) * (node195 a b)
def node204 (a b : G) : G := (node203 a b) * (node200 a b)
def node205 (a b : G) : G := (node204 a b) * (node189 a b)
def node206 (a b : G) : G := (node205 a b) * (node200 a b)
def node207 (a b : G) : G := (node206 a b) * (node203 a b)
def node208 (a b : G) : G := (node189 a b) * (node200 a b)
def node209 (a b : G) : G := (node208 a b) * (node207 a b)
def node210 (a b : G) : G := (node209 a b) * (node200 a b)
def node211 (a b : G) : G := (node210 a b) * (node189 a b)
def node212 (a b : G) : G := (node54 a b) * (node74 a b)
def node213 (a b : G) : G := (node212 a b) * (node79 a b)
def node214 (a b : G) : G := (node213 a b) * (node85 a b)
def node215 (a b : G) : G := (node214 a b) * (node92 a b)
def node216 (a b : G) : G := (node215 a b) * (node99 a b)
def node217 (a b : G) : G := (node216 a b) * (node107 a b)
def node218 (a b : G) : G := (node217 a b) * (node115 a b)
def node219 (a b : G) : G := (node92 a b) * (node211 a b)
def node220 (a b : G) : G := (node219 a b) * (node207 a b)
def node221 (a b : G) : G := (node220 a b) * (node19 a b)
def node222 (a b : G) : G := (node218 a b) * (node218 a b)
def node223 (a b : G) : G := (node222 a b) * (node218 a b)
def node224 (a b : G) : G := (node223 a b) * (node223 a b)
def node225 (a b : G) : G := (node224 a b) * (node218 a b)
def node226 (a b : G) : G := (node225 a b) * (node221 a b)
def node227 (a b : G) : G := (node226 a b) * (node226 a b)
def node228 (a b : G) : G := (node227 a b) * (node226 a b)
def node229 (a b : G) : G := (node228 a b) * (node228 a b)
def node230 (a b : G) : G := (node229 a b) * (node226 a b)
def node231 (a b : G) : G := (node230 a b) * (node230 a b)
def node232 (a b : G) : G := (node231 a b) * (node226 a b)
def node233 (a b : G) : G := (node54 a b) * (node74 a b)
def node234 (a b : G) : G := (node221 a b) * (node218 a b)
def node235 (a b : G) : G := (node234 a b) * (node234 a b)
def node236 (a b : G) : G := (node235 a b) * (node235 a b)
def node237 (a b : G) : G := (node236 a b) * (node234 a b)
def node238 (a b : G) : G := (node237 a b) * (node237 a b)
def node239 (a b : G) : G := (node238 a b)⁻¹
def node240 (a b : G) : G := (node239 a b) * (node233 a b)
def node241 (a b : G) : G := (node240 a b) * (node238 a b)

theorem node0_spec (a b : G) : node0 a b = 1 := rfl
omit [Group G] in
theorem node1_spec (a b : G) : node1 a b = a := rfl
omit [Group G] in
theorem node2_spec (a b : G) : node2 a b = b := rfl
theorem node3_spec (a b : G) : node3 a b = (node1 a b) * (node1 a b) := rfl
theorem node4_spec (a b : G) : node4 a b = (node2 a b) * (node2 a b) := rfl
theorem node5_spec (a b : G) : node5 a b = (node4 a b) * (node2 a b) := rfl
theorem node6_spec (a b : G) : node6 a b = (node1 a b) * (node2 a b) := rfl
theorem node7_spec (a b : G) : node7 a b = (node6 a b) * (node6 a b) := rfl
theorem node8_spec (a b : G) : node8 a b = (node7 a b) * (node6 a b) := rfl
theorem node9_spec (a b : G) : node9 a b = (node8 a b) * (node8 a b) := rfl
theorem node10_spec (a b : G) : node10 a b = (node9 a b) * (node6 a b) := rfl
theorem node11_spec (a b : G) : node11 a b = (node10 a b) * (node10 a b) := rfl
theorem node12_spec (a b : G) : node12 a b = (node11 a b) * (node6 a b) := rfl
theorem node13_spec (a b : G) : node13 a b = (node12 a b) * (node2 a b) := rfl
theorem node14_spec (a b : G) : node14 a b = (node13 a b) * (node13 a b) := rfl
theorem node15_spec (a b : G) : node15 a b = (node14 a b) * (node14 a b) := rfl
theorem node16_spec (a b : G) : node16 a b = (node15 a b) * (node15 a b) := rfl
theorem node17_spec (a b : G) : node17 a b = (node16 a b) * (node13 a b) := rfl
theorem node18_spec (a b : G) : node18 a b = (node17 a b) * (node17 a b) := rfl
theorem node19_spec (a b : G) : node19 a b = (node18 a b) * (node13 a b) := rfl
theorem node20_spec (a b : G) : node20 a b = (node1 a b) * (node19 a b) := rfl
theorem node21_spec (a b : G) : node21 a b = (node20 a b) * (node20 a b) := rfl
theorem node22_spec (a b : G) : node22 a b = (node21 a b) * (node20 a b) := rfl
theorem node23_spec (a b : G) : node23 a b = (node13 a b) * (node13 a b) := rfl
theorem node24_spec (a b : G) : node24 a b = (node23 a b) * (node13 a b) := rfl
theorem node25_spec (a b : G) : node25 a b = (node22 a b) * (node24 a b) := rfl
theorem node26_spec (a b : G) : node26 a b = (node25 a b) * (node25 a b) := rfl
theorem node27_spec (a b : G) : node27 a b = (node26 a b) * (node26 a b) := rfl
theorem node28_spec (a b : G) : node28 a b = (node27 a b) * (node25 a b) := rfl
theorem node29_spec (a b : G) : node29 a b = (node28 a b) * (node28 a b) := rfl
theorem node30_spec (a b : G) : node30 a b = (node13 a b)⁻¹ := rfl
theorem node31_spec (a b : G) : node31 a b = (node30 a b) * (node29 a b) := rfl
theorem node32_spec (a b : G) : node32 a b = (node31 a b) * (node13 a b) := rfl
theorem node33_spec (a b : G) : node33 a b = (node32 a b) * (node22 a b) := rfl
theorem node34_spec (a b : G) : node34 a b = (node33 a b) * (node33 a b) := rfl
theorem node35_spec (a b : G) : node35 a b = (node34 a b) * (node33 a b) := rfl
theorem node36_spec (a b : G) : node36 a b = (node35 a b) * (node35 a b) := rfl
theorem node37_spec (a b : G) : node37 a b = (node36 a b) * (node22 a b) := rfl
theorem node38_spec (a b : G) : node38 a b = (node33 a b) * (node33 a b) := rfl
theorem node39_spec (a b : G) : node39 a b = (node38 a b) * (node33 a b) := rfl
theorem node40_spec (a b : G) : node40 a b = (node37 a b) * (node39 a b) := rfl
theorem node41_spec (a b : G) : node41 a b = (node40 a b) * (node40 a b) := rfl
theorem node42_spec (a b : G) : node42 a b = (node41 a b) * (node32 a b) := rfl
theorem node43_spec (a b : G) : node43 a b = (node42 a b) * (node22 a b) := rfl
theorem node44_spec (a b : G) : node44 a b = (node32 a b) * (node32 a b) := rfl
theorem node45_spec (a b : G) : node45 a b = (node43 a b) * (node44 a b) := rfl
theorem node46_spec (a b : G) : node46 a b = (node45 a b) * (node22 a b) := rfl
theorem node47_spec (a b : G) : node47 a b = (node46 a b) * (node46 a b) := rfl
theorem node48_spec (a b : G) : node48 a b = (node47 a b) * (node47 a b) := rfl
theorem node49_spec (a b : G) : node49 a b = (node48 a b) * (node46 a b) := rfl
theorem node50_spec (a b : G) : node50 a b = (node33 a b) * (node33 a b) := rfl
theorem node51_spec (a b : G) : node51 a b = (node50 a b) * (node50 a b) := rfl
theorem node52_spec (a b : G) : node52 a b = (node51 a b)⁻¹ := rfl
theorem node53_spec (a b : G) : node53 a b = (node52 a b) * (node49 a b) := rfl
theorem node54_spec (a b : G) : node54 a b = (node53 a b) * (node51 a b) := rfl
theorem node55_spec (a b : G) : node55 a b = (node33 a b) * (node33 a b) := rfl
theorem node56_spec (a b : G) : node56 a b = (node55 a b) * (node55 a b) := rfl
theorem node57_spec (a b : G) : node57 a b = (node56 a b) * (node56 a b) := rfl
theorem node58_spec (a b : G) : node58 a b = (node57 a b) * (node22 a b) := rfl
theorem node59_spec (a b : G) : node59 a b = (node33 a b) * (node33 a b) := rfl
theorem node60_spec (a b : G) : node60 a b = (node59 a b) * (node33 a b) := rfl
theorem node61_spec (a b : G) : node61 a b = (node58 a b) * (node60 a b) := rfl
theorem node62_spec (a b : G) : node62 a b = (node32 a b) * (node22 a b) := rfl
theorem node63_spec (a b : G) : node63 a b = (node32 a b) * (node32 a b) := rfl
theorem node64_spec (a b : G) : node64 a b = (node62 a b) * (node63 a b) := rfl
theorem node65_spec (a b : G) : node65 a b = (node64 a b) * (node22 a b) := rfl
theorem node66_spec (a b : G) : node66 a b = (node65 a b) * (node65 a b) := rfl
theorem node67_spec (a b : G) : node67 a b = (node66 a b)⁻¹ := rfl
theorem node68_spec (a b : G) : node68 a b = (node67 a b) * (node61 a b) := rfl
theorem node69_spec (a b : G) : node69 a b = (node68 a b) * (node66 a b) := rfl
theorem node70_spec (a b : G) : node70 a b = (node69 a b) * (node54 a b) := rfl
theorem node71_spec (a b : G) : node71 a b = (node70 a b) * (node0 a b) := rfl
theorem node72_spec (a b : G) : node72 a b = (node71 a b)⁻¹ := rfl
theorem node73_spec (a b : G) : node73 a b = (node72 a b) * (node54 a b) := rfl
theorem node74_spec (a b : G) : node74 a b = (node73 a b) * (node71 a b) := rfl
theorem node75_spec (a b : G) : node75 a b = (node69 a b) * (node54 a b) := rfl
theorem node76_spec (a b : G) : node76 a b = (node75 a b) * (node69 a b) := rfl
theorem node77_spec (a b : G) : node77 a b = (node76 a b)⁻¹ := rfl
theorem node78_spec (a b : G) : node78 a b = (node77 a b) * (node54 a b) := rfl
theorem node79_spec (a b : G) : node79 a b = (node78 a b) * (node76 a b) := rfl
theorem node80_spec (a b : G) : node80 a b = (node69 a b) * (node54 a b) := rfl
theorem node81_spec (a b : G) : node81 a b = (node69 a b) * (node69 a b) := rfl
theorem node82_spec (a b : G) : node82 a b = (node80 a b) * (node81 a b) := rfl
theorem node83_spec (a b : G) : node83 a b = (node82 a b)⁻¹ := rfl
theorem node84_spec (a b : G) : node84 a b = (node83 a b) * (node54 a b) := rfl
theorem node85_spec (a b : G) : node85 a b = (node84 a b) * (node82 a b) := rfl
theorem node86_spec (a b : G) : node86 a b = (node69 a b) * (node54 a b) := rfl
theorem node87_spec (a b : G) : node87 a b = (node69 a b) * (node69 a b) := rfl
theorem node88_spec (a b : G) : node88 a b = (node87 a b) * (node69 a b) := rfl
theorem node89_spec (a b : G) : node89 a b = (node86 a b) * (node88 a b) := rfl
theorem node90_spec (a b : G) : node90 a b = (node89 a b)⁻¹ := rfl
theorem node91_spec (a b : G) : node91 a b = (node90 a b) * (node54 a b) := rfl
theorem node92_spec (a b : G) : node92 a b = (node91 a b) * (node89 a b) := rfl
theorem node93_spec (a b : G) : node93 a b = (node69 a b) * (node54 a b) := rfl
theorem node94_spec (a b : G) : node94 a b = (node69 a b) * (node69 a b) := rfl
theorem node95_spec (a b : G) : node95 a b = (node94 a b) * (node94 a b) := rfl
theorem node96_spec (a b : G) : node96 a b = (node93 a b) * (node95 a b) := rfl
theorem node97_spec (a b : G) : node97 a b = (node96 a b)⁻¹ := rfl
theorem node98_spec (a b : G) : node98 a b = (node97 a b) * (node54 a b) := rfl
theorem node99_spec (a b : G) : node99 a b = (node98 a b) * (node96 a b) := rfl
theorem node100_spec (a b : G) : node100 a b = (node69 a b) * (node54 a b) := rfl
theorem node101_spec (a b : G) : node101 a b = (node69 a b) * (node69 a b) := rfl
theorem node102_spec (a b : G) : node102 a b = (node101 a b) * (node101 a b) := rfl
theorem node103_spec (a b : G) : node103 a b = (node102 a b) * (node69 a b) := rfl
theorem node104_spec (a b : G) : node104 a b = (node100 a b) * (node103 a b) := rfl
theorem node105_spec (a b : G) : node105 a b = (node104 a b)⁻¹ := rfl
theorem node106_spec (a b : G) : node106 a b = (node105 a b) * (node54 a b) := rfl
theorem node107_spec (a b : G) : node107 a b = (node106 a b) * (node104 a b) := rfl
theorem node108_spec (a b : G) : node108 a b = (node69 a b) * (node54 a b) := rfl
theorem node109_spec (a b : G) : node109 a b = (node69 a b) * (node69 a b) := rfl
theorem node110_spec (a b : G) : node110 a b = (node109 a b) * (node69 a b) := rfl
theorem node111_spec (a b : G) : node111 a b = (node110 a b) * (node110 a b) := rfl
theorem node112_spec (a b : G) : node112 a b = (node108 a b) * (node111 a b) := rfl
theorem node113_spec (a b : G) : node113 a b = (node112 a b)⁻¹ := rfl
theorem node114_spec (a b : G) : node114 a b = (node113 a b) * (node54 a b) := rfl
theorem node115_spec (a b : G) : node115 a b = (node114 a b) * (node112 a b) := rfl
theorem node116_spec (a b : G) : node116 a b = (node6 a b) * (node6 a b) := rfl
theorem node117_spec (a b : G) : node117 a b = (node116 a b) * (node116 a b) := rfl
theorem node118_spec (a b : G) : node118 a b = (node117 a b) * (node6 a b) := rfl
theorem node119_spec (a b : G) : node119 a b = (node118 a b) * (node19 a b) := rfl
theorem node120_spec (a b : G) : node120 a b = (node118 a b)⁻¹ := rfl
theorem node121_spec (a b : G) : node121 a b = (node119 a b) * (node120 a b) := rfl
theorem node122_spec (a b : G) : node122 a b = (node121 a b) * (node54 a b) := rfl
theorem node123_spec (a b : G) : node123 a b = (node122 a b) * (node118 a b) := rfl
theorem node124_spec (a b : G) : node124 a b = (node123 a b)⁻¹ := rfl
theorem node125_spec (a b : G) : node125 a b = (node123 a b) * (node13 a b) := rfl
theorem node126_spec (a b : G) : node126 a b = (node125 a b) * (node124 a b) := rfl
theorem node127_spec (a b : G) : node127 a b = (node126 a b) * (node126 a b) := rfl
theorem node128_spec (a b : G) : node128 a b = (node127 a b)⁻¹ := rfl
theorem node129_spec (a b : G) : node129 a b = (node128 a b) * (node92 a b) := rfl
theorem node130_spec (a b : G) : node130 a b = (node129 a b) * (node127 a b) := rfl
theorem node131_spec (a b : G) : node131 a b = (node79 a b) * (node85 a b) := rfl
theorem node132_spec (a b : G) : node132 a b = (node130 a b)⁻¹ := rfl
theorem node133_spec (a b : G) : node133 a b = (node131 a b)⁻¹ := rfl
theorem node134_spec (a b : G) : node134 a b = (node132 a b) * (node133 a b) := rfl
theorem node135_spec (a b : G) : node135 a b = (node134 a b) * (node130 a b) := rfl
theorem node136_spec (a b : G) : node136 a b = (node135 a b) * (node131 a b) := rfl
theorem node137_spec (a b : G) : node137 a b = (node126 a b) * (node126 a b) := rfl
theorem node138_spec (a b : G) : node138 a b = (node137 a b) * (node137 a b) := rfl
theorem node139_spec (a b : G) : node139 a b = (node138 a b) * (node126 a b) := rfl
theorem node140_spec (a b : G) : node140 a b = (node139 a b)⁻¹ := rfl
theorem node141_spec (a b : G) : node141 a b = (node140 a b) * (node92 a b) := rfl
theorem node142_spec (a b : G) : node142 a b = (node141 a b) * (node139 a b) := rfl
theorem node143_spec (a b : G) : node143 a b = (node79 a b) * (node85 a b) := rfl
theorem node144_spec (a b : G) : node144 a b = (node142 a b)⁻¹ := rfl
theorem node145_spec (a b : G) : node145 a b = (node143 a b)⁻¹ := rfl
theorem node146_spec (a b : G) : node146 a b = (node144 a b) * (node145 a b) := rfl
theorem node147_spec (a b : G) : node147 a b = (node146 a b) * (node142 a b) := rfl
theorem node148_spec (a b : G) : node148 a b = (node147 a b) * (node143 a b) := rfl
theorem node149_spec (a b : G) : node149 a b = (node136 a b) * (node148 a b) := rfl
theorem node150_spec (a b : G) : node150 a b = (node149 a b)⁻¹ := rfl
theorem node151_spec (a b : G) : node151 a b = (node150 a b) * (node115 a b) := rfl
theorem node152_spec (a b : G) : node152 a b = (node151 a b) * (node149 a b) := rfl
theorem node153_spec (a b : G) : node153 a b = (node99 a b) * (node107 a b) := rfl
theorem node154_spec (a b : G) : node154 a b = (node152 a b)⁻¹ := rfl
theorem node155_spec (a b : G) : node155 a b = (node153 a b)⁻¹ := rfl
theorem node156_spec (a b : G) : node156 a b = (node154 a b) * (node155 a b) := rfl
theorem node157_spec (a b : G) : node157 a b = (node156 a b) * (node152 a b) := rfl
theorem node158_spec (a b : G) : node158 a b = (node157 a b) * (node153 a b) := rfl
theorem node159_spec (a b : G) : node159 a b = (node148 a b) * (node136 a b) := rfl
theorem node160_spec (a b : G) : node160 a b = (node159 a b)⁻¹ := rfl
theorem node161_spec (a b : G) : node161 a b = (node160 a b) * (node115 a b) := rfl
theorem node162_spec (a b : G) : node162 a b = (node161 a b) * (node159 a b) := rfl
theorem node163_spec (a b : G) : node163 a b = (node99 a b) * (node107 a b) := rfl
theorem node164_spec (a b : G) : node164 a b = (node162 a b)⁻¹ := rfl
theorem node165_spec (a b : G) : node165 a b = (node163 a b)⁻¹ := rfl
theorem node166_spec (a b : G) : node166 a b = (node164 a b) * (node165 a b) := rfl
theorem node167_spec (a b : G) : node167 a b = (node166 a b) * (node162 a b) := rfl
theorem node168_spec (a b : G) : node168 a b = (node167 a b) * (node163 a b) := rfl
theorem node169_spec (a b : G) : node169 a b = (node158 a b) * (node168 a b) := rfl
theorem node170_spec (a b : G) : node170 a b = (node136 a b) * (node148 a b) := rfl
theorem node171_spec (a b : G) : node171 a b = (node170 a b) * (node170 a b) := rfl
theorem node172_spec (a b : G) : node172 a b = (node171 a b) * (node171 a b) := rfl
theorem node173_spec (a b : G) : node173 a b = (node172 a b)⁻¹ := rfl
theorem node174_spec (a b : G) : node174 a b = (node173 a b) * (node115 a b) := rfl
theorem node175_spec (a b : G) : node175 a b = (node174 a b) * (node172 a b) := rfl
theorem node176_spec (a b : G) : node176 a b = (node99 a b) * (node107 a b) := rfl
theorem node177_spec (a b : G) : node177 a b = (node175 a b)⁻¹ := rfl
theorem node178_spec (a b : G) : node178 a b = (node176 a b)⁻¹ := rfl
theorem node179_spec (a b : G) : node179 a b = (node177 a b) * (node178 a b) := rfl
theorem node180_spec (a b : G) : node180 a b = (node179 a b) * (node175 a b) := rfl
theorem node181_spec (a b : G) : node181 a b = (node180 a b) * (node176 a b) := rfl
theorem node182_spec (a b : G) : node182 a b = (node136 a b) * (node148 a b) := rfl
theorem node183_spec (a b : G) : node183 a b = (node182 a b) * (node182 a b) := rfl
theorem node184_spec (a b : G) : node184 a b = (node183 a b) * (node182 a b) := rfl
theorem node185_spec (a b : G) : node185 a b = (node184 a b) * (node148 a b) := rfl
theorem node186_spec (a b : G) : node186 a b = (node185 a b) * (node136 a b) := rfl
theorem node187_spec (a b : G) : node187 a b = (node186 a b)⁻¹ := rfl
theorem node188_spec (a b : G) : node188 a b = (node187 a b) * (node115 a b) := rfl
theorem node189_spec (a b : G) : node189 a b = (node188 a b) * (node186 a b) := rfl
theorem node190_spec (a b : G) : node190 a b = (node169 a b) * (node181 a b) := rfl
theorem node191_spec (a b : G) : node191 a b = (node190 a b) * (node189 a b) := rfl
theorem node192_spec (a b : G) : node192 a b = (node191 a b) * (node191 a b) := rfl
theorem node193_spec (a b : G) : node193 a b = (node192 a b) * (node191 a b) := rfl
theorem node194_spec (a b : G) : node194 a b = (node193 a b) * (node181 a b) := rfl
theorem node195_spec (a b : G) : node195 a b = (node194 a b) * (node189 a b) := rfl
theorem node196_spec (a b : G) : node196 a b = (node195 a b) * (node195 a b) := rfl
theorem node197_spec (a b : G) : node197 a b = (node196 a b) * (node196 a b) := rfl
theorem node198_spec (a b : G) : node198 a b = (node197 a b)⁻¹ := rfl
theorem node199_spec (a b : G) : node199 a b = (node198 a b) * (node189 a b) := rfl
theorem node200_spec (a b : G) : node200 a b = (node199 a b) * (node197 a b) := rfl
theorem node201_spec (a b : G) : node201 a b = (node195 a b)⁻¹ := rfl
theorem node202_spec (a b : G) : node202 a b = (node201 a b) * (node200 a b) := rfl
theorem node203_spec (a b : G) : node203 a b = (node202 a b) * (node195 a b) := rfl
theorem node204_spec (a b : G) : node204 a b = (node203 a b) * (node200 a b) := rfl
theorem node205_spec (a b : G) : node205 a b = (node204 a b) * (node189 a b) := rfl
theorem node206_spec (a b : G) : node206 a b = (node205 a b) * (node200 a b) := rfl
theorem node207_spec (a b : G) : node207 a b = (node206 a b) * (node203 a b) := rfl
theorem node208_spec (a b : G) : node208 a b = (node189 a b) * (node200 a b) := rfl
theorem node209_spec (a b : G) : node209 a b = (node208 a b) * (node207 a b) := rfl
theorem node210_spec (a b : G) : node210 a b = (node209 a b) * (node200 a b) := rfl
theorem node211_spec (a b : G) : node211 a b = (node210 a b) * (node189 a b) := rfl
theorem node212_spec (a b : G) : node212 a b = (node54 a b) * (node74 a b) := rfl
theorem node213_spec (a b : G) : node213 a b = (node212 a b) * (node79 a b) := rfl
theorem node214_spec (a b : G) : node214 a b = (node213 a b) * (node85 a b) := rfl
theorem node215_spec (a b : G) : node215 a b = (node214 a b) * (node92 a b) := rfl
theorem node216_spec (a b : G) : node216 a b = (node215 a b) * (node99 a b) := rfl
theorem node217_spec (a b : G) : node217 a b = (node216 a b) * (node107 a b) := rfl
theorem node218_spec (a b : G) : node218 a b = (node217 a b) * (node115 a b) := rfl
theorem node219_spec (a b : G) : node219 a b = (node92 a b) * (node211 a b) := rfl
theorem node220_spec (a b : G) : node220 a b = (node219 a b) * (node207 a b) := rfl
theorem node221_spec (a b : G) : node221 a b = (node220 a b) * (node19 a b) := rfl
theorem node222_spec (a b : G) : node222 a b = (node218 a b) * (node218 a b) := rfl
theorem node223_spec (a b : G) : node223 a b = (node222 a b) * (node218 a b) := rfl
theorem node224_spec (a b : G) : node224 a b = (node223 a b) * (node223 a b) := rfl
theorem node225_spec (a b : G) : node225 a b = (node224 a b) * (node218 a b) := rfl
theorem node226_spec (a b : G) : node226 a b = (node225 a b) * (node221 a b) := rfl
theorem node227_spec (a b : G) : node227 a b = (node226 a b) * (node226 a b) := rfl
theorem node228_spec (a b : G) : node228 a b = (node227 a b) * (node226 a b) := rfl
theorem node229_spec (a b : G) : node229 a b = (node228 a b) * (node228 a b) := rfl
theorem node230_spec (a b : G) : node230 a b = (node229 a b) * (node226 a b) := rfl
theorem node231_spec (a b : G) : node231 a b = (node230 a b) * (node230 a b) := rfl
theorem node232_spec (a b : G) : node232 a b = (node231 a b) * (node226 a b) := rfl
theorem node233_spec (a b : G) : node233 a b = (node54 a b) * (node74 a b) := rfl
theorem node234_spec (a b : G) : node234 a b = (node221 a b) * (node218 a b) := rfl
theorem node235_spec (a b : G) : node235 a b = (node234 a b) * (node234 a b) := rfl
theorem node236_spec (a b : G) : node236 a b = (node235 a b) * (node235 a b) := rfl
theorem node237_spec (a b : G) : node237 a b = (node236 a b) * (node234 a b) := rfl
theorem node238_spec (a b : G) : node238 a b = (node237 a b) * (node237 a b) := rfl
theorem node239_spec (a b : G) : node239 a b = (node238 a b)⁻¹ := rfl
theorem node240_spec (a b : G) : node240 a b = (node239 a b) * (node233 a b) := rfl
theorem node241_spec (a b : G) : node241 a b = (node240 a b) * (node238 a b) := rfl
private theorem power_two (x : G) : x ^ 2 = x * x := pow_two x
private theorem power_3 (x : G) : x ^ 3 = x ^ 1 * x ^ 1 * x := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_4 (x : G) : x ^ 4 = x ^ 2 * x ^ 2 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_5 (x : G) : x ^ 5 = x ^ 2 * x ^ 2 * x := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_6 (x : G) : x ^ 6 = x ^ 3 * x ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_7 (x : G) : x ^ 7 = x ^ 3 * x ^ 3 * x := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_8 (x : G) : x ^ 8 = x ^ 4 * x ^ 4 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_10 (x : G) : x ^ 10 = x ^ 5 * x ^ 5 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_15 (x : G) : x ^ 15 = x ^ 7 * x ^ 7 * x := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_19 (x : G) : x ^ 19 = x ^ 9 * x ^ 9 * x := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
private theorem power_9 (x : G) : x ^ 9 = x ^ 4 * x ^ 4 * x := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem recoveredA_eq_node (a b : G) : recoveredA (generatorWords a b) = node232 a b := by
  simp only [recoveredA, recoveredR, recoveredS, generatorWords, wordConjugate, wordCommutator, Fin.val_ofNat, Nat.reduceMod, power_9, power_19, power_15, power_10, power_8, power_7, power_6, power_5, power_4, power_3, power_two, pow_one, pow_zero, inv_inv, node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13, node14, node15, node16, node17, node18, node19, node20, node21, node22, node23, node24, node25, node26, node27, node28, node29, node30, node31, node32, node33, node34, node35, node36, node37, node38, node39, node40, node41, node42, node43, node44, node45, node46, node47, node48, node49, node50, node51, node52, node53, node54, node55, node56, node57, node58, node59, node60, node61, node62, node63, node64, node65, node66, node67, node68, node69, node70, node71, node72, node73, node74, node75, node76, node77, node78, node79, node80, node81, node82, node83, node84, node85, node86, node87, node88, node89, node90, node91, node92, node93, node94, node95, node96, node97, node98, node99, node100, node101, node102, node103, node104, node105, node106, node107, node108, node109, node110, node111, node112, node113, node114, node115, node116, node117, node118, node119, node120, node121, node122, node123, node124, node125, node126, node127, node128, node129, node130, node131, node132, node133, node134, node135, node136, node137, node138, node139, node140, node141, node142, node143, node144, node145, node146, node147, node148, node149, node150, node151, node152, node153, node154, node155, node156, node157, node158, node159, node160, node161, node162, node163, node164, node165, node166, node167, node168, node169, node170, node171, node172, node173, node174, node175, node176, node177, node178, node179, node180, node181, node182, node183, node184, node185, node186, node187, node188, node189, node190, node191, node192, node193, node194, node195, node196, node197, node198, node199, node200, node201, node202, node203, node204, node205, node206, node207, node208, node209, node210, node211, node212, node213, node214, node215, node216, node217, node218, node219, node220, node221, node222, node223, node224, node225, node226, node227, node228, node229, node230, node231, node232, node233, node234, node235, node236, node237, node238, node239, node240, node241]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem recoveredB_eq_node (a b : G) : recoveredB (generatorWords a b) = node241 a b := by
  simp only [recoveredB, recoveredR, recoveredS, generatorWords, wordConjugate, wordCommutator, Fin.val_ofNat, Nat.reduceMod, power_9, power_19, power_15, power_10, power_8, power_7, power_6, power_5, power_4, power_3, power_two, pow_one, pow_zero, inv_inv, node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13, node14, node15, node16, node17, node18, node19, node20, node21, node22, node23, node24, node25, node26, node27, node28, node29, node30, node31, node32, node33, node34, node35, node36, node37, node38, node39, node40, node41, node42, node43, node44, node45, node46, node47, node48, node49, node50, node51, node52, node53, node54, node55, node56, node57, node58, node59, node60, node61, node62, node63, node64, node65, node66, node67, node68, node69, node70, node71, node72, node73, node74, node75, node76, node77, node78, node79, node80, node81, node82, node83, node84, node85, node86, node87, node88, node89, node90, node91, node92, node93, node94, node95, node96, node97, node98, node99, node100, node101, node102, node103, node104, node105, node106, node107, node108, node109, node110, node111, node112, node113, node114, node115, node116, node117, node118, node119, node120, node121, node122, node123, node124, node125, node126, node127, node128, node129, node130, node131, node132, node133, node134, node135, node136, node137, node138, node139, node140, node141, node142, node143, node144, node145, node146, node147, node148, node149, node150, node151, node152, node153, node154, node155, node156, node157, node158, node159, node160, node161, node162, node163, node164, node165, node166, node167, node168, node169, node170, node171, node172, node173, node174, node175, node176, node177, node178, node179, node180, node181, node182, node183, node184, node185, node186, node187, node188, node189, node190, node191, node192, node193, node194, node195, node196, node197, node198, node199, node200, node201, node202, node203, node204, node205, node206, node207, node208, node209, node210, node211, node212, node213, node214, node215, node216, node217, node218, node219, node220, node221, node222, node223, node224, node225, node226, node227, node228, node229, node230, node231, node232, node233, node234, node235, node236, node237, node238, node239, node240, node241]
  rfl

end RecoveredWordProgram
end BabyMonster.OrderLowerBound
