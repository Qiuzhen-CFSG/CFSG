module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.CachedActions
import Mathlib.Tactic.FinCases

/-!
# Prime-order obstructions for Held representatives 4096 through 4351

For every nonlocal row, kernel reduction verifies a nontrivial prime orbit
of a word in the actual marked generators and representative. The orbit
lemma then constructs an element of that prime order in their generated
subgroup. The cached marked actions are proved equal to the originals.

Source: `../source/orbits.json`, generated from the unchanged ATLAS carrier
by `../source/search_orbits.py`. Emitted by `source/generate.py`; the generator
and JSON are not trusted proof inputs.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

set_option Elab.async false

set_option maxRecDepth 16000 in
private theorem obstruction_4096 : HasPrimeObstruction (representative 4096) := by
  apply obstruction_of_cachedAction 4096 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4097 : HasPrimeObstruction (representative 4097) := by
  apply obstruction_of_cachedAction 4097 [5] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4098 : HasPrimeObstruction (representative 4098) := by
  apply obstruction_of_cachedAction 4098 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4099 : HasPrimeObstruction (representative 4099) := by
  apply obstruction_of_cachedAction 4099 [5] 5 1
    (by decide) (by decide) (by decide) 93
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4100 : HasPrimeObstruction (representative 4100) := by
  apply obstruction_of_cachedAction 4100 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4101 : HasPrimeObstruction (representative 4101) := by
  apply obstruction_of_cachedAction 4101 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4102 : HasPrimeObstruction (representative 4102) := by
  apply obstruction_of_cachedAction 4102 [5] 7 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4103 : HasPrimeObstruction (representative 4103) := by
  apply obstruction_of_cachedAction 4103 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4104 : HasPrimeObstruction (representative 4104) := by
  apply obstruction_of_cachedAction 4104 [5, 1] 7 1
    (by decide) (by decide) (by decide) 21
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4105 : HasPrimeObstruction (representative 4105) := by
  apply obstruction_of_cachedAction 4105 [5] 7 1
    (by decide) (by decide) (by decide) 91
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4106 : HasPrimeObstruction (representative 4106) := by
  apply obstruction_of_cachedAction 4106 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4107 : HasPrimeObstruction (representative 4107) := by
  apply obstruction_of_cachedAction 4107 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4108 : HasPrimeObstruction (representative 4108) := by
  apply obstruction_of_cachedAction 4108 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4109 : HasPrimeObstruction (representative 4109) := by
  apply obstruction_of_cachedAction 4109 [5] 7 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4110 : HasPrimeObstruction (representative 4110) := by
  apply obstruction_of_cachedAction 4110 [5] 7 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4111 : HasPrimeObstruction (representative 4111) := by
  apply obstruction_of_cachedAction 4111 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4112 : HasPrimeObstruction (representative 4112) := by
  apply obstruction_of_cachedAction 4112 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4113 : HasPrimeObstruction (representative 4113) := by
  apply obstruction_of_cachedAction 4113 [5, 3] 5 1
    (by decide) (by decide) (by decide) 107
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4114 : HasPrimeObstruction (representative 4114) := by
  apply obstruction_of_cachedAction 4114 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4115 : HasPrimeObstruction (representative 4115) := by
  apply obstruction_of_cachedAction 4115 [5] 7 1
    (by decide) (by decide) (by decide) 65
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4116 : HasPrimeObstruction (representative 4116) := by
  apply obstruction_of_cachedAction 4116 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4117 : HasPrimeObstruction (representative 4117) := by
  apply obstruction_of_cachedAction 4117 [5, 3] 5 1
    (by decide) (by decide) (by decide) 71
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4118 : HasPrimeObstruction (representative 4118) := by
  apply obstruction_of_cachedAction 4118 [5, 2] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4119 : HasPrimeObstruction (representative 4119) := by
  apply obstruction_of_cachedAction 4119 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4120 : HasPrimeObstruction (representative 4120) := by
  apply obstruction_of_cachedAction 4120 [5, 2] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4121 : HasPrimeObstruction (representative 4121) := by
  apply obstruction_of_cachedAction 4121 [5] 5 1
    (by decide) (by decide) (by decide) 39
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4122 : HasPrimeObstruction (representative 4122) := by
  apply obstruction_of_cachedAction 4122 [5, 2] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4123 : HasPrimeObstruction (representative 4123) := by
  apply obstruction_of_cachedAction 4123 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4124 : HasPrimeObstruction (representative 4124) := by
  apply obstruction_of_cachedAction 4124 [5] 5 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4125 : HasPrimeObstruction (representative 4125) := by
  apply obstruction_of_cachedAction 4125 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4126 : HasPrimeObstruction (representative 4126) := by
  apply obstruction_of_cachedAction 4126 [5, 3] 5 1
    (by decide) (by decide) (by decide) 85
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4127 : HasPrimeObstruction (representative 4127) := by
  apply obstruction_of_cachedAction 4127 [5] 7 1
    (by decide) (by decide) (by decide) 188
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4128 : HasPrimeObstruction (representative 4128) := by
  apply obstruction_of_cachedAction 4128 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4129 : HasPrimeObstruction (representative 4129) := by
  apply obstruction_of_cachedAction 4129 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4130 : HasPrimeObstruction (representative 4130) := by
  apply obstruction_of_cachedAction 4130 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4131 : HasPrimeObstruction (representative 4131) := by
  apply obstruction_of_cachedAction 4131 [5, 1] 7 1
    (by decide) (by decide) (by decide) 93
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4132 : HasPrimeObstruction (representative 4132) := by
  apply obstruction_of_cachedAction 4132 [5, 1] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4133 : HasPrimeObstruction (representative 4133) := by
  apply obstruction_of_cachedAction 4133 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4134 : HasPrimeObstruction (representative 4134) := by
  apply obstruction_of_cachedAction 4134 [5, 3] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4135 : HasPrimeObstruction (representative 4135) := by
  apply obstruction_of_cachedAction 4135 [5] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4136 : HasPrimeObstruction (representative 4136) := by
  apply obstruction_of_cachedAction 4136 [5] 5 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4137 : HasPrimeObstruction (representative 4137) := by
  apply obstruction_of_cachedAction 4137 [5, 2] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4138 : HasPrimeObstruction (representative 4138) := by
  apply obstruction_of_cachedAction 4138 [5] 5 1
    (by decide) (by decide) (by decide) 58
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4139 : HasPrimeObstruction (representative 4139) := by
  apply obstruction_of_cachedAction 4139 [5] 5 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4140 : HasPrimeObstruction (representative 4140) := by
  apply obstruction_of_cachedAction 4140 [5] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4141 : HasPrimeObstruction (representative 4141) := by
  apply obstruction_of_cachedAction 4141 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4142 : HasPrimeObstruction (representative 4142) := by
  apply obstruction_of_cachedAction 4142 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4143 : HasPrimeObstruction (representative 4143) := by
  apply obstruction_of_cachedAction 4143 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4144 : HasPrimeObstruction (representative 4144) := by
  apply obstruction_of_cachedAction 4144 [5] 7 1
    (by decide) (by decide) (by decide) 54
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4145 : HasPrimeObstruction (representative 4145) := by
  apply obstruction_of_cachedAction 4145 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4146 : HasPrimeObstruction (representative 4146) := by
  apply obstruction_of_cachedAction 4146 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4147 : HasPrimeObstruction (representative 4147) := by
  apply obstruction_of_cachedAction 4147 [5, 3] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4148 : HasPrimeObstruction (representative 4148) := by
  apply obstruction_of_cachedAction 4148 [5] 5 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4149 : HasPrimeObstruction (representative 4149) := by
  apply obstruction_of_cachedAction 4149 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4150 : HasPrimeObstruction (representative 4150) := by
  apply obstruction_of_cachedAction 4150 [5, 3] 7 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4151 : HasPrimeObstruction (representative 4151) := by
  apply obstruction_of_cachedAction 4151 [5, 1] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4152 : HasPrimeObstruction (representative 4152) := by
  apply obstruction_of_cachedAction 4152 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4153 : HasPrimeObstruction (representative 4153) := by
  apply obstruction_of_cachedAction 4153 [5] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4154 : HasPrimeObstruction (representative 4154) := by
  apply obstruction_of_cachedAction 4154 [5, 3] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4155 : HasPrimeObstruction (representative 4155) := by
  apply obstruction_of_cachedAction 4155 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4156 : HasPrimeObstruction (representative 4156) := by
  apply obstruction_of_cachedAction 4156 [5] 7 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4157 : HasPrimeObstruction (representative 4157) := by
  apply obstruction_of_cachedAction 4157 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4158 : HasPrimeObstruction (representative 4158) := by
  apply obstruction_of_cachedAction 4158 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4159 : HasPrimeObstruction (representative 4159) := by
  apply obstruction_of_cachedAction 4159 [5] 7 1
    (by decide) (by decide) (by decide) 93
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4160 : HasPrimeObstruction (representative 4160) := by
  apply obstruction_of_cachedAction 4160 [5, 3] 5 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4161 : HasPrimeObstruction (representative 4161) := by
  apply obstruction_of_cachedAction 4161 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4162 : HasPrimeObstruction (representative 4162) := by
  apply obstruction_of_cachedAction 4162 [5, 2] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4163 : HasPrimeObstruction (representative 4163) := by
  apply obstruction_of_cachedAction 4163 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4164 : HasPrimeObstruction (representative 4164) := by
  apply obstruction_of_cachedAction 4164 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4165 : HasPrimeObstruction (representative 4165) := by
  apply obstruction_of_cachedAction 4165 [5, 4] 5 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4166 : HasPrimeObstruction (representative 4166) := by
  apply obstruction_of_cachedAction 4166 [5] 7 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4167 : HasPrimeObstruction (representative 4167) := by
  apply obstruction_of_cachedAction 4167 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4168 : HasPrimeObstruction (representative 4168) := by
  apply obstruction_of_cachedAction 4168 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4169 : HasPrimeObstruction (representative 4169) := by
  apply obstruction_of_cachedAction 4169 [5, 3] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4170 : HasPrimeObstruction (representative 4170) := by
  apply obstruction_of_cachedAction 4170 [5, 2] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4171 : HasPrimeObstruction (representative 4171) := by
  apply obstruction_of_cachedAction 4171 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4172 : HasPrimeObstruction (representative 4172) := by
  apply obstruction_of_cachedAction 4172 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4173 : HasPrimeObstruction (representative 4173) := by
  apply obstruction_of_cachedAction 4173 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4174 : HasPrimeObstruction (representative 4174) := by
  apply obstruction_of_cachedAction 4174 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4175 : HasPrimeObstruction (representative 4175) := by
  apply obstruction_of_cachedAction 4175 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4176 : HasPrimeObstruction (representative 4176) := by
  apply obstruction_of_cachedAction 4176 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4177 : HasPrimeObstruction (representative 4177) := by
  apply obstruction_of_cachedAction 4177 [5, 3] 5 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4178 : HasPrimeObstruction (representative 4178) := by
  apply obstruction_of_cachedAction 4178 [5, 1] 7 1
    (by decide) (by decide) (by decide) 65
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4179 : HasPrimeObstruction (representative 4179) := by
  apply obstruction_of_cachedAction 4179 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4180 : HasPrimeObstruction (representative 4180) := by
  apply obstruction_of_cachedAction 4180 [5] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4181 : HasPrimeObstruction (representative 4181) := by
  apply obstruction_of_cachedAction 4181 [5] 7 1
    (by decide) (by decide) (by decide) 152
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4182 : HasPrimeObstruction (representative 4182) := by
  apply obstruction_of_cachedAction 4182 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4183 : HasPrimeObstruction (representative 4183) := by
  apply obstruction_of_cachedAction 4183 [5, 2] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4184 : HasPrimeObstruction (representative 4184) := by
  apply obstruction_of_cachedAction 4184 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4185 : HasPrimeObstruction (representative 4185) := by
  apply obstruction_of_cachedAction 4185 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4186 : HasPrimeObstruction (representative 4186) := by
  apply obstruction_of_cachedAction 4186 [5, 3] 7 1
    (by decide) (by decide) (by decide) 143
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4187 : HasPrimeObstruction (representative 4187) := by
  apply obstruction_of_cachedAction 4187 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4188 : HasPrimeObstruction (representative 4188) := by
  apply obstruction_of_cachedAction 4188 [5, 1] 7 1
    (by decide) (by decide) (by decide) 73
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4189 : HasPrimeObstruction (representative 4189) := by
  apply obstruction_of_cachedAction 4189 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4190 : HasPrimeObstruction (representative 4190) := by
  apply obstruction_of_cachedAction 4190 [5] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4191 : HasPrimeObstruction (representative 4191) := by
  apply obstruction_of_cachedAction 4191 [5] 7 1
    (by decide) (by decide) (by decide) 66
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4192 : HasPrimeObstruction (representative 4192) := by
  apply obstruction_of_cachedAction 4192 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4193 : HasPrimeObstruction (representative 4193) := by
  apply obstruction_of_cachedAction 4193 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4194 : HasPrimeObstruction (representative 4194) := by
  apply obstruction_of_cachedAction 4194 [5] 7 1
    (by decide) (by decide) (by decide) 68
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4195 : HasPrimeObstruction (representative 4195) := by
  apply obstruction_of_cachedAction 4195 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4196 : HasPrimeObstruction (representative 4196) := by
  apply obstruction_of_cachedAction 4196 [5, 1] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4197 : HasPrimeObstruction (representative 4197) := by
  apply obstruction_of_cachedAction 4197 [5] 7 1
    (by decide) (by decide) (by decide) 94
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4198 : HasPrimeObstruction (representative 4198) := by
  apply obstruction_of_cachedAction 4198 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4199 : HasPrimeObstruction (representative 4199) := by
  apply obstruction_of_cachedAction 4199 [5] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4200 : HasPrimeObstruction (representative 4200) := by
  apply obstruction_of_cachedAction 4200 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4201 : HasPrimeObstruction (representative 4201) := by
  apply obstruction_of_cachedAction 4201 [5] 7 1
    (by decide) (by decide) (by decide) 71
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4202 : HasPrimeObstruction (representative 4202) := by
  apply obstruction_of_cachedAction 4202 [5] 7 1
    (by decide) (by decide) (by decide) 45
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4203 : HasPrimeObstruction (representative 4203) := by
  apply obstruction_of_cachedAction 4203 [5] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4204 : HasPrimeObstruction (representative 4204) := by
  apply obstruction_of_cachedAction 4204 [5] 7 1
    (by decide) (by decide) (by decide) 155
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4205 : HasPrimeObstruction (representative 4205) := by
  apply obstruction_of_cachedAction 4205 [5] 7 1
    (by decide) (by decide) (by decide) 276
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4206 : HasPrimeObstruction (representative 4206) := by
  apply obstruction_of_cachedAction 4206 [5, 2] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4207 : HasPrimeObstruction (representative 4207) := by
  apply obstruction_of_cachedAction 4207 [5, 1] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4208 : HasPrimeObstruction (representative 4208) := by
  apply obstruction_of_cachedAction 4208 [5, 4] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4209 : HasPrimeObstruction (representative 4209) := by
  apply obstruction_of_cachedAction 4209 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4210 : HasPrimeObstruction (representative 4210) := by
  apply obstruction_of_cachedAction 4210 [5, 3] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4211 : HasPrimeObstruction (representative 4211) := by
  apply obstruction_of_cachedAction 4211 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4212 : HasPrimeObstruction (representative 4212) := by
  apply obstruction_of_cachedAction 4212 [5] 7 1
    (by decide) (by decide) (by decide) 240
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4213 : HasPrimeObstruction (representative 4213) := by
  apply obstruction_of_cachedAction 4213 [5, 4] 5 1
    (by decide) (by decide) (by decide) 73
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4214 : HasPrimeObstruction (representative 4214) := by
  apply obstruction_of_cachedAction 4214 [5] 7 1
    (by decide) (by decide) (by decide) 39
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4215 : HasPrimeObstruction (representative 4215) := by
  apply obstruction_of_cachedAction 4215 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4216 : HasPrimeObstruction (representative 4216) := by
  apply obstruction_of_cachedAction 4216 [5] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4217 : HasPrimeObstruction (representative 4217) := by
  apply obstruction_of_cachedAction 4217 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4218 : HasPrimeObstruction (representative 4218) := by
  apply obstruction_of_cachedAction 4218 [5, 1] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4219 : HasPrimeObstruction (representative 4219) := by
  apply obstruction_of_cachedAction 4219 [5] 7 1
    (by decide) (by decide) (by decide) 83
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4220 : HasPrimeObstruction (representative 4220) := by
  apply obstruction_of_cachedAction 4220 [5, 2] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4221 : HasPrimeObstruction (representative 4221) := by
  apply obstruction_of_cachedAction 4221 [5] 7 1
    (by decide) (by decide) (by decide) 40
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4222 : HasPrimeObstruction (representative 4222) := by
  apply obstruction_of_cachedAction 4222 [5, 4] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4223 : HasPrimeObstruction (representative 4223) := by
  apply obstruction_of_cachedAction 4223 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4224 : HasPrimeObstruction (representative 4224) := by
  apply obstruction_of_cachedAction 4224 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4225 : HasPrimeObstruction (representative 4225) := by
  apply obstruction_of_cachedAction 4225 [5, 2] 5 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4226 : HasPrimeObstruction (representative 4226) := by
  apply obstruction_of_cachedAction 4226 [5, 1] 7 1
    (by decide) (by decide) (by decide) 117
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4227 : HasPrimeObstruction (representative 4227) := by
  apply obstruction_of_cachedAction 4227 [5] 7 1
    (by decide) (by decide) (by decide) 364
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4228 : HasPrimeObstruction (representative 4228) := by
  apply obstruction_of_cachedAction 4228 [5] 7 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4229 : HasPrimeObstruction (representative 4229) := by
  apply obstruction_of_cachedAction 4229 [5] 5 1
    (by decide) (by decide) (by decide) 60
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4230 : HasPrimeObstruction (representative 4230) := by
  apply obstruction_of_cachedAction 4230 [5] 7 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4231 : HasPrimeObstruction (representative 4231) := by
  apply obstruction_of_cachedAction 4231 [5] 7 1
    (by decide) (by decide) (by decide) 318
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4232 : HasPrimeObstruction (representative 4232) := by
  apply obstruction_of_cachedAction 4232 [5] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4233 : HasPrimeObstruction (representative 4233) := by
  apply obstruction_of_cachedAction 4233 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4234 : HasPrimeObstruction (representative 4234) := by
  apply obstruction_of_cachedAction 4234 [5] 7 1
    (by decide) (by decide) (by decide) 58
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4235 : HasPrimeObstruction (representative 4235) := by
  apply obstruction_of_cachedAction 4235 [5] 7 1
    (by decide) (by decide) (by decide) 158
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4236 : HasPrimeObstruction (representative 4236) := by
  apply obstruction_of_cachedAction 4236 [5, 3] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4237 : HasPrimeObstruction (representative 4237) := by
  apply obstruction_of_cachedAction 4237 [5, 4] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4238 : HasPrimeObstruction (representative 4238) := by
  apply obstruction_of_cachedAction 4238 [5, 2] 5 1
    (by decide) (by decide) (by decide) 63
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4239 : HasPrimeObstruction (representative 4239) := by
  apply obstruction_of_cachedAction 4239 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4240 : HasPrimeObstruction (representative 4240) := by
  apply obstruction_of_cachedAction 4240 [5, 1] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4241 : HasPrimeObstruction (representative 4241) := by
  apply obstruction_of_cachedAction 4241 [5, 3] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4242 : HasPrimeObstruction (representative 4242) := by
  apply obstruction_of_cachedAction 4242 [5, 1] 7 1
    (by decide) (by decide) (by decide) 185
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4243 : HasPrimeObstruction (representative 4243) := by
  apply obstruction_of_cachedAction 4243 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4244 : HasPrimeObstruction (representative 4244) := by
  apply obstruction_of_cachedAction 4244 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4245 : HasPrimeObstruction (representative 4245) := by
  apply obstruction_of_cachedAction 4245 [5, 1] 7 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4246 : HasPrimeObstruction (representative 4246) := by
  apply obstruction_of_cachedAction 4246 [5, 2] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4247 : HasPrimeObstruction (representative 4247) := by
  apply obstruction_of_cachedAction 4247 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4248 : HasPrimeObstruction (representative 4248) := by
  apply obstruction_of_cachedAction 4248 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4249 : HasPrimeObstruction (representative 4249) := by
  apply obstruction_of_cachedAction 4249 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4250 : HasPrimeObstruction (representative 4250) := by
  apply obstruction_of_cachedAction 4250 [5, 3] 7 1
    (by decide) (by decide) (by decide) 229
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4251 : HasPrimeObstruction (representative 4251) := by
  apply obstruction_of_cachedAction 4251 [5] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4252 : HasPrimeObstruction (representative 4252) := by
  apply obstruction_of_cachedAction 4252 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4253 : HasPrimeObstruction (representative 4253) := by
  apply obstruction_of_cachedAction 4253 [5] 7 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4254 : HasPrimeObstruction (representative 4254) := by
  apply obstruction_of_cachedAction 4254 [5] 7 1
    (by decide) (by decide) (by decide) 45
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4255 : HasPrimeObstruction (representative 4255) := by
  apply obstruction_of_cachedAction 4255 [5] 7 1
    (by decide) (by decide) (by decide) 37
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4256 : HasPrimeObstruction (representative 4256) := by
  apply obstruction_of_cachedAction 4256 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4257 : HasPrimeObstruction (representative 4257) := by
  apply obstruction_of_cachedAction 4257 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4258 : HasPrimeObstruction (representative 4258) := by
  apply obstruction_of_cachedAction 4258 [5] 5 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4259 : HasPrimeObstruction (representative 4259) := by
  apply obstruction_of_cachedAction 4259 [5] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4260 : HasPrimeObstruction (representative 4260) := by
  apply obstruction_of_cachedAction 4260 [5, 2] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4261 : HasPrimeObstruction (representative 4261) := by
  apply obstruction_of_cachedAction 4261 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4262 : HasPrimeObstruction (representative 4262) := by
  apply obstruction_of_cachedAction 4262 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4263 : HasPrimeObstruction (representative 4263) := by
  apply obstruction_of_cachedAction 4263 [5] 7 1
    (by decide) (by decide) (by decide) 142
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4264 : HasPrimeObstruction (representative 4264) := by
  apply obstruction_of_cachedAction 4264 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4265 : HasPrimeObstruction (representative 4265) := by
  apply obstruction_of_cachedAction 4265 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4266 : HasPrimeObstruction (representative 4266) := by
  apply obstruction_of_cachedAction 4266 [5] 5 1
    (by decide) (by decide) (by decide) 63
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4267 : HasPrimeObstruction (representative 4267) := by
  apply obstruction_of_cachedAction 4267 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4268 : HasPrimeObstruction (representative 4268) := by
  apply obstruction_of_cachedAction 4268 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4269 : HasPrimeObstruction (representative 4269) := by
  apply obstruction_of_cachedAction 4269 [5] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4270 : HasPrimeObstruction (representative 4270) := by
  apply obstruction_of_cachedAction 4270 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4271 : HasPrimeObstruction (representative 4271) := by
  apply obstruction_of_cachedAction 4271 [5, 2] 7 1
    (by decide) (by decide) (by decide) 54
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4272 : HasPrimeObstruction (representative 4272) := by
  apply obstruction_of_cachedAction 4272 [5, 4] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4273 : HasPrimeObstruction (representative 4273) := by
  apply obstruction_of_cachedAction 4273 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4274 : HasPrimeObstruction (representative 4274) := by
  apply obstruction_of_cachedAction 4274 [5, 1] 7 1
    (by decide) (by decide) (by decide) 174
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4275 : HasPrimeObstruction (representative 4275) := by
  apply obstruction_of_cachedAction 4275 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4276 : HasPrimeObstruction (representative 4276) := by
  apply obstruction_of_cachedAction 4276 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4277 : HasPrimeObstruction (representative 4277) := by
  apply obstruction_of_cachedAction 4277 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4282 : HasPrimeObstruction (representative 4282) := by
  apply obstruction_of_cachedAction 4282 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4283 : HasPrimeObstruction (representative 4283) := by
  apply obstruction_of_cachedAction 4283 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4284 : HasPrimeObstruction (representative 4284) := by
  apply obstruction_of_cachedAction 4284 [5] 7 1
    (by decide) (by decide) (by decide) 158
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4285 : HasPrimeObstruction (representative 4285) := by
  apply obstruction_of_cachedAction 4285 [5] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4286 : HasPrimeObstruction (representative 4286) := by
  apply obstruction_of_cachedAction 4286 [5] 7 1
    (by decide) (by decide) (by decide) 80
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4287 : HasPrimeObstruction (representative 4287) := by
  apply obstruction_of_cachedAction 4287 [5] 7 1
    (by decide) (by decide) (by decide) 208
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4288 : HasPrimeObstruction (representative 4288) := by
  apply obstruction_of_cachedAction 4288 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4289 : HasPrimeObstruction (representative 4289) := by
  apply obstruction_of_cachedAction 4289 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4290 : HasPrimeObstruction (representative 4290) := by
  apply obstruction_of_cachedAction 4290 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4295 : HasPrimeObstruction (representative 4295) := by
  apply obstruction_of_cachedAction 4295 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4296 : HasPrimeObstruction (representative 4296) := by
  apply obstruction_of_cachedAction 4296 [5] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4297 : HasPrimeObstruction (representative 4297) := by
  apply obstruction_of_cachedAction 4297 [5] 7 1
    (by decide) (by decide) (by decide) 96
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4298 : HasPrimeObstruction (representative 4298) := by
  apply obstruction_of_cachedAction 4298 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4299 : HasPrimeObstruction (representative 4299) := by
  apply obstruction_of_cachedAction 4299 [5] 5 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4300 : HasPrimeObstruction (representative 4300) := by
  apply obstruction_of_cachedAction 4300 [5] 7 1
    (by decide) (by decide) (by decide) 136
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4301 : HasPrimeObstruction (representative 4301) := by
  apply obstruction_of_cachedAction 4301 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4302 : HasPrimeObstruction (representative 4302) := by
  apply obstruction_of_cachedAction 4302 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4303 : HasPrimeObstruction (representative 4303) := by
  apply obstruction_of_cachedAction 4303 [5, 2] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4304 : HasPrimeObstruction (representative 4304) := by
  apply obstruction_of_cachedAction 4304 [5, 4] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4305 : HasPrimeObstruction (representative 4305) := by
  apply obstruction_of_cachedAction 4305 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4306 : HasPrimeObstruction (representative 4306) := by
  apply obstruction_of_cachedAction 4306 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4307 : HasPrimeObstruction (representative 4307) := by
  apply obstruction_of_cachedAction 4307 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4308 : HasPrimeObstruction (representative 4308) := by
  apply obstruction_of_cachedAction 4308 [5] 7 1
    (by decide) (by decide) (by decide) 108
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4309 : HasPrimeObstruction (representative 4309) := by
  apply obstruction_of_cachedAction 4309 [5] 7 1
    (by decide) (by decide) (by decide) 95
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4310 : HasPrimeObstruction (representative 4310) := by
  apply obstruction_of_cachedAction 4310 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4311 : HasPrimeObstruction (representative 4311) := by
  apply obstruction_of_cachedAction 4311 [5] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4312 : HasPrimeObstruction (representative 4312) := by
  apply obstruction_of_cachedAction 4312 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4313 : HasPrimeObstruction (representative 4313) := by
  apply obstruction_of_cachedAction 4313 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4314 : HasPrimeObstruction (representative 4314) := by
  apply obstruction_of_cachedAction 4314 [5, 4] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4315 : HasPrimeObstruction (representative 4315) := by
  apply obstruction_of_cachedAction 4315 [5] 7 1
    (by decide) (by decide) (by decide) 104
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4316 : HasPrimeObstruction (representative 4316) := by
  apply obstruction_of_cachedAction 4316 [5] 5 1
    (by decide) (by decide) (by decide) 85
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4317 : HasPrimeObstruction (representative 4317) := by
  apply obstruction_of_cachedAction 4317 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4318 : HasPrimeObstruction (representative 4318) := by
  apply obstruction_of_cachedAction 4318 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4319 : HasPrimeObstruction (representative 4319) := by
  apply obstruction_of_cachedAction 4319 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4320 : HasPrimeObstruction (representative 4320) := by
  apply obstruction_of_cachedAction 4320 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4321 : HasPrimeObstruction (representative 4321) := by
  apply obstruction_of_cachedAction 4321 [5, 3] 7 1
    (by decide) (by decide) (by decide) 46
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4322 : HasPrimeObstruction (representative 4322) := by
  apply obstruction_of_cachedAction 4322 [5] 7 1
    (by decide) (by decide) (by decide) 36
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4323 : HasPrimeObstruction (representative 4323) := by
  apply obstruction_of_cachedAction 4323 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4324 : HasPrimeObstruction (representative 4324) := by
  apply obstruction_of_cachedAction 4324 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4325 : HasPrimeObstruction (representative 4325) := by
  apply obstruction_of_cachedAction 4325 [5, 1] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4326 : HasPrimeObstruction (representative 4326) := by
  apply obstruction_of_cachedAction 4326 [5] 7 1
    (by decide) (by decide) (by decide) 76
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4327 : HasPrimeObstruction (representative 4327) := by
  apply obstruction_of_cachedAction 4327 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4328 : HasPrimeObstruction (representative 4328) := by
  apply obstruction_of_cachedAction 4328 [5] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4329 : HasPrimeObstruction (representative 4329) := by
  apply obstruction_of_cachedAction 4329 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4330 : HasPrimeObstruction (representative 4330) := by
  apply obstruction_of_cachedAction 4330 [5, 1] 5 1
    (by decide) (by decide) (by decide) 83
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4331 : HasPrimeObstruction (representative 4331) := by
  apply obstruction_of_cachedAction 4331 [5, 3] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4332 : HasPrimeObstruction (representative 4332) := by
  apply obstruction_of_cachedAction 4332 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4333 : HasPrimeObstruction (representative 4333) := by
  apply obstruction_of_cachedAction 4333 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4334 : HasPrimeObstruction (representative 4334) := by
  apply obstruction_of_cachedAction 4334 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4335 : HasPrimeObstruction (representative 4335) := by
  apply obstruction_of_cachedAction 4335 [5] 7 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4336 : HasPrimeObstruction (representative 4336) := by
  apply obstruction_of_cachedAction 4336 [5] 7 1
    (by decide) (by decide) (by decide) 59
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4337 : HasPrimeObstruction (representative 4337) := by
  apply obstruction_of_cachedAction 4337 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4338 : HasPrimeObstruction (representative 4338) := by
  apply obstruction_of_cachedAction 4338 [5, 1] 5 1
    (by decide) (by decide) (by decide) 55
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4339 : HasPrimeObstruction (representative 4339) := by
  apply obstruction_of_cachedAction 4339 [5] 5 1
    (by decide) (by decide) (by decide) 59
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4340 : HasPrimeObstruction (representative 4340) := by
  apply obstruction_of_cachedAction 4340 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4341 : HasPrimeObstruction (representative 4341) := by
  apply obstruction_of_cachedAction 4341 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4342 : HasPrimeObstruction (representative 4342) := by
  apply obstruction_of_cachedAction 4342 [5, 2] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4343 : HasPrimeObstruction (representative 4343) := by
  apply obstruction_of_cachedAction 4343 [5, 2] 5 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4344 : HasPrimeObstruction (representative 4344) := by
  apply obstruction_of_cachedAction 4344 [5] 7 1
    (by decide) (by decide) (by decide) 83
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4345 : HasPrimeObstruction (representative 4345) := by
  apply obstruction_of_cachedAction 4345 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4346 : HasPrimeObstruction (representative 4346) := by
  apply obstruction_of_cachedAction 4346 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4347 : HasPrimeObstruction (representative 4347) := by
  apply obstruction_of_cachedAction 4347 [5] 7 1
    (by decide) (by decide) (by decide) 46
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4348 : HasPrimeObstruction (representative 4348) := by
  apply obstruction_of_cachedAction 4348 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4349 : HasPrimeObstruction (representative 4349) := by
  apply obstruction_of_cachedAction 4349 [5, 2] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4350 : HasPrimeObstruction (representative 4350) := by
  apply obstruction_of_cachedAction 4350 [5, 1] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_4351 : HasPrimeObstruction (representative 4351) := by
  apply obstruction_of_cachedAction 4351 [5, 2] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

/-- Every nonlocal representative in this interval has a forbidden prime order. -/
public theorem obstruction_block16 (j : Fin 256)
    (h : localBranch ⟨4096 + j.val, by omega⟩ = none) :
    HasPrimeObstruction (representative ⟨4096 + j.val, by omega⟩) := by
  fin_cases j
  · exact obstruction_4096
  · exact obstruction_4097
  · exact obstruction_4098
  · exact obstruction_4099
  · exact obstruction_4100
  · exact obstruction_4101
  · exact obstruction_4102
  · exact obstruction_4103
  · exact obstruction_4104
  · exact obstruction_4105
  · exact obstruction_4106
  · exact obstruction_4107
  · exact obstruction_4108
  · exact obstruction_4109
  · exact obstruction_4110
  · exact obstruction_4111
  · exact obstruction_4112
  · exact obstruction_4113
  · exact obstruction_4114
  · exact obstruction_4115
  · exact obstruction_4116
  · exact obstruction_4117
  · exact obstruction_4118
  · exact obstruction_4119
  · exact obstruction_4120
  · exact obstruction_4121
  · exact obstruction_4122
  · exact obstruction_4123
  · exact obstruction_4124
  · exact obstruction_4125
  · exact obstruction_4126
  · exact obstruction_4127
  · exact obstruction_4128
  · exact obstruction_4129
  · exact obstruction_4130
  · exact obstruction_4131
  · exact obstruction_4132
  · exact obstruction_4133
  · exact obstruction_4134
  · exact obstruction_4135
  · exact obstruction_4136
  · exact obstruction_4137
  · exact obstruction_4138
  · exact obstruction_4139
  · exact obstruction_4140
  · exact obstruction_4141
  · exact obstruction_4142
  · exact obstruction_4143
  · exact obstruction_4144
  · exact obstruction_4145
  · exact obstruction_4146
  · exact obstruction_4147
  · exact obstruction_4148
  · exact obstruction_4149
  · exact obstruction_4150
  · exact obstruction_4151
  · exact obstruction_4152
  · exact obstruction_4153
  · exact obstruction_4154
  · exact obstruction_4155
  · exact obstruction_4156
  · exact obstruction_4157
  · exact obstruction_4158
  · exact obstruction_4159
  · exact obstruction_4160
  · exact obstruction_4161
  · exact obstruction_4162
  · exact obstruction_4163
  · exact obstruction_4164
  · exact obstruction_4165
  · exact obstruction_4166
  · exact obstruction_4167
  · exact obstruction_4168
  · exact obstruction_4169
  · exact obstruction_4170
  · exact obstruction_4171
  · exact obstruction_4172
  · exact obstruction_4173
  · exact obstruction_4174
  · exact obstruction_4175
  · exact obstruction_4176
  · exact obstruction_4177
  · exact obstruction_4178
  · exact obstruction_4179
  · exact obstruction_4180
  · exact obstruction_4181
  · exact obstruction_4182
  · exact obstruction_4183
  · exact obstruction_4184
  · exact obstruction_4185
  · exact obstruction_4186
  · exact obstruction_4187
  · exact obstruction_4188
  · exact obstruction_4189
  · exact obstruction_4190
  · exact obstruction_4191
  · exact obstruction_4192
  · exact obstruction_4193
  · exact obstruction_4194
  · exact obstruction_4195
  · exact obstruction_4196
  · exact obstruction_4197
  · exact obstruction_4198
  · exact obstruction_4199
  · exact obstruction_4200
  · exact obstruction_4201
  · exact obstruction_4202
  · exact obstruction_4203
  · exact obstruction_4204
  · exact obstruction_4205
  · exact obstruction_4206
  · exact obstruction_4207
  · exact obstruction_4208
  · exact obstruction_4209
  · exact obstruction_4210
  · exact obstruction_4211
  · exact obstruction_4212
  · exact obstruction_4213
  · exact obstruction_4214
  · exact obstruction_4215
  · exact obstruction_4216
  · exact obstruction_4217
  · exact obstruction_4218
  · exact obstruction_4219
  · exact obstruction_4220
  · exact obstruction_4221
  · exact obstruction_4222
  · exact obstruction_4223
  · exact obstruction_4224
  · exact obstruction_4225
  · exact obstruction_4226
  · exact obstruction_4227
  · exact obstruction_4228
  · exact obstruction_4229
  · exact obstruction_4230
  · exact obstruction_4231
  · exact obstruction_4232
  · exact obstruction_4233
  · exact obstruction_4234
  · exact obstruction_4235
  · exact obstruction_4236
  · exact obstruction_4237
  · exact obstruction_4238
  · exact obstruction_4239
  · exact obstruction_4240
  · exact obstruction_4241
  · exact obstruction_4242
  · exact obstruction_4243
  · exact obstruction_4244
  · exact obstruction_4245
  · exact obstruction_4246
  · exact obstruction_4247
  · exact obstruction_4248
  · exact obstruction_4249
  · exact obstruction_4250
  · exact obstruction_4251
  · exact obstruction_4252
  · exact obstruction_4253
  · exact obstruction_4254
  · exact obstruction_4255
  · exact obstruction_4256
  · exact obstruction_4257
  · exact obstruction_4258
  · exact obstruction_4259
  · exact obstruction_4260
  · exact obstruction_4261
  · exact obstruction_4262
  · exact obstruction_4263
  · exact obstruction_4264
  · exact obstruction_4265
  · exact obstruction_4266
  · exact obstruction_4267
  · exact obstruction_4268
  · exact obstruction_4269
  · exact obstruction_4270
  · exact obstruction_4271
  · exact obstruction_4272
  · exact obstruction_4273
  · exact obstruction_4274
  · exact obstruction_4275
  · exact obstruction_4276
  · exact obstruction_4277
  · simp [localBranch] at h
  · simp [localBranch] at h
  · simp [localBranch] at h
  · simp [localBranch] at h
  · exact obstruction_4282
  · exact obstruction_4283
  · exact obstruction_4284
  · exact obstruction_4285
  · exact obstruction_4286
  · exact obstruction_4287
  · exact obstruction_4288
  · exact obstruction_4289
  · exact obstruction_4290
  · simp [localBranch] at h
  · simp [localBranch] at h
  · simp [localBranch] at h
  · simp [localBranch] at h
  · exact obstruction_4295
  · exact obstruction_4296
  · exact obstruction_4297
  · exact obstruction_4298
  · exact obstruction_4299
  · exact obstruction_4300
  · exact obstruction_4301
  · exact obstruction_4302
  · exact obstruction_4303
  · exact obstruction_4304
  · exact obstruction_4305
  · exact obstruction_4306
  · exact obstruction_4307
  · exact obstruction_4308
  · exact obstruction_4309
  · exact obstruction_4310
  · exact obstruction_4311
  · exact obstruction_4312
  · exact obstruction_4313
  · exact obstruction_4314
  · exact obstruction_4315
  · exact obstruction_4316
  · exact obstruction_4317
  · exact obstruction_4318
  · exact obstruction_4319
  · exact obstruction_4320
  · exact obstruction_4321
  · exact obstruction_4322
  · exact obstruction_4323
  · exact obstruction_4324
  · exact obstruction_4325
  · exact obstruction_4326
  · exact obstruction_4327
  · exact obstruction_4328
  · exact obstruction_4329
  · exact obstruction_4330
  · exact obstruction_4331
  · exact obstruction_4332
  · exact obstruction_4333
  · exact obstruction_4334
  · exact obstruction_4335
  · exact obstruction_4336
  · exact obstruction_4337
  · exact obstruction_4338
  · exact obstruction_4339
  · exact obstruction_4340
  · exact obstruction_4341
  · exact obstruction_4342
  · exact obstruction_4343
  · exact obstruction_4344
  · exact obstruction_4345
  · exact obstruction_4346
  · exact obstruction_4347
  · exact obstruction_4348
  · exact obstruction_4349
  · exact obstruction_4350
  · exact obstruction_4351

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
