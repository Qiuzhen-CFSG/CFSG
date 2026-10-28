module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.Extensions

/-!
# Elementary rows and extension witnesses

Finite data for the 241 elementary rows, including the identity row, and
their selected extensions and conjugators. These definitions assert no
correctness; the sibling certificate module checks them by kernel reduction.
Balanced selection keeps lookup depth bounded without changing resource limits.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 4.5 and Proposition 4.8 step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
namespace FiniteChecks
def row000 : Finset Code := {0}
def row001 : Finset Code := {0, 1}
def row002 : Finset Code := {0, 2}
def row003 : Finset Code := {0, 4}
def row004 : Finset Code := {0, 6}
def row005 : Finset Code := {0, 8}
def row006 : Finset Code := {0, 9}
def row007 : Finset Code := {0, 10}
def row008 : Finset Code := {0, 12}
def row009 : Finset Code := {0, 14}
def row010 : Finset Code := {0, 16}
def row011 : Finset Code := {0, 17}
def row012 : Finset Code := {0, 20}
def row013 : Finset Code := {0, 24}
def row014 : Finset Code := {0, 25}
def row015 : Finset Code := {0, 28}
def row016 : Finset Code := {0, 32}
def row017 : Finset Code := {0, 36}
def row018 : Finset Code := {0, 37}
def row019 : Finset Code := {0, 40}
def row020 : Finset Code := {0, 44}
def row021 : Finset Code := {0, 45}
def row022 : Finset Code := {0, 48}
def row023 : Finset Code := {0, 52}
def row024 : Finset Code := {0, 53}
def row025 : Finset Code := {0, 56}
def row026 : Finset Code := {0, 60}
def row027 : Finset Code := {0, 61}
def row028 : Finset Code := {0, 64}
def row029 : Finset Code := {0, 66}
def row030 : Finset Code := {0, 67}
def row031 : Finset Code := {0, 72}
def row032 : Finset Code := {0, 74}
def row033 : Finset Code := {0, 75}
def row034 : Finset Code := {0, 83}
def row035 : Finset Code := {0, 91}
def row036 : Finset Code := {0, 96}
def row037 : Finset Code := {0, 102}
def row038 : Finset Code := {0, 103}
def row039 : Finset Code := {0, 104}
def row040 : Finset Code := {0, 110}
def row041 : Finset Code := {0, 111}
def row042 : Finset Code := {0, 119}
def row043 : Finset Code := {0, 127}
def row044 : Finset Code := {0, 1, 8, 9}
def row045 : Finset Code := {0, 1, 16, 17}
def row046 : Finset Code := {0, 1, 24, 25}
def row047 : Finset Code := {0, 1, 36, 37}
def row048 : Finset Code := {0, 1, 44, 45}
def row049 : Finset Code := {0, 1, 52, 53}
def row050 : Finset Code := {0, 1, 60, 61}
def row051 : Finset Code := {0, 1, 66, 67}
def row052 : Finset Code := {0, 1, 74, 75}
def row053 : Finset Code := {0, 1, 102, 103}
def row054 : Finset Code := {0, 1, 110, 111}
def row055 : Finset Code := {0, 2, 4, 6}
def row056 : Finset Code := {0, 2, 8, 10}
def row057 : Finset Code := {0, 2, 12, 14}
def row058 : Finset Code := {0, 2, 64, 66}
def row059 : Finset Code := {0, 2, 72, 74}
def row060 : Finset Code := {0, 4, 8, 12}
def row061 : Finset Code := {0, 4, 10, 14}
def row062 : Finset Code := {0, 4, 16, 20}
def row063 : Finset Code := {0, 4, 24, 28}
def row064 : Finset Code := {0, 4, 32, 36}
def row065 : Finset Code := {0, 4, 40, 44}
def row066 : Finset Code := {0, 4, 48, 52}
def row067 : Finset Code := {0, 4, 56, 60}
def row068 : Finset Code := {0, 6, 8, 14}
def row069 : Finset Code := {0, 6, 10, 12}
def row070 : Finset Code := {0, 6, 96, 102}
def row071 : Finset Code := {0, 6, 104, 110}
def row072 : Finset Code := {0, 8, 16, 24}
def row073 : Finset Code := {0, 8, 17, 25}
def row074 : Finset Code := {0, 8, 20, 28}
def row075 : Finset Code := {0, 8, 32, 40}
def row076 : Finset Code := {0, 8, 36, 44}
def row077 : Finset Code := {0, 8, 37, 45}
def row078 : Finset Code := {0, 8, 48, 56}
def row079 : Finset Code := {0, 8, 52, 60}
def row080 : Finset Code := {0, 8, 53, 61}
def row081 : Finset Code := {0, 8, 64, 72}
def row082 : Finset Code := {0, 8, 66, 74}
def row083 : Finset Code := {0, 8, 67, 75}
def row084 : Finset Code := {0, 8, 83, 91}
def row085 : Finset Code := {0, 8, 96, 104}
def row086 : Finset Code := {0, 8, 102, 110}
def row087 : Finset Code := {0, 8, 103, 111}
def row088 : Finset Code := {0, 8, 119, 127}
def row089 : Finset Code := {0, 9, 16, 25}
def row090 : Finset Code := {0, 9, 17, 24}
def row091 : Finset Code := {0, 9, 36, 45}
def row092 : Finset Code := {0, 9, 37, 44}
def row093 : Finset Code := {0, 9, 52, 61}
def row094 : Finset Code := {0, 9, 53, 60}
def row095 : Finset Code := {0, 9, 66, 75}
def row096 : Finset Code := {0, 9, 67, 74}
def row097 : Finset Code := {0, 9, 102, 111}
def row098 : Finset Code := {0, 9, 103, 110}
def row099 : Finset Code := {0, 10, 64, 74}
def row100 : Finset Code := {0, 10, 66, 72}
def row101 : Finset Code := {0, 12, 16, 28}
def row102 : Finset Code := {0, 12, 20, 24}
def row103 : Finset Code := {0, 12, 32, 44}
def row104 : Finset Code := {0, 12, 36, 40}
def row105 : Finset Code := {0, 12, 48, 60}
def row106 : Finset Code := {0, 12, 52, 56}
def row107 : Finset Code := {0, 14, 96, 110}
def row108 : Finset Code := {0, 14, 102, 104}
def row109 : Finset Code := {0, 16, 32, 48}
def row110 : Finset Code := {0, 16, 36, 52}
def row111 : Finset Code := {0, 16, 37, 53}
def row112 : Finset Code := {0, 16, 40, 56}
def row113 : Finset Code := {0, 16, 44, 60}
def row114 : Finset Code := {0, 16, 45, 61}
def row115 : Finset Code := {0, 17, 36, 53}
def row116 : Finset Code := {0, 17, 37, 52}
def row117 : Finset Code := {0, 17, 44, 61}
def row118 : Finset Code := {0, 17, 45, 60}
def row119 : Finset Code := {0, 20, 32, 52}
def row120 : Finset Code := {0, 20, 36, 48}
def row121 : Finset Code := {0, 20, 40, 60}
def row122 : Finset Code := {0, 20, 44, 56}
def row123 : Finset Code := {0, 20, 67, 127}
def row124 : Finset Code := {0, 20, 75, 119}
def row125 : Finset Code := {0, 20, 83, 111}
def row126 : Finset Code := {0, 20, 91, 103}
def row127 : Finset Code := {0, 24, 32, 56}
def row128 : Finset Code := {0, 24, 36, 60}
def row129 : Finset Code := {0, 24, 37, 61}
def row130 : Finset Code := {0, 24, 40, 48}
def row131 : Finset Code := {0, 24, 44, 52}
def row132 : Finset Code := {0, 24, 45, 53}
def row133 : Finset Code := {0, 25, 36, 61}
def row134 : Finset Code := {0, 25, 37, 60}
def row135 : Finset Code := {0, 25, 44, 53}
def row136 : Finset Code := {0, 25, 45, 52}
def row137 : Finset Code := {0, 28, 32, 60}
def row138 : Finset Code := {0, 28, 36, 56}
def row139 : Finset Code := {0, 28, 40, 52}
def row140 : Finset Code := {0, 28, 44, 48}
def row141 : Finset Code := {0, 28, 67, 119}
def row142 : Finset Code := {0, 28, 75, 127}
def row143 : Finset Code := {0, 28, 83, 103}
def row144 : Finset Code := {0, 28, 91, 111}
def row145 : Finset Code := {0, 32, 64, 96}
def row146 : Finset Code := {0, 32, 72, 104}
def row147 : Finset Code := {0, 36, 66, 110}
def row148 : Finset Code := {0, 36, 67, 111}
def row149 : Finset Code := {0, 36, 74, 102}
def row150 : Finset Code := {0, 36, 75, 103}
def row151 : Finset Code := {0, 36, 83, 127}
def row152 : Finset Code := {0, 36, 91, 119}
def row153 : Finset Code := {0, 37, 66, 111}
def row154 : Finset Code := {0, 37, 67, 110}
def row155 : Finset Code := {0, 37, 74, 103}
def row156 : Finset Code := {0, 37, 75, 102}
def row157 : Finset Code := {0, 40, 64, 104}
def row158 : Finset Code := {0, 40, 72, 96}
def row159 : Finset Code := {0, 44, 66, 102}
def row160 : Finset Code := {0, 44, 67, 103}
def row161 : Finset Code := {0, 44, 74, 110}
def row162 : Finset Code := {0, 44, 75, 111}
def row163 : Finset Code := {0, 44, 83, 119}
def row164 : Finset Code := {0, 44, 91, 127}
def row165 : Finset Code := {0, 45, 66, 103}
def row166 : Finset Code := {0, 45, 67, 102}
def row167 : Finset Code := {0, 45, 74, 111}
def row168 : Finset Code := {0, 45, 75, 110}
def row169 : Finset Code := {0, 48, 67, 83}
def row170 : Finset Code := {0, 48, 75, 91}
def row171 : Finset Code := {0, 48, 103, 119}
def row172 : Finset Code := {0, 48, 111, 127}
def row173 : Finset Code := {0, 56, 67, 91}
def row174 : Finset Code := {0, 56, 75, 83}
def row175 : Finset Code := {0, 56, 103, 127}
def row176 : Finset Code := {0, 56, 111, 119}
def row177 : Finset Code := {0, 1, 8, 9, 16, 17, 24, 25}
def row178 : Finset Code := {0, 1, 8, 9, 36, 37, 44, 45}
def row179 : Finset Code := {0, 1, 8, 9, 52, 53, 60, 61}
def row180 : Finset Code := {0, 1, 8, 9, 66, 67, 74, 75}
def row181 : Finset Code := {0, 1, 8, 9, 102, 103, 110, 111}
def row182 : Finset Code := {0, 1, 16, 17, 36, 37, 52, 53}
def row183 : Finset Code := {0, 1, 16, 17, 44, 45, 60, 61}
def row184 : Finset Code := {0, 1, 24, 25, 36, 37, 60, 61}
def row185 : Finset Code := {0, 1, 24, 25, 44, 45, 52, 53}
def row186 : Finset Code := {0, 1, 36, 37, 66, 67, 110, 111}
def row187 : Finset Code := {0, 1, 36, 37, 74, 75, 102, 103}
def row188 : Finset Code := {0, 1, 44, 45, 66, 67, 102, 103}
def row189 : Finset Code := {0, 1, 44, 45, 74, 75, 110, 111}
def row190 : Finset Code := {0, 2, 4, 6, 8, 10, 12, 14}
def row191 : Finset Code := {0, 2, 8, 10, 64, 66, 72, 74}
def row192 : Finset Code := {0, 4, 8, 12, 16, 20, 24, 28}
def row193 : Finset Code := {0, 4, 8, 12, 32, 36, 40, 44}
def row194 : Finset Code := {0, 4, 8, 12, 48, 52, 56, 60}
def row195 : Finset Code := {0, 4, 16, 20, 32, 36, 48, 52}
def row196 : Finset Code := {0, 4, 16, 20, 40, 44, 56, 60}
def row197 : Finset Code := {0, 4, 24, 28, 32, 36, 56, 60}
def row198 : Finset Code := {0, 4, 24, 28, 40, 44, 48, 52}
def row199 : Finset Code := {0, 6, 8, 14, 96, 102, 104, 110}
def row200 : Finset Code := {0, 8, 16, 24, 32, 40, 48, 56}
def row201 : Finset Code := {0, 8, 16, 24, 36, 44, 52, 60}
def row202 : Finset Code := {0, 8, 16, 24, 37, 45, 53, 61}
def row203 : Finset Code := {0, 8, 17, 25, 36, 44, 53, 61}
def row204 : Finset Code := {0, 8, 17, 25, 37, 45, 52, 60}
def row205 : Finset Code := {0, 8, 20, 28, 32, 40, 52, 60}
def row206 : Finset Code := {0, 8, 20, 28, 36, 44, 48, 56}
def row207 : Finset Code := {0, 8, 20, 28, 67, 75, 119, 127}
def row208 : Finset Code := {0, 8, 20, 28, 83, 91, 103, 111}
def row209 : Finset Code := {0, 8, 32, 40, 64, 72, 96, 104}
def row210 : Finset Code := {0, 8, 36, 44, 66, 74, 102, 110}
def row211 : Finset Code := {0, 8, 36, 44, 67, 75, 103, 111}
def row212 : Finset Code := {0, 8, 36, 44, 83, 91, 119, 127}
def row213 : Finset Code := {0, 8, 37, 45, 66, 74, 103, 111}
def row214 : Finset Code := {0, 8, 37, 45, 67, 75, 102, 110}
def row215 : Finset Code := {0, 8, 48, 56, 67, 75, 83, 91}
def row216 : Finset Code := {0, 8, 48, 56, 103, 111, 119, 127}
def row217 : Finset Code := {0, 9, 16, 25, 36, 45, 52, 61}
def row218 : Finset Code := {0, 9, 16, 25, 37, 44, 53, 60}
def row219 : Finset Code := {0, 9, 17, 24, 36, 45, 53, 60}
def row220 : Finset Code := {0, 9, 17, 24, 37, 44, 52, 61}
def row221 : Finset Code := {0, 9, 36, 45, 66, 75, 103, 110}
def row222 : Finset Code := {0, 9, 36, 45, 67, 74, 102, 111}
def row223 : Finset Code := {0, 9, 37, 44, 66, 75, 102, 111}
def row224 : Finset Code := {0, 9, 37, 44, 67, 74, 103, 110}
def row225 : Finset Code := {0, 12, 16, 28, 32, 44, 48, 60}
def row226 : Finset Code := {0, 12, 16, 28, 36, 40, 52, 56}
def row227 : Finset Code := {0, 12, 20, 24, 32, 44, 52, 56}
def row228 : Finset Code := {0, 12, 20, 24, 36, 40, 48, 60}
def row229 : Finset Code := {0, 20, 36, 48, 67, 83, 111, 127}
def row230 : Finset Code := {0, 20, 36, 48, 75, 91, 103, 119}
def row231 : Finset Code := {0, 20, 44, 56, 67, 91, 103, 127}
def row232 : Finset Code := {0, 20, 44, 56, 75, 83, 111, 119}
def row233 : Finset Code := {0, 28, 36, 56, 67, 91, 111, 119}
def row234 : Finset Code := {0, 28, 36, 56, 75, 83, 103, 127}
def row235 : Finset Code := {0, 28, 44, 48, 67, 83, 103, 119}
def row236 : Finset Code := {0, 28, 44, 48, 75, 91, 111, 127}
def row237 : Finset Code := {0, 1, 8, 9, 16, 17, 24, 25, 36, 37, 44, 45, 52, 53, 60, 61}
def row238 : Finset Code := {0, 1, 8, 9, 36, 37, 44, 45, 66, 67, 74, 75, 102, 103, 110, 111}
def row239 : Finset Code := {0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60}
def row240 : Finset Code := {0, 8, 20, 28, 36, 44, 48, 56, 67, 75, 83, 91, 103, 111, 119, 127}
end FiniteChecks

/-- The 241 candidate elementary rows, with the identity in row zero. -/
def elementaryRows (i : Fin 241) : Finset Code :=
  if i.val < 120 then
  (if i.val < 60 then
  (if i.val < 30 then
  (if i.val < 15 then
  (if i.val < 7 then
  (if i.val < 3 then
  (if i.val < 1 then
  (FiniteChecks.row000) else
  (if i.val < 2 then
  (FiniteChecks.row001) else
  (FiniteChecks.row002))) else
  (if i.val < 5 then
  (if i.val < 4 then
  (FiniteChecks.row003) else
  (FiniteChecks.row004)) else
  (if i.val < 6 then
  (FiniteChecks.row005) else
  (FiniteChecks.row006)))) else
  (if i.val < 11 then
  (if i.val < 9 then
  (if i.val < 8 then
  (FiniteChecks.row007) else
  (FiniteChecks.row008)) else
  (if i.val < 10 then
  (FiniteChecks.row009) else
  (FiniteChecks.row010))) else
  (if i.val < 13 then
  (if i.val < 12 then
  (FiniteChecks.row011) else
  (FiniteChecks.row012)) else
  (if i.val < 14 then
  (FiniteChecks.row013) else
  (FiniteChecks.row014))))) else
  (if i.val < 22 then
  (if i.val < 18 then
  (if i.val < 16 then
  (FiniteChecks.row015) else
  (if i.val < 17 then
  (FiniteChecks.row016) else
  (FiniteChecks.row017))) else
  (if i.val < 20 then
  (if i.val < 19 then
  (FiniteChecks.row018) else
  (FiniteChecks.row019)) else
  (if i.val < 21 then
  (FiniteChecks.row020) else
  (FiniteChecks.row021)))) else
  (if i.val < 26 then
  (if i.val < 24 then
  (if i.val < 23 then
  (FiniteChecks.row022) else
  (FiniteChecks.row023)) else
  (if i.val < 25 then
  (FiniteChecks.row024) else
  (FiniteChecks.row025))) else
  (if i.val < 28 then
  (if i.val < 27 then
  (FiniteChecks.row026) else
  (FiniteChecks.row027)) else
  (if i.val < 29 then
  (FiniteChecks.row028) else
  (FiniteChecks.row029)))))) else
  (if i.val < 45 then
  (if i.val < 37 then
  (if i.val < 33 then
  (if i.val < 31 then
  (FiniteChecks.row030) else
  (if i.val < 32 then
  (FiniteChecks.row031) else
  (FiniteChecks.row032))) else
  (if i.val < 35 then
  (if i.val < 34 then
  (FiniteChecks.row033) else
  (FiniteChecks.row034)) else
  (if i.val < 36 then
  (FiniteChecks.row035) else
  (FiniteChecks.row036)))) else
  (if i.val < 41 then
  (if i.val < 39 then
  (if i.val < 38 then
  (FiniteChecks.row037) else
  (FiniteChecks.row038)) else
  (if i.val < 40 then
  (FiniteChecks.row039) else
  (FiniteChecks.row040))) else
  (if i.val < 43 then
  (if i.val < 42 then
  (FiniteChecks.row041) else
  (FiniteChecks.row042)) else
  (if i.val < 44 then
  (FiniteChecks.row043) else
  (FiniteChecks.row044))))) else
  (if i.val < 52 then
  (if i.val < 48 then
  (if i.val < 46 then
  (FiniteChecks.row045) else
  (if i.val < 47 then
  (FiniteChecks.row046) else
  (FiniteChecks.row047))) else
  (if i.val < 50 then
  (if i.val < 49 then
  (FiniteChecks.row048) else
  (FiniteChecks.row049)) else
  (if i.val < 51 then
  (FiniteChecks.row050) else
  (FiniteChecks.row051)))) else
  (if i.val < 56 then
  (if i.val < 54 then
  (if i.val < 53 then
  (FiniteChecks.row052) else
  (FiniteChecks.row053)) else
  (if i.val < 55 then
  (FiniteChecks.row054) else
  (FiniteChecks.row055))) else
  (if i.val < 58 then
  (if i.val < 57 then
  (FiniteChecks.row056) else
  (FiniteChecks.row057)) else
  (if i.val < 59 then
  (FiniteChecks.row058) else
  (FiniteChecks.row059))))))) else
  (if i.val < 90 then
  (if i.val < 75 then
  (if i.val < 67 then
  (if i.val < 63 then
  (if i.val < 61 then
  (FiniteChecks.row060) else
  (if i.val < 62 then
  (FiniteChecks.row061) else
  (FiniteChecks.row062))) else
  (if i.val < 65 then
  (if i.val < 64 then
  (FiniteChecks.row063) else
  (FiniteChecks.row064)) else
  (if i.val < 66 then
  (FiniteChecks.row065) else
  (FiniteChecks.row066)))) else
  (if i.val < 71 then
  (if i.val < 69 then
  (if i.val < 68 then
  (FiniteChecks.row067) else
  (FiniteChecks.row068)) else
  (if i.val < 70 then
  (FiniteChecks.row069) else
  (FiniteChecks.row070))) else
  (if i.val < 73 then
  (if i.val < 72 then
  (FiniteChecks.row071) else
  (FiniteChecks.row072)) else
  (if i.val < 74 then
  (FiniteChecks.row073) else
  (FiniteChecks.row074))))) else
  (if i.val < 82 then
  (if i.val < 78 then
  (if i.val < 76 then
  (FiniteChecks.row075) else
  (if i.val < 77 then
  (FiniteChecks.row076) else
  (FiniteChecks.row077))) else
  (if i.val < 80 then
  (if i.val < 79 then
  (FiniteChecks.row078) else
  (FiniteChecks.row079)) else
  (if i.val < 81 then
  (FiniteChecks.row080) else
  (FiniteChecks.row081)))) else
  (if i.val < 86 then
  (if i.val < 84 then
  (if i.val < 83 then
  (FiniteChecks.row082) else
  (FiniteChecks.row083)) else
  (if i.val < 85 then
  (FiniteChecks.row084) else
  (FiniteChecks.row085))) else
  (if i.val < 88 then
  (if i.val < 87 then
  (FiniteChecks.row086) else
  (FiniteChecks.row087)) else
  (if i.val < 89 then
  (FiniteChecks.row088) else
  (FiniteChecks.row089)))))) else
  (if i.val < 105 then
  (if i.val < 97 then
  (if i.val < 93 then
  (if i.val < 91 then
  (FiniteChecks.row090) else
  (if i.val < 92 then
  (FiniteChecks.row091) else
  (FiniteChecks.row092))) else
  (if i.val < 95 then
  (if i.val < 94 then
  (FiniteChecks.row093) else
  (FiniteChecks.row094)) else
  (if i.val < 96 then
  (FiniteChecks.row095) else
  (FiniteChecks.row096)))) else
  (if i.val < 101 then
  (if i.val < 99 then
  (if i.val < 98 then
  (FiniteChecks.row097) else
  (FiniteChecks.row098)) else
  (if i.val < 100 then
  (FiniteChecks.row099) else
  (FiniteChecks.row100))) else
  (if i.val < 103 then
  (if i.val < 102 then
  (FiniteChecks.row101) else
  (FiniteChecks.row102)) else
  (if i.val < 104 then
  (FiniteChecks.row103) else
  (FiniteChecks.row104))))) else
  (if i.val < 112 then
  (if i.val < 108 then
  (if i.val < 106 then
  (FiniteChecks.row105) else
  (if i.val < 107 then
  (FiniteChecks.row106) else
  (FiniteChecks.row107))) else
  (if i.val < 110 then
  (if i.val < 109 then
  (FiniteChecks.row108) else
  (FiniteChecks.row109)) else
  (if i.val < 111 then
  (FiniteChecks.row110) else
  (FiniteChecks.row111)))) else
  (if i.val < 116 then
  (if i.val < 114 then
  (if i.val < 113 then
  (FiniteChecks.row112) else
  (FiniteChecks.row113)) else
  (if i.val < 115 then
  (FiniteChecks.row114) else
  (FiniteChecks.row115))) else
  (if i.val < 118 then
  (if i.val < 117 then
  (FiniteChecks.row116) else
  (FiniteChecks.row117)) else
  (if i.val < 119 then
  (FiniteChecks.row118) else
  (FiniteChecks.row119)))))))) else
  (if i.val < 180 then
  (if i.val < 150 then
  (if i.val < 135 then
  (if i.val < 127 then
  (if i.val < 123 then
  (if i.val < 121 then
  (FiniteChecks.row120) else
  (if i.val < 122 then
  (FiniteChecks.row121) else
  (FiniteChecks.row122))) else
  (if i.val < 125 then
  (if i.val < 124 then
  (FiniteChecks.row123) else
  (FiniteChecks.row124)) else
  (if i.val < 126 then
  (FiniteChecks.row125) else
  (FiniteChecks.row126)))) else
  (if i.val < 131 then
  (if i.val < 129 then
  (if i.val < 128 then
  (FiniteChecks.row127) else
  (FiniteChecks.row128)) else
  (if i.val < 130 then
  (FiniteChecks.row129) else
  (FiniteChecks.row130))) else
  (if i.val < 133 then
  (if i.val < 132 then
  (FiniteChecks.row131) else
  (FiniteChecks.row132)) else
  (if i.val < 134 then
  (FiniteChecks.row133) else
  (FiniteChecks.row134))))) else
  (if i.val < 142 then
  (if i.val < 138 then
  (if i.val < 136 then
  (FiniteChecks.row135) else
  (if i.val < 137 then
  (FiniteChecks.row136) else
  (FiniteChecks.row137))) else
  (if i.val < 140 then
  (if i.val < 139 then
  (FiniteChecks.row138) else
  (FiniteChecks.row139)) else
  (if i.val < 141 then
  (FiniteChecks.row140) else
  (FiniteChecks.row141)))) else
  (if i.val < 146 then
  (if i.val < 144 then
  (if i.val < 143 then
  (FiniteChecks.row142) else
  (FiniteChecks.row143)) else
  (if i.val < 145 then
  (FiniteChecks.row144) else
  (FiniteChecks.row145))) else
  (if i.val < 148 then
  (if i.val < 147 then
  (FiniteChecks.row146) else
  (FiniteChecks.row147)) else
  (if i.val < 149 then
  (FiniteChecks.row148) else
  (FiniteChecks.row149)))))) else
  (if i.val < 165 then
  (if i.val < 157 then
  (if i.val < 153 then
  (if i.val < 151 then
  (FiniteChecks.row150) else
  (if i.val < 152 then
  (FiniteChecks.row151) else
  (FiniteChecks.row152))) else
  (if i.val < 155 then
  (if i.val < 154 then
  (FiniteChecks.row153) else
  (FiniteChecks.row154)) else
  (if i.val < 156 then
  (FiniteChecks.row155) else
  (FiniteChecks.row156)))) else
  (if i.val < 161 then
  (if i.val < 159 then
  (if i.val < 158 then
  (FiniteChecks.row157) else
  (FiniteChecks.row158)) else
  (if i.val < 160 then
  (FiniteChecks.row159) else
  (FiniteChecks.row160))) else
  (if i.val < 163 then
  (if i.val < 162 then
  (FiniteChecks.row161) else
  (FiniteChecks.row162)) else
  (if i.val < 164 then
  (FiniteChecks.row163) else
  (FiniteChecks.row164))))) else
  (if i.val < 172 then
  (if i.val < 168 then
  (if i.val < 166 then
  (FiniteChecks.row165) else
  (if i.val < 167 then
  (FiniteChecks.row166) else
  (FiniteChecks.row167))) else
  (if i.val < 170 then
  (if i.val < 169 then
  (FiniteChecks.row168) else
  (FiniteChecks.row169)) else
  (if i.val < 171 then
  (FiniteChecks.row170) else
  (FiniteChecks.row171)))) else
  (if i.val < 176 then
  (if i.val < 174 then
  (if i.val < 173 then
  (FiniteChecks.row172) else
  (FiniteChecks.row173)) else
  (if i.val < 175 then
  (FiniteChecks.row174) else
  (FiniteChecks.row175))) else
  (if i.val < 178 then
  (if i.val < 177 then
  (FiniteChecks.row176) else
  (FiniteChecks.row177)) else
  (if i.val < 179 then
  (FiniteChecks.row178) else
  (FiniteChecks.row179))))))) else
  (if i.val < 210 then
  (if i.val < 195 then
  (if i.val < 187 then
  (if i.val < 183 then
  (if i.val < 181 then
  (FiniteChecks.row180) else
  (if i.val < 182 then
  (FiniteChecks.row181) else
  (FiniteChecks.row182))) else
  (if i.val < 185 then
  (if i.val < 184 then
  (FiniteChecks.row183) else
  (FiniteChecks.row184)) else
  (if i.val < 186 then
  (FiniteChecks.row185) else
  (FiniteChecks.row186)))) else
  (if i.val < 191 then
  (if i.val < 189 then
  (if i.val < 188 then
  (FiniteChecks.row187) else
  (FiniteChecks.row188)) else
  (if i.val < 190 then
  (FiniteChecks.row189) else
  (FiniteChecks.row190))) else
  (if i.val < 193 then
  (if i.val < 192 then
  (FiniteChecks.row191) else
  (FiniteChecks.row192)) else
  (if i.val < 194 then
  (FiniteChecks.row193) else
  (FiniteChecks.row194))))) else
  (if i.val < 202 then
  (if i.val < 198 then
  (if i.val < 196 then
  (FiniteChecks.row195) else
  (if i.val < 197 then
  (FiniteChecks.row196) else
  (FiniteChecks.row197))) else
  (if i.val < 200 then
  (if i.val < 199 then
  (FiniteChecks.row198) else
  (FiniteChecks.row199)) else
  (if i.val < 201 then
  (FiniteChecks.row200) else
  (FiniteChecks.row201)))) else
  (if i.val < 206 then
  (if i.val < 204 then
  (if i.val < 203 then
  (FiniteChecks.row202) else
  (FiniteChecks.row203)) else
  (if i.val < 205 then
  (FiniteChecks.row204) else
  (FiniteChecks.row205))) else
  (if i.val < 208 then
  (if i.val < 207 then
  (FiniteChecks.row206) else
  (FiniteChecks.row207)) else
  (if i.val < 209 then
  (FiniteChecks.row208) else
  (FiniteChecks.row209)))))) else
  (if i.val < 225 then
  (if i.val < 217 then
  (if i.val < 213 then
  (if i.val < 211 then
  (FiniteChecks.row210) else
  (if i.val < 212 then
  (FiniteChecks.row211) else
  (FiniteChecks.row212))) else
  (if i.val < 215 then
  (if i.val < 214 then
  (FiniteChecks.row213) else
  (FiniteChecks.row214)) else
  (if i.val < 216 then
  (FiniteChecks.row215) else
  (FiniteChecks.row216)))) else
  (if i.val < 221 then
  (if i.val < 219 then
  (if i.val < 218 then
  (FiniteChecks.row217) else
  (FiniteChecks.row218)) else
  (if i.val < 220 then
  (FiniteChecks.row219) else
  (FiniteChecks.row220))) else
  (if i.val < 223 then
  (if i.val < 222 then
  (FiniteChecks.row221) else
  (FiniteChecks.row222)) else
  (if i.val < 224 then
  (FiniteChecks.row223) else
  (FiniteChecks.row224))))) else
  (if i.val < 233 then
  (if i.val < 229 then
  (if i.val < 227 then
  (if i.val < 226 then
  (FiniteChecks.row225) else
  (FiniteChecks.row226)) else
  (if i.val < 228 then
  (FiniteChecks.row227) else
  (FiniteChecks.row228))) else
  (if i.val < 231 then
  (if i.val < 230 then
  (FiniteChecks.row229) else
  (FiniteChecks.row230)) else
  (if i.val < 232 then
  (FiniteChecks.row231) else
  (FiniteChecks.row232)))) else
  (if i.val < 237 then
  (if i.val < 235 then
  (if i.val < 234 then
  (FiniteChecks.row233) else
  (FiniteChecks.row234)) else
  (if i.val < 236 then
  (FiniteChecks.row235) else
  (FiniteChecks.row236))) else
  (if i.val < 239 then
  (if i.val < 238 then
  (FiniteChecks.row237) else
  (FiniteChecks.row238)) else
  (if i.val < 240 then
  (FiniteChecks.row239) else
  (FiniteChecks.row240))))))))

namespace FiniteChecks
def next000 : Code → Fin 241 :=
  ![0, 1, 2, 0, 3, 0, 4, 0, 5, 6, 7, 0, 8, 0, 9, 0, 10, 11, 0, 0, 12, 0, 0, 0, 13, 14, 0, 0, 15, 0, 0, 0, 16, 0, 0, 0, 17, 18, 0, 0, 19, 0, 0, 0, 20, 21, 0, 0, 22, 0, 0, 0, 23, 24, 0, 0, 25, 0, 0, 0, 26, 27, 0, 0, 28, 0, 29, 30, 0, 0, 0, 0, 31, 0, 32, 33, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 37, 38, 39, 0, 0, 0, 0, 0, 40, 41, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 43]
def next001 : Code → Fin 241 :=
  ![1, 1, 0, 0, 0, 0, 0, 0, 44, 44, 0, 0, 0, 0, 0, 0, 45, 45, 0, 0, 0, 0, 0, 0, 46, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 47, 0, 0, 0, 0, 0, 0, 48, 48, 0, 0, 0, 0, 0, 0, 49, 49, 0, 0, 0, 0, 0, 0, 50, 50, 0, 0, 0, 0, 51, 51, 0, 0, 0, 0, 0, 0, 52, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 53, 0, 0, 0, 0, 0, 0, 54, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next002 : Code → Fin 241 :=
  ![2, 0, 2, 0, 55, 0, 55, 0, 56, 0, 56, 0, 57, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 58, 0, 0, 0, 0, 0, 59, 0, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next003 : Code → Fin 241 :=
  ![3, 0, 55, 0, 3, 0, 55, 0, 60, 0, 61, 0, 60, 0, 61, 0, 62, 0, 0, 0, 62, 0, 0, 0, 63, 0, 0, 0, 63, 0, 0, 0, 64, 0, 0, 0, 64, 0, 0, 0, 65, 0, 0, 0, 65, 0, 0, 0, 66, 0, 0, 0, 66, 0, 0, 0, 67, 0, 0, 0, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next004 : Code → Fin 241 :=
  ![4, 0, 55, 0, 55, 0, 4, 0, 68, 0, 69, 0, 69, 0, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 70, 0, 71, 0, 0, 0, 0, 0, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next005 : Code → Fin 241 :=
  ![5, 44, 56, 0, 60, 0, 68, 0, 5, 44, 56, 0, 60, 0, 68, 0, 72, 73, 0, 0, 74, 0, 0, 0, 72, 73, 0, 0, 74, 0, 0, 0, 75, 0, 0, 0, 76, 77, 0, 0, 75, 0, 0, 0, 76, 77, 0, 0, 78, 0, 0, 0, 79, 80, 0, 0, 78, 0, 0, 0, 79, 80, 0, 0, 81, 0, 82, 83, 0, 0, 0, 0, 81, 0, 82, 83, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 85, 0, 0, 0, 0, 0, 86, 87, 85, 0, 0, 0, 0, 0, 86, 87, 0, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 88]
def next006 : Code → Fin 241 :=
  ![6, 44, 0, 0, 0, 0, 0, 0, 44, 6, 0, 0, 0, 0, 0, 0, 89, 90, 0, 0, 0, 0, 0, 0, 90, 89, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 92, 0, 0, 0, 0, 0, 0, 92, 91, 0, 0, 0, 0, 0, 0, 93, 94, 0, 0, 0, 0, 0, 0, 94, 93, 0, 0, 0, 0, 95, 96, 0, 0, 0, 0, 0, 0, 96, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97, 98, 0, 0, 0, 0, 0, 0, 98, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next007 : Code → Fin 241 :=
  ![7, 0, 56, 0, 61, 0, 69, 0, 56, 0, 7, 0, 69, 0, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 100, 0, 0, 0, 0, 0, 100, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next008 : Code → Fin 241 :=
  ![8, 0, 57, 0, 60, 0, 69, 0, 60, 0, 69, 0, 8, 0, 57, 0, 101, 0, 0, 0, 102, 0, 0, 0, 102, 0, 0, 0, 101, 0, 0, 0, 103, 0, 0, 0, 104, 0, 0, 0, 104, 0, 0, 0, 103, 0, 0, 0, 105, 0, 0, 0, 106, 0, 0, 0, 106, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next009 : Code → Fin 241 :=
  ![9, 0, 57, 0, 61, 0, 68, 0, 68, 0, 61, 0, 57, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 108, 0, 108, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next010 : Code → Fin 241 :=
  ![10, 45, 0, 0, 62, 0, 0, 0, 72, 89, 0, 0, 101, 0, 0, 0, 10, 45, 0, 0, 62, 0, 0, 0, 72, 89, 0, 0, 101, 0, 0, 0, 109, 0, 0, 0, 110, 111, 0, 0, 112, 0, 0, 0, 113, 114, 0, 0, 109, 0, 0, 0, 110, 111, 0, 0, 112, 0, 0, 0, 113, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next011 : Code → Fin 241 :=
  ![11, 45, 0, 0, 0, 0, 0, 0, 73, 90, 0, 0, 0, 0, 0, 0, 45, 11, 0, 0, 0, 0, 0, 0, 90, 73, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 115, 116, 0, 0, 0, 0, 0, 0, 117, 118, 0, 0, 0, 0, 0, 0, 116, 115, 0, 0, 0, 0, 0, 0, 118, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next012 : Code → Fin 241 :=
  ![12, 0, 0, 0, 62, 0, 0, 0, 74, 0, 0, 0, 102, 0, 0, 0, 62, 0, 0, 0, 12, 0, 0, 0, 102, 0, 0, 0, 74, 0, 0, 0, 119, 0, 0, 0, 120, 0, 0, 0, 121, 0, 0, 0, 122, 0, 0, 0, 120, 0, 0, 0, 119, 0, 0, 0, 122, 0, 0, 0, 121, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 123]
def next013 : Code → Fin 241 :=
  ![13, 46, 0, 0, 63, 0, 0, 0, 72, 90, 0, 0, 102, 0, 0, 0, 72, 90, 0, 0, 102, 0, 0, 0, 13, 46, 0, 0, 63, 0, 0, 0, 127, 0, 0, 0, 128, 129, 0, 0, 130, 0, 0, 0, 131, 132, 0, 0, 130, 0, 0, 0, 131, 132, 0, 0, 127, 0, 0, 0, 128, 129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next014 : Code → Fin 241 :=
  ![14, 46, 0, 0, 0, 0, 0, 0, 73, 89, 0, 0, 0, 0, 0, 0, 89, 73, 0, 0, 0, 0, 0, 0, 46, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133, 134, 0, 0, 0, 0, 0, 0, 135, 136, 0, 0, 0, 0, 0, 0, 136, 135, 0, 0, 0, 0, 0, 0, 134, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next015 : Code → Fin 241 :=
  ![15, 0, 0, 0, 63, 0, 0, 0, 74, 0, 0, 0, 101, 0, 0, 0, 101, 0, 0, 0, 74, 0, 0, 0, 63, 0, 0, 0, 15, 0, 0, 0, 137, 0, 0, 0, 138, 0, 0, 0, 139, 0, 0, 0, 140, 0, 0, 0, 140, 0, 0, 0, 139, 0, 0, 0, 138, 0, 0, 0, 137, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 142]
def next016 : Code → Fin 241 :=
  ![16, 0, 0, 0, 64, 0, 0, 0, 75, 0, 0, 0, 103, 0, 0, 0, 109, 0, 0, 0, 119, 0, 0, 0, 127, 0, 0, 0, 137, 0, 0, 0, 16, 0, 0, 0, 64, 0, 0, 0, 75, 0, 0, 0, 103, 0, 0, 0, 109, 0, 0, 0, 119, 0, 0, 0, 127, 0, 0, 0, 137, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next017 : Code → Fin 241 :=
  ![17, 47, 0, 0, 64, 0, 0, 0, 76, 91, 0, 0, 104, 0, 0, 0, 110, 115, 0, 0, 120, 0, 0, 0, 128, 133, 0, 0, 138, 0, 0, 0, 64, 0, 0, 0, 17, 47, 0, 0, 104, 0, 0, 0, 76, 91, 0, 0, 120, 0, 0, 0, 110, 115, 0, 0, 138, 0, 0, 0, 128, 133, 0, 0, 0, 0, 147, 148, 0, 0, 0, 0, 0, 0, 149, 150, 0, 0, 0, 0, 0, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 150, 0, 0, 0, 0, 0, 0, 147, 148, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 151]
def next018 : Code → Fin 241 :=
  ![18, 47, 0, 0, 0, 0, 0, 0, 77, 92, 0, 0, 0, 0, 0, 0, 111, 116, 0, 0, 0, 0, 0, 0, 129, 134, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 18, 0, 0, 0, 0, 0, 0, 92, 77, 0, 0, 0, 0, 0, 0, 116, 111, 0, 0, 0, 0, 0, 0, 134, 129, 0, 0, 0, 0, 153, 154, 0, 0, 0, 0, 0, 0, 155, 156, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156, 155, 0, 0, 0, 0, 0, 0, 154, 153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next019 : Code → Fin 241 :=
  ![19, 0, 0, 0, 65, 0, 0, 0, 75, 0, 0, 0, 104, 0, 0, 0, 112, 0, 0, 0, 121, 0, 0, 0, 130, 0, 0, 0, 139, 0, 0, 0, 75, 0, 0, 0, 104, 0, 0, 0, 19, 0, 0, 0, 65, 0, 0, 0, 130, 0, 0, 0, 139, 0, 0, 0, 112, 0, 0, 0, 121, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next020 : Code → Fin 241 :=
  ![20, 48, 0, 0, 65, 0, 0, 0, 76, 92, 0, 0, 103, 0, 0, 0, 113, 117, 0, 0, 122, 0, 0, 0, 131, 135, 0, 0, 140, 0, 0, 0, 103, 0, 0, 0, 76, 92, 0, 0, 65, 0, 0, 0, 20, 48, 0, 0, 140, 0, 0, 0, 131, 135, 0, 0, 122, 0, 0, 0, 113, 117, 0, 0, 0, 0, 159, 160, 0, 0, 0, 0, 0, 0, 161, 162, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 164, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 159, 160, 0, 0, 0, 0, 0, 0, 161, 162, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 164]
def next021 : Code → Fin 241 :=
  ![21, 48, 0, 0, 0, 0, 0, 0, 77, 91, 0, 0, 0, 0, 0, 0, 114, 118, 0, 0, 0, 0, 0, 0, 132, 136, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 77, 0, 0, 0, 0, 0, 0, 48, 21, 0, 0, 0, 0, 0, 0, 136, 132, 0, 0, 0, 0, 0, 0, 118, 114, 0, 0, 0, 0, 165, 166, 0, 0, 0, 0, 0, 0, 167, 168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 166, 165, 0, 0, 0, 0, 0, 0, 168, 167, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next022 : Code → Fin 241 :=
  ![22, 0, 0, 0, 66, 0, 0, 0, 78, 0, 0, 0, 105, 0, 0, 0, 109, 0, 0, 0, 120, 0, 0, 0, 130, 0, 0, 0, 140, 0, 0, 0, 109, 0, 0, 0, 120, 0, 0, 0, 130, 0, 0, 0, 140, 0, 0, 0, 22, 0, 0, 0, 66, 0, 0, 0, 78, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 172]
def next023 : Code → Fin 241 :=
  ![23, 49, 0, 0, 66, 0, 0, 0, 79, 93, 0, 0, 106, 0, 0, 0, 110, 116, 0, 0, 119, 0, 0, 0, 131, 136, 0, 0, 139, 0, 0, 0, 119, 0, 0, 0, 110, 116, 0, 0, 139, 0, 0, 0, 131, 136, 0, 0, 66, 0, 0, 0, 23, 49, 0, 0, 106, 0, 0, 0, 79, 93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next024 : Code → Fin 241 :=
  ![24, 49, 0, 0, 0, 0, 0, 0, 80, 94, 0, 0, 0, 0, 0, 0, 111, 115, 0, 0, 0, 0, 0, 0, 132, 135, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 115, 111, 0, 0, 0, 0, 0, 0, 135, 132, 0, 0, 0, 0, 0, 0, 49, 24, 0, 0, 0, 0, 0, 0, 94, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next025 : Code → Fin 241 :=
  ![25, 0, 0, 0, 67, 0, 0, 0, 78, 0, 0, 0, 106, 0, 0, 0, 112, 0, 0, 0, 122, 0, 0, 0, 127, 0, 0, 0, 138, 0, 0, 0, 127, 0, 0, 0, 138, 0, 0, 0, 112, 0, 0, 0, 122, 0, 0, 0, 78, 0, 0, 0, 106, 0, 0, 0, 25, 0, 0, 0, 67, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 175]
def next026 : Code → Fin 241 :=
  ![26, 50, 0, 0, 67, 0, 0, 0, 79, 94, 0, 0, 105, 0, 0, 0, 113, 118, 0, 0, 121, 0, 0, 0, 128, 134, 0, 0, 137, 0, 0, 0, 137, 0, 0, 0, 128, 134, 0, 0, 121, 0, 0, 0, 113, 118, 0, 0, 105, 0, 0, 0, 79, 94, 0, 0, 67, 0, 0, 0, 26, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next027 : Code → Fin 241 :=
  ![27, 50, 0, 0, 0, 0, 0, 0, 80, 93, 0, 0, 0, 0, 0, 0, 114, 117, 0, 0, 0, 0, 0, 0, 129, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133, 129, 0, 0, 0, 0, 0, 0, 117, 114, 0, 0, 0, 0, 0, 0, 93, 80, 0, 0, 0, 0, 0, 0, 50, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next028 : Code → Fin 241 :=
  ![28, 0, 58, 0, 0, 0, 0, 0, 81, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 58, 0, 0, 0, 0, 0, 81, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next029 : Code → Fin 241 :=
  ![29, 51, 58, 0, 0, 0, 0, 0, 82, 95, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 153, 0, 0, 0, 0, 0, 0, 159, 165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 29, 51, 0, 0, 0, 0, 100, 0, 82, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 159, 165, 0, 0, 0, 0, 0, 0, 147, 153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next030 : Code → Fin 241 :=
  ![30, 51, 0, 0, 0, 0, 0, 0, 83, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 148, 154, 0, 0, 0, 0, 0, 0, 160, 166, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 30, 0, 0, 0, 0, 0, 0, 96, 83, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 166, 160, 0, 0, 0, 0, 0, 0, 154, 148, 0, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 123]
def next031 : Code → Fin 241 :=
  ![31, 0, 59, 0, 0, 0, 0, 0, 81, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 0, 100, 0, 0, 0, 0, 0, 31, 0, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next032 : Code → Fin 241 :=
  ![32, 52, 59, 0, 0, 0, 0, 0, 82, 96, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 155, 0, 0, 0, 0, 0, 0, 161, 167, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 82, 96, 0, 0, 0, 0, 59, 0, 32, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 155, 0, 0, 0, 0, 0, 0, 161, 167, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next033 : Code → Fin 241 :=
  ![33, 52, 0, 0, 0, 0, 0, 0, 83, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 0, 0, 0, 150, 156, 0, 0, 0, 0, 0, 0, 162, 168, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 0, 0, 95, 83, 0, 0, 0, 0, 0, 0, 52, 33, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156, 150, 0, 0, 0, 0, 0, 0, 168, 162, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 142]
def next034 : Code → Fin 241 :=
  ![34, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 151]
def next035 : Code → Fin 241 :=
  ![35, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 164, 0, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 164]
def next036 : Code → Fin 241 :=
  ![36, 0, 0, 0, 0, 0, 70, 0, 85, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 70, 0, 85, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next037 : Code → Fin 241 :=
  ![37, 53, 0, 0, 0, 0, 70, 0, 86, 97, 0, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 156, 0, 0, 0, 0, 0, 0, 159, 166, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 159, 166, 0, 0, 0, 0, 0, 0, 149, 156, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 37, 53, 108, 0, 0, 0, 0, 0, 86, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next038 : Code → Fin 241 :=
  ![38, 53, 0, 0, 0, 0, 0, 0, 87, 98, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 150, 155, 0, 0, 0, 0, 0, 0, 160, 165, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165, 160, 0, 0, 0, 0, 0, 0, 155, 150, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 38, 0, 0, 0, 0, 0, 0, 98, 87, 0, 0, 0, 0, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 175]
def next039 : Code → Fin 241 :=
  ![39, 0, 0, 0, 0, 0, 71, 0, 85, 0, 0, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 0, 0, 0, 0, 0, 108, 0, 39, 0, 0, 0, 0, 0, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next040 : Code → Fin 241 :=
  ![40, 54, 0, 0, 0, 0, 71, 0, 86, 98, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 154, 0, 0, 0, 0, 0, 0, 161, 168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 154, 0, 0, 0, 0, 0, 0, 161, 168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 86, 98, 71, 0, 0, 0, 0, 0, 40, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next041 : Code → Fin 241 :=
  ![41, 54, 0, 0, 0, 0, 0, 0, 87, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 148, 153, 0, 0, 0, 0, 0, 0, 162, 167, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 0, 0, 153, 148, 0, 0, 0, 0, 0, 0, 167, 162, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97, 87, 0, 0, 0, 0, 0, 0, 54, 41, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 172]
def next042 : Code → Fin 241 :=
  ![42, 0, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 88]
def next043 : Code → Fin 241 :=
  ![43, 0, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 0, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 164, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 0, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 164, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 0, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 43]
def next044 : Code → Fin 241 :=
  ![44, 44, 0, 0, 0, 0, 0, 0, 44, 44, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next045 : Code → Fin 241 :=
  ![45, 45, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 45, 45, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next046 : Code → Fin 241 :=
  ![46, 46, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 46, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next047 : Code → Fin 241 :=
  ![47, 47, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 47, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next048 : Code → Fin 241 :=
  ![48, 48, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 48, 48, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next049 : Code → Fin 241 :=
  ![49, 49, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 49, 49, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next050 : Code → Fin 241 :=
  ![50, 50, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 0, 0, 50, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next051 : Code → Fin 241 :=
  ![51, 51, 0, 0, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 51, 0, 0, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next052 : Code → Fin 241 :=
  ![52, 52, 0, 0, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 52, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next053 : Code → Fin 241 :=
  ![53, 53, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 53, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next054 : Code → Fin 241 :=
  ![54, 54, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 54, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next055 : Code → Fin 241 :=
  ![55, 0, 55, 0, 55, 0, 55, 0, 190, 0, 190, 0, 190, 0, 190, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next056 : Code → Fin 241 :=
  ![56, 0, 56, 0, 190, 0, 190, 0, 56, 0, 56, 0, 190, 0, 190, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next057 : Code → Fin 241 :=
  ![57, 0, 57, 0, 190, 0, 190, 0, 190, 0, 190, 0, 57, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next058 : Code → Fin 241 :=
  ![58, 0, 58, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 58, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next059 : Code → Fin 241 :=
  ![59, 0, 59, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 59, 0, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next060 : Code → Fin 241 :=
  ![60, 0, 190, 0, 60, 0, 190, 0, 60, 0, 190, 0, 60, 0, 190, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next061 : Code → Fin 241 :=
  ![61, 0, 190, 0, 61, 0, 190, 0, 190, 0, 61, 0, 190, 0, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next062 : Code → Fin 241 :=
  ![62, 0, 0, 0, 62, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 62, 0, 0, 0, 62, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next063 : Code → Fin 241 :=
  ![63, 0, 0, 0, 63, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 63, 0, 0, 0, 63, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next064 : Code → Fin 241 :=
  ![64, 0, 0, 0, 64, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 64, 0, 0, 0, 64, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next065 : Code → Fin 241 :=
  ![65, 0, 0, 0, 65, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 65, 0, 0, 0, 65, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next066 : Code → Fin 241 :=
  ![66, 0, 0, 0, 66, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 66, 0, 0, 0, 66, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next067 : Code → Fin 241 :=
  ![67, 0, 0, 0, 67, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 67, 0, 0, 0, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next068 : Code → Fin 241 :=
  ![68, 0, 190, 0, 190, 0, 68, 0, 68, 0, 190, 0, 190, 0, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 199, 0, 199, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next069 : Code → Fin 241 :=
  ![69, 0, 190, 0, 190, 0, 69, 0, 190, 0, 69, 0, 69, 0, 190, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next070 : Code → Fin 241 :=
  ![70, 0, 0, 0, 0, 0, 70, 0, 199, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 70, 0, 199, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next071 : Code → Fin 241 :=
  ![71, 0, 0, 0, 0, 0, 71, 0, 199, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 199, 0, 71, 0, 0, 0, 0, 0, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next072 : Code → Fin 241 :=
  ![72, 177, 0, 0, 192, 0, 0, 0, 72, 177, 0, 0, 192, 0, 0, 0, 72, 177, 0, 0, 192, 0, 0, 0, 72, 177, 0, 0, 192, 0, 0, 0, 200, 0, 0, 0, 201, 202, 0, 0, 200, 0, 0, 0, 201, 202, 0, 0, 200, 0, 0, 0, 201, 202, 0, 0, 200, 0, 0, 0, 201, 202, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next073 : Code → Fin 241 :=
  ![73, 177, 0, 0, 0, 0, 0, 0, 73, 177, 0, 0, 0, 0, 0, 0, 177, 73, 0, 0, 0, 0, 0, 0, 177, 73, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 203, 204, 0, 0, 0, 0, 0, 0, 203, 204, 0, 0, 0, 0, 0, 0, 204, 203, 0, 0, 0, 0, 0, 0, 204, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next074 : Code → Fin 241 :=
  ![74, 0, 0, 0, 192, 0, 0, 0, 74, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 74, 0, 0, 0, 192, 0, 0, 0, 74, 0, 0, 0, 205, 0, 0, 0, 206, 0, 0, 0, 205, 0, 0, 0, 206, 0, 0, 0, 206, 0, 0, 0, 205, 0, 0, 0, 206, 0, 0, 0, 205, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207]
def next075 : Code → Fin 241 :=
  ![75, 0, 0, 0, 193, 0, 0, 0, 75, 0, 0, 0, 193, 0, 0, 0, 200, 0, 0, 0, 205, 0, 0, 0, 200, 0, 0, 0, 205, 0, 0, 0, 75, 0, 0, 0, 193, 0, 0, 0, 75, 0, 0, 0, 193, 0, 0, 0, 200, 0, 0, 0, 205, 0, 0, 0, 200, 0, 0, 0, 205, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next076 : Code → Fin 241 :=
  ![76, 178, 0, 0, 193, 0, 0, 0, 76, 178, 0, 0, 193, 0, 0, 0, 201, 203, 0, 0, 206, 0, 0, 0, 201, 203, 0, 0, 206, 0, 0, 0, 193, 0, 0, 0, 76, 178, 0, 0, 193, 0, 0, 0, 76, 178, 0, 0, 206, 0, 0, 0, 201, 203, 0, 0, 206, 0, 0, 0, 201, 203, 0, 0, 0, 0, 210, 211, 0, 0, 0, 0, 0, 0, 210, 211, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 211, 0, 0, 0, 0, 0, 0, 210, 211, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212]
def next077 : Code → Fin 241 :=
  ![77, 178, 0, 0, 0, 0, 0, 0, 77, 178, 0, 0, 0, 0, 0, 0, 202, 204, 0, 0, 0, 0, 0, 0, 202, 204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178, 77, 0, 0, 0, 0, 0, 0, 178, 77, 0, 0, 0, 0, 0, 0, 204, 202, 0, 0, 0, 0, 0, 0, 204, 202, 0, 0, 0, 0, 213, 214, 0, 0, 0, 0, 0, 0, 213, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 213, 0, 0, 0, 0, 0, 0, 214, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next078 : Code → Fin 241 :=
  ![78, 0, 0, 0, 194, 0, 0, 0, 78, 0, 0, 0, 194, 0, 0, 0, 200, 0, 0, 0, 206, 0, 0, 0, 200, 0, 0, 0, 206, 0, 0, 0, 200, 0, 0, 0, 206, 0, 0, 0, 200, 0, 0, 0, 206, 0, 0, 0, 78, 0, 0, 0, 194, 0, 0, 0, 78, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216]
def next079 : Code → Fin 241 :=
  ![79, 179, 0, 0, 194, 0, 0, 0, 79, 179, 0, 0, 194, 0, 0, 0, 201, 204, 0, 0, 205, 0, 0, 0, 201, 204, 0, 0, 205, 0, 0, 0, 205, 0, 0, 0, 201, 204, 0, 0, 205, 0, 0, 0, 201, 204, 0, 0, 194, 0, 0, 0, 79, 179, 0, 0, 194, 0, 0, 0, 79, 179, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next080 : Code → Fin 241 :=
  ![80, 179, 0, 0, 0, 0, 0, 0, 80, 179, 0, 0, 0, 0, 0, 0, 202, 203, 0, 0, 0, 0, 0, 0, 202, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 203, 202, 0, 0, 0, 0, 0, 0, 203, 202, 0, 0, 0, 0, 0, 0, 179, 80, 0, 0, 0, 0, 0, 0, 179, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next081 : Code → Fin 241 :=
  ![81, 0, 191, 0, 0, 0, 0, 0, 81, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 0, 191, 0, 0, 0, 0, 0, 81, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next082 : Code → Fin 241 :=
  ![82, 180, 191, 0, 0, 0, 0, 0, 82, 180, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 213, 0, 0, 0, 0, 0, 0, 210, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191, 0, 82, 180, 0, 0, 0, 0, 191, 0, 82, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 213, 0, 0, 0, 0, 0, 0, 210, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next083 : Code → Fin 241 :=
  ![83, 180, 0, 0, 0, 0, 0, 0, 83, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 211, 214, 0, 0, 0, 0, 0, 0, 211, 214, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 83, 0, 0, 0, 0, 0, 0, 180, 83, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 211, 0, 0, 0, 0, 0, 0, 214, 211, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207]
def next084 : Code → Fin 241 :=
  ![84, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212]
def next085 : Code → Fin 241 :=
  ![85, 0, 0, 0, 0, 0, 199, 0, 85, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 0, 0, 0, 0, 0, 199, 0, 85, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next086 : Code → Fin 241 :=
  ![86, 181, 0, 0, 0, 0, 199, 0, 86, 181, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 214, 0, 0, 0, 0, 0, 0, 210, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 214, 0, 0, 0, 0, 0, 0, 210, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 86, 181, 199, 0, 0, 0, 0, 0, 86, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next087 : Code → Fin 241 :=
  ![87, 181, 0, 0, 0, 0, 0, 0, 87, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 211, 213, 0, 0, 0, 0, 0, 0, 211, 213, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213, 211, 0, 0, 0, 0, 0, 0, 213, 211, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181, 87, 0, 0, 0, 0, 0, 0, 181, 87, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216]
def next088 : Code → Fin 241 :=
  ![88, 0, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 88]
def next089 : Code → Fin 241 :=
  ![89, 177, 0, 0, 0, 0, 0, 0, 177, 89, 0, 0, 0, 0, 0, 0, 89, 177, 0, 0, 0, 0, 0, 0, 177, 89, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 217, 218, 0, 0, 0, 0, 0, 0, 218, 217, 0, 0, 0, 0, 0, 0, 217, 218, 0, 0, 0, 0, 0, 0, 218, 217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next090 : Code → Fin 241 :=
  ![90, 177, 0, 0, 0, 0, 0, 0, 177, 90, 0, 0, 0, 0, 0, 0, 177, 90, 0, 0, 0, 0, 0, 0, 90, 177, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 219, 220, 0, 0, 0, 0, 0, 0, 220, 219, 0, 0, 0, 0, 0, 0, 220, 219, 0, 0, 0, 0, 0, 0, 219, 220, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next091 : Code → Fin 241 :=
  ![91, 178, 0, 0, 0, 0, 0, 0, 178, 91, 0, 0, 0, 0, 0, 0, 217, 219, 0, 0, 0, 0, 0, 0, 219, 217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 178, 0, 0, 0, 0, 0, 0, 178, 91, 0, 0, 0, 0, 0, 0, 217, 219, 0, 0, 0, 0, 0, 0, 219, 217, 0, 0, 0, 0, 221, 222, 0, 0, 0, 0, 0, 0, 222, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 221, 0, 0, 0, 0, 0, 0, 221, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next092 : Code → Fin 241 :=
  ![92, 178, 0, 0, 0, 0, 0, 0, 178, 92, 0, 0, 0, 0, 0, 0, 218, 220, 0, 0, 0, 0, 0, 0, 220, 218, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178, 92, 0, 0, 0, 0, 0, 0, 92, 178, 0, 0, 0, 0, 0, 0, 220, 218, 0, 0, 0, 0, 0, 0, 218, 220, 0, 0, 0, 0, 223, 224, 0, 0, 0, 0, 0, 0, 224, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 224, 0, 0, 0, 0, 0, 0, 224, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next093 : Code → Fin 241 :=
  ![93, 179, 0, 0, 0, 0, 0, 0, 179, 93, 0, 0, 0, 0, 0, 0, 217, 220, 0, 0, 0, 0, 0, 0, 220, 217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 217, 220, 0, 0, 0, 0, 0, 0, 220, 217, 0, 0, 0, 0, 0, 0, 93, 179, 0, 0, 0, 0, 0, 0, 179, 93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next094 : Code → Fin 241 :=
  ![94, 179, 0, 0, 0, 0, 0, 0, 179, 94, 0, 0, 0, 0, 0, 0, 218, 219, 0, 0, 0, 0, 0, 0, 219, 218, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 219, 218, 0, 0, 0, 0, 0, 0, 218, 219, 0, 0, 0, 0, 0, 0, 179, 94, 0, 0, 0, 0, 0, 0, 94, 179, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next095 : Code → Fin 241 :=
  ![95, 180, 0, 0, 0, 0, 0, 0, 180, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 223, 0, 0, 0, 0, 0, 0, 223, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 95, 180, 0, 0, 0, 0, 0, 0, 180, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 221, 0, 0, 0, 0, 0, 0, 221, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next096 : Code → Fin 241 :=
  ![96, 180, 0, 0, 0, 0, 0, 0, 180, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 224, 0, 0, 0, 0, 0, 0, 224, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 96, 0, 0, 0, 0, 0, 0, 96, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 224, 0, 0, 0, 0, 0, 0, 224, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next097 : Code → Fin 241 :=
  ![97, 181, 0, 0, 0, 0, 0, 0, 181, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 223, 0, 0, 0, 0, 0, 0, 223, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 222, 0, 0, 0, 0, 0, 0, 222, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97, 181, 0, 0, 0, 0, 0, 0, 181, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next098 : Code → Fin 241 :=
  ![98, 181, 0, 0, 0, 0, 0, 0, 181, 98, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 224, 0, 0, 0, 0, 0, 0, 224, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 224, 0, 0, 0, 0, 0, 0, 224, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181, 98, 0, 0, 0, 0, 0, 0, 98, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next099 : Code → Fin 241 :=
  ![99, 0, 191, 0, 0, 0, 0, 0, 191, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 191, 0, 0, 0, 0, 0, 191, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next100 : Code → Fin 241 :=
  ![100, 0, 191, 0, 0, 0, 0, 0, 191, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191, 0, 100, 0, 0, 0, 0, 0, 100, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next101 : Code → Fin 241 :=
  ![101, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 101, 0, 0, 0, 101, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 101, 0, 0, 0, 225, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next102 : Code → Fin 241 :=
  ![102, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 102, 0, 0, 0, 192, 0, 0, 0, 102, 0, 0, 0, 102, 0, 0, 0, 192, 0, 0, 0, 227, 0, 0, 0, 228, 0, 0, 0, 228, 0, 0, 0, 227, 0, 0, 0, 228, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 228, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next103 : Code → Fin 241 :=
  ![103, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 103, 0, 0, 0, 225, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 225, 0, 0, 0, 103, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 103, 0, 0, 0, 225, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next104 : Code → Fin 241 :=
  ![104, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 104, 0, 0, 0, 226, 0, 0, 0, 228, 0, 0, 0, 228, 0, 0, 0, 226, 0, 0, 0, 193, 0, 0, 0, 104, 0, 0, 0, 104, 0, 0, 0, 193, 0, 0, 0, 228, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 228, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next105 : Code → Fin 241 :=
  ![105, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 105, 0, 0, 0, 225, 0, 0, 0, 228, 0, 0, 0, 228, 0, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 228, 0, 0, 0, 228, 0, 0, 0, 225, 0, 0, 0, 105, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next106 : Code → Fin 241 :=
  ![106, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 106, 0, 0, 0, 226, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 226, 0, 0, 0, 227, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 227, 0, 0, 0, 194, 0, 0, 0, 106, 0, 0, 0, 106, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next107 : Code → Fin 241 :=
  ![107, 0, 0, 0, 0, 0, 199, 0, 199, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 199, 0, 199, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next108 : Code → Fin 241 :=
  ![108, 0, 0, 0, 0, 0, 199, 0, 199, 0, 0, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 108, 0, 108, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next109 : Code → Fin 241 :=
  ![109, 0, 0, 0, 195, 0, 0, 0, 200, 0, 0, 0, 225, 0, 0, 0, 109, 0, 0, 0, 195, 0, 0, 0, 200, 0, 0, 0, 225, 0, 0, 0, 109, 0, 0, 0, 195, 0, 0, 0, 200, 0, 0, 0, 225, 0, 0, 0, 109, 0, 0, 0, 195, 0, 0, 0, 200, 0, 0, 0, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next110 : Code → Fin 241 :=
  ![110, 182, 0, 0, 195, 0, 0, 0, 201, 217, 0, 0, 226, 0, 0, 0, 110, 182, 0, 0, 195, 0, 0, 0, 201, 217, 0, 0, 226, 0, 0, 0, 195, 0, 0, 0, 110, 182, 0, 0, 226, 0, 0, 0, 201, 217, 0, 0, 195, 0, 0, 0, 110, 182, 0, 0, 226, 0, 0, 0, 201, 217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next111 : Code → Fin 241 :=
  ![111, 182, 0, 0, 0, 0, 0, 0, 202, 218, 0, 0, 0, 0, 0, 0, 111, 182, 0, 0, 0, 0, 0, 0, 202, 218, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 182, 111, 0, 0, 0, 0, 0, 0, 218, 202, 0, 0, 0, 0, 0, 0, 182, 111, 0, 0, 0, 0, 0, 0, 218, 202, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next112 : Code → Fin 241 :=
  ![112, 0, 0, 0, 196, 0, 0, 0, 200, 0, 0, 0, 226, 0, 0, 0, 112, 0, 0, 0, 196, 0, 0, 0, 200, 0, 0, 0, 226, 0, 0, 0, 200, 0, 0, 0, 226, 0, 0, 0, 112, 0, 0, 0, 196, 0, 0, 0, 200, 0, 0, 0, 226, 0, 0, 0, 112, 0, 0, 0, 196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next113 : Code → Fin 241 :=
  ![113, 183, 0, 0, 196, 0, 0, 0, 201, 218, 0, 0, 225, 0, 0, 0, 113, 183, 0, 0, 196, 0, 0, 0, 201, 218, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 201, 218, 0, 0, 196, 0, 0, 0, 113, 183, 0, 0, 225, 0, 0, 0, 201, 218, 0, 0, 196, 0, 0, 0, 113, 183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next114 : Code → Fin 241 :=
  ![114, 183, 0, 0, 0, 0, 0, 0, 202, 217, 0, 0, 0, 0, 0, 0, 114, 183, 0, 0, 0, 0, 0, 0, 202, 217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 217, 202, 0, 0, 0, 0, 0, 0, 183, 114, 0, 0, 0, 0, 0, 0, 217, 202, 0, 0, 0, 0, 0, 0, 183, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next115 : Code → Fin 241 :=
  ![115, 182, 0, 0, 0, 0, 0, 0, 203, 219, 0, 0, 0, 0, 0, 0, 182, 115, 0, 0, 0, 0, 0, 0, 219, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 115, 182, 0, 0, 0, 0, 0, 0, 203, 219, 0, 0, 0, 0, 0, 0, 182, 115, 0, 0, 0, 0, 0, 0, 219, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next116 : Code → Fin 241 :=
  ![116, 182, 0, 0, 0, 0, 0, 0, 204, 220, 0, 0, 0, 0, 0, 0, 182, 116, 0, 0, 0, 0, 0, 0, 220, 204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 182, 116, 0, 0, 0, 0, 0, 0, 220, 204, 0, 0, 0, 0, 0, 0, 116, 182, 0, 0, 0, 0, 0, 0, 204, 220, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next117 : Code → Fin 241 :=
  ![117, 183, 0, 0, 0, 0, 0, 0, 203, 220, 0, 0, 0, 0, 0, 0, 183, 117, 0, 0, 0, 0, 0, 0, 220, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 203, 220, 0, 0, 0, 0, 0, 0, 117, 183, 0, 0, 0, 0, 0, 0, 220, 203, 0, 0, 0, 0, 0, 0, 183, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next118 : Code → Fin 241 :=
  ![118, 183, 0, 0, 0, 0, 0, 0, 204, 219, 0, 0, 0, 0, 0, 0, 183, 118, 0, 0, 0, 0, 0, 0, 219, 204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 219, 204, 0, 0, 0, 0, 0, 0, 183, 118, 0, 0, 0, 0, 0, 0, 204, 219, 0, 0, 0, 0, 0, 0, 118, 183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next119 : Code → Fin 241 :=
  ![119, 0, 0, 0, 195, 0, 0, 0, 205, 0, 0, 0, 227, 0, 0, 0, 195, 0, 0, 0, 119, 0, 0, 0, 227, 0, 0, 0, 205, 0, 0, 0, 119, 0, 0, 0, 195, 0, 0, 0, 205, 0, 0, 0, 227, 0, 0, 0, 195, 0, 0, 0, 119, 0, 0, 0, 227, 0, 0, 0, 205, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next120 : Code → Fin 241 :=
  ![120, 0, 0, 0, 195, 0, 0, 0, 206, 0, 0, 0, 228, 0, 0, 0, 195, 0, 0, 0, 120, 0, 0, 0, 228, 0, 0, 0, 206, 0, 0, 0, 195, 0, 0, 0, 120, 0, 0, 0, 228, 0, 0, 0, 206, 0, 0, 0, 120, 0, 0, 0, 195, 0, 0, 0, 206, 0, 0, 0, 228, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 229]
def next121 : Code → Fin 241 :=
  ![121, 0, 0, 0, 196, 0, 0, 0, 205, 0, 0, 0, 228, 0, 0, 0, 196, 0, 0, 0, 121, 0, 0, 0, 228, 0, 0, 0, 205, 0, 0, 0, 205, 0, 0, 0, 228, 0, 0, 0, 121, 0, 0, 0, 196, 0, 0, 0, 228, 0, 0, 0, 205, 0, 0, 0, 196, 0, 0, 0, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next122 : Code → Fin 241 :=
  ![122, 0, 0, 0, 196, 0, 0, 0, 206, 0, 0, 0, 227, 0, 0, 0, 196, 0, 0, 0, 122, 0, 0, 0, 227, 0, 0, 0, 206, 0, 0, 0, 227, 0, 0, 0, 206, 0, 0, 0, 196, 0, 0, 0, 122, 0, 0, 0, 206, 0, 0, 0, 227, 0, 0, 0, 122, 0, 0, 0, 196, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 231]
def next123 : Code → Fin 241 :=
  ![123, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 123]
def next124 : Code → Fin 241 :=
  ![124, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 207]
def next125 : Code → Fin 241 :=
  ![125, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 229]
def next126 : Code → Fin 241 :=
  ![126, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 231]
def next127 : Code → Fin 241 :=
  ![127, 0, 0, 0, 197, 0, 0, 0, 200, 0, 0, 0, 227, 0, 0, 0, 200, 0, 0, 0, 227, 0, 0, 0, 127, 0, 0, 0, 197, 0, 0, 0, 127, 0, 0, 0, 197, 0, 0, 0, 200, 0, 0, 0, 227, 0, 0, 0, 200, 0, 0, 0, 227, 0, 0, 0, 127, 0, 0, 0, 197, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next128 : Code → Fin 241 :=
  ![128, 184, 0, 0, 197, 0, 0, 0, 201, 219, 0, 0, 228, 0, 0, 0, 201, 219, 0, 0, 228, 0, 0, 0, 128, 184, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 128, 184, 0, 0, 228, 0, 0, 0, 201, 219, 0, 0, 228, 0, 0, 0, 201, 219, 0, 0, 197, 0, 0, 0, 128, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next129 : Code → Fin 241 :=
  ![129, 184, 0, 0, 0, 0, 0, 0, 202, 220, 0, 0, 0, 0, 0, 0, 202, 220, 0, 0, 0, 0, 0, 0, 129, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 184, 129, 0, 0, 0, 0, 0, 0, 220, 202, 0, 0, 0, 0, 0, 0, 220, 202, 0, 0, 0, 0, 0, 0, 184, 129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next130 : Code → Fin 241 :=
  ![130, 0, 0, 0, 198, 0, 0, 0, 200, 0, 0, 0, 228, 0, 0, 0, 200, 0, 0, 0, 228, 0, 0, 0, 130, 0, 0, 0, 198, 0, 0, 0, 200, 0, 0, 0, 228, 0, 0, 0, 130, 0, 0, 0, 198, 0, 0, 0, 130, 0, 0, 0, 198, 0, 0, 0, 200, 0, 0, 0, 228, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next131 : Code → Fin 241 :=
  ![131, 185, 0, 0, 198, 0, 0, 0, 201, 220, 0, 0, 227, 0, 0, 0, 201, 220, 0, 0, 227, 0, 0, 0, 131, 185, 0, 0, 198, 0, 0, 0, 227, 0, 0, 0, 201, 220, 0, 0, 198, 0, 0, 0, 131, 185, 0, 0, 198, 0, 0, 0, 131, 185, 0, 0, 227, 0, 0, 0, 201, 220, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next132 : Code → Fin 241 :=
  ![132, 185, 0, 0, 0, 0, 0, 0, 202, 219, 0, 0, 0, 0, 0, 0, 202, 219, 0, 0, 0, 0, 0, 0, 132, 185, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 219, 202, 0, 0, 0, 0, 0, 0, 185, 132, 0, 0, 0, 0, 0, 0, 185, 132, 0, 0, 0, 0, 0, 0, 219, 202, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next133 : Code → Fin 241 :=
  ![133, 184, 0, 0, 0, 0, 0, 0, 203, 217, 0, 0, 0, 0, 0, 0, 217, 203, 0, 0, 0, 0, 0, 0, 184, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133, 184, 0, 0, 0, 0, 0, 0, 203, 217, 0, 0, 0, 0, 0, 0, 217, 203, 0, 0, 0, 0, 0, 0, 184, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next134 : Code → Fin 241 :=
  ![134, 184, 0, 0, 0, 0, 0, 0, 204, 218, 0, 0, 0, 0, 0, 0, 218, 204, 0, 0, 0, 0, 0, 0, 184, 134, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 184, 134, 0, 0, 0, 0, 0, 0, 218, 204, 0, 0, 0, 0, 0, 0, 204, 218, 0, 0, 0, 0, 0, 0, 134, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next135 : Code → Fin 241 :=
  ![135, 185, 0, 0, 0, 0, 0, 0, 203, 218, 0, 0, 0, 0, 0, 0, 218, 203, 0, 0, 0, 0, 0, 0, 185, 135, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 203, 218, 0, 0, 0, 0, 0, 0, 135, 185, 0, 0, 0, 0, 0, 0, 185, 135, 0, 0, 0, 0, 0, 0, 218, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next136 : Code → Fin 241 :=
  ![136, 185, 0, 0, 0, 0, 0, 0, 204, 217, 0, 0, 0, 0, 0, 0, 217, 204, 0, 0, 0, 0, 0, 0, 185, 136, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 217, 204, 0, 0, 0, 0, 0, 0, 185, 136, 0, 0, 0, 0, 0, 0, 136, 185, 0, 0, 0, 0, 0, 0, 204, 217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next137 : Code → Fin 241 :=
  ![137, 0, 0, 0, 197, 0, 0, 0, 205, 0, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 205, 0, 0, 0, 197, 0, 0, 0, 137, 0, 0, 0, 137, 0, 0, 0, 197, 0, 0, 0, 205, 0, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 205, 0, 0, 0, 197, 0, 0, 0, 137, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next138 : Code → Fin 241 :=
  ![138, 0, 0, 0, 197, 0, 0, 0, 206, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 206, 0, 0, 0, 197, 0, 0, 0, 138, 0, 0, 0, 197, 0, 0, 0, 138, 0, 0, 0, 226, 0, 0, 0, 206, 0, 0, 0, 206, 0, 0, 0, 226, 0, 0, 0, 138, 0, 0, 0, 197, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 234]
def next139 : Code → Fin 241 :=
  ![139, 0, 0, 0, 198, 0, 0, 0, 205, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 205, 0, 0, 0, 198, 0, 0, 0, 139, 0, 0, 0, 205, 0, 0, 0, 226, 0, 0, 0, 139, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 139, 0, 0, 0, 226, 0, 0, 0, 205, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next140 : Code → Fin 241 :=
  ![140, 0, 0, 0, 198, 0, 0, 0, 206, 0, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 206, 0, 0, 0, 198, 0, 0, 0, 140, 0, 0, 0, 225, 0, 0, 0, 206, 0, 0, 0, 198, 0, 0, 0, 140, 0, 0, 0, 140, 0, 0, 0, 198, 0, 0, 0, 206, 0, 0, 0, 225, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 236]
def next141 : Code → Fin 241 :=
  ![141, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 141, 0, 0, 0, 0, 0, 0, 0, 207]
def next142 : Code → Fin 241 :=
  ![142, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 142]
def next143 : Code → Fin 241 :=
  ![143, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 234]
def next144 : Code → Fin 241 :=
  ![144, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 236]
def next145 : Code → Fin 241 :=
  ![145, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next146 : Code → Fin 241 :=
  ![146, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next147 : Code → Fin 241 :=
  ![147, 186, 0, 0, 0, 0, 0, 0, 210, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 186, 0, 0, 0, 0, 0, 0, 210, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 186, 0, 0, 0, 0, 0, 0, 210, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 221, 0, 0, 0, 0, 0, 0, 147, 186, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next148 : Code → Fin 241 :=
  ![148, 186, 0, 0, 0, 0, 0, 0, 211, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 148, 186, 0, 0, 0, 0, 0, 0, 211, 222, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 148, 0, 0, 0, 0, 0, 0, 222, 211, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 211, 0, 0, 0, 0, 0, 0, 186, 148, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 229]
def next149 : Code → Fin 241 :=
  ![149, 187, 0, 0, 0, 0, 0, 0, 210, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 187, 0, 0, 0, 0, 0, 0, 210, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 222, 0, 0, 0, 0, 0, 0, 149, 187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 187, 0, 0, 0, 0, 0, 0, 210, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next150 : Code → Fin 241 :=
  ![150, 187, 0, 0, 0, 0, 0, 0, 211, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 150, 187, 0, 0, 0, 0, 0, 0, 211, 221, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 211, 0, 0, 0, 0, 0, 0, 187, 150, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 150, 0, 0, 0, 0, 0, 0, 221, 211, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 234]
def next151 : Code → Fin 241 :=
  ![151, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 151]
def next152 : Code → Fin 241 :=
  ![152, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 212]
def next153 : Code → Fin 241 :=
  ![153, 186, 0, 0, 0, 0, 0, 0, 213, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 153, 0, 0, 0, 0, 0, 0, 223, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 153, 186, 0, 0, 0, 0, 0, 0, 213, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 213, 0, 0, 0, 0, 0, 0, 186, 153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next154 : Code → Fin 241 :=
  ![154, 186, 0, 0, 0, 0, 0, 0, 214, 224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 154, 0, 0, 0, 0, 0, 0, 224, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 154, 0, 0, 0, 0, 0, 0, 224, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 224, 0, 0, 0, 0, 0, 0, 154, 186, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next155 : Code → Fin 241 :=
  ![155, 187, 0, 0, 0, 0, 0, 0, 213, 224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 155, 0, 0, 0, 0, 0, 0, 224, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213, 224, 0, 0, 0, 0, 0, 0, 155, 187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 155, 0, 0, 0, 0, 0, 0, 224, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next156 : Code → Fin 241 :=
  ![156, 187, 0, 0, 0, 0, 0, 0, 214, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 156, 0, 0, 0, 0, 0, 0, 223, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 214, 0, 0, 0, 0, 0, 0, 187, 156, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156, 187, 0, 0, 0, 0, 0, 0, 214, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next157 : Code → Fin 241 :=
  ![157, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next158 : Code → Fin 241 :=
  ![158, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next159 : Code → Fin 241 :=
  ![159, 188, 0, 0, 0, 0, 0, 0, 210, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 223, 0, 0, 0, 0, 0, 0, 159, 188, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 159, 188, 0, 0, 0, 0, 0, 0, 210, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 159, 188, 0, 0, 0, 0, 0, 0, 210, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next160 : Code → Fin 241 :=
  ![160, 188, 0, 0, 0, 0, 0, 0, 211, 224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 211, 224, 0, 0, 0, 0, 0, 0, 160, 188, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 160, 0, 0, 0, 0, 0, 0, 224, 211, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 160, 0, 0, 0, 0, 0, 0, 224, 211, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 231]
def next161 : Code → Fin 241 :=
  ![161, 189, 0, 0, 0, 0, 0, 0, 210, 224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 0, 0, 0, 0, 0, 0, 161, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 0, 0, 0, 0, 0, 0, 161, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 0, 0, 0, 0, 0, 0, 161, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next162 : Code → Fin 241 :=
  ![162, 189, 0, 0, 0, 0, 0, 0, 211, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 211, 223, 0, 0, 0, 0, 0, 0, 162, 189, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 211, 0, 0, 0, 0, 0, 0, 189, 162, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 211, 0, 0, 0, 0, 0, 0, 189, 162, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 236]
def next163 : Code → Fin 241 :=
  ![163, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 212]
def next164 : Code → Fin 241 :=
  ![164, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 164, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 164, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 164]
def next165 : Code → Fin 241 :=
  ![165, 188, 0, 0, 0, 0, 0, 0, 213, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 213, 0, 0, 0, 0, 0, 0, 188, 165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165, 188, 0, 0, 0, 0, 0, 0, 213, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 165, 0, 0, 0, 0, 0, 0, 221, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next166 : Code → Fin 241 :=
  ![166, 188, 0, 0, 0, 0, 0, 0, 214, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 214, 0, 0, 0, 0, 0, 0, 188, 166, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 166, 0, 0, 0, 0, 0, 0, 222, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 166, 188, 0, 0, 0, 0, 0, 0, 214, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next167 : Code → Fin 241 :=
  ![167, 189, 0, 0, 0, 0, 0, 0, 213, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 213, 0, 0, 0, 0, 0, 0, 189, 167, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213, 222, 0, 0, 0, 0, 0, 0, 167, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 213, 0, 0, 0, 0, 0, 0, 189, 167, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next168 : Code → Fin 241 :=
  ![168, 189, 0, 0, 0, 0, 0, 0, 214, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 214, 0, 0, 0, 0, 0, 0, 189, 168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 214, 0, 0, 0, 0, 0, 0, 189, 168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 221, 0, 0, 0, 0, 0, 0, 168, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next169 : Code → Fin 241 :=
  ![169, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 229]
def next170 : Code → Fin 241 :=
  ![170, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 170, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 236]
def next171 : Code → Fin 241 :=
  ![171, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 216]
def next172 : Code → Fin 241 :=
  ![172, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 172]
def next173 : Code → Fin 241 :=
  ![173, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 231]
def next174 : Code → Fin 241 :=
  ![174, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 234]
def next175 : Code → Fin 241 :=
  ![175, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 175]
def next176 : Code → Fin 241 :=
  ![176, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 0, 0, 216]
def next177 : Code → Fin 241 :=
  ![177, 177, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 177, 177, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next178 : Code → Fin 241 :=
  ![178, 178, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 178, 178, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next179 : Code → Fin 241 :=
  ![179, 179, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 0, 0, 179, 179, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next180 : Code → Fin 241 :=
  ![180, 180, 0, 0, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 180, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next181 : Code → Fin 241 :=
  ![181, 181, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 181, 181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next182 : Code → Fin 241 :=
  ![182, 182, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 182, 182, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next183 : Code → Fin 241 :=
  ![183, 183, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 183, 183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next184 : Code → Fin 241 :=
  ![184, 184, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 184, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next185 : Code → Fin 241 :=
  ![185, 185, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 185, 185, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next186 : Code → Fin 241 :=
  ![186, 186, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 186, 186, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next187 : Code → Fin 241 :=
  ![187, 187, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 187, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next188 : Code → Fin 241 :=
  ![188, 188, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 188, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next189 : Code → Fin 241 :=
  ![189, 189, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 189, 189, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next190 : Code → Fin 241 :=
  ![190, 0, 190, 0, 190, 0, 190, 0, 190, 0, 190, 0, 190, 0, 190, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next191 : Code → Fin 241 :=
  ![191, 0, 191, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 191, 0, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next192 : Code → Fin 241 :=
  ![192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 192, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next193 : Code → Fin 241 :=
  ![193, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 193, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next194 : Code → Fin 241 :=
  ![194, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 194, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next195 : Code → Fin 241 :=
  ![195, 0, 0, 0, 195, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 195, 0, 0, 0, 195, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next196 : Code → Fin 241 :=
  ![196, 0, 0, 0, 196, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 196, 0, 0, 0, 196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next197 : Code → Fin 241 :=
  ![197, 0, 0, 0, 197, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 197, 0, 0, 0, 197, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next198 : Code → Fin 241 :=
  ![198, 0, 0, 0, 198, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 198, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next199 : Code → Fin 241 :=
  ![199, 0, 0, 0, 0, 0, 199, 0, 199, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 199, 0, 199, 0, 0, 0, 0, 0, 199, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next200 : Code → Fin 241 :=
  ![200, 0, 0, 0, 239, 0, 0, 0, 200, 0, 0, 0, 239, 0, 0, 0, 200, 0, 0, 0, 239, 0, 0, 0, 200, 0, 0, 0, 239, 0, 0, 0, 200, 0, 0, 0, 239, 0, 0, 0, 200, 0, 0, 0, 239, 0, 0, 0, 200, 0, 0, 0, 239, 0, 0, 0, 200, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next201 : Code → Fin 241 :=
  ![201, 237, 0, 0, 239, 0, 0, 0, 201, 237, 0, 0, 239, 0, 0, 0, 201, 237, 0, 0, 239, 0, 0, 0, 201, 237, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 201, 237, 0, 0, 239, 0, 0, 0, 201, 237, 0, 0, 239, 0, 0, 0, 201, 237, 0, 0, 239, 0, 0, 0, 201, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next202 : Code → Fin 241 :=
  ![202, 237, 0, 0, 0, 0, 0, 0, 202, 237, 0, 0, 0, 0, 0, 0, 202, 237, 0, 0, 0, 0, 0, 0, 202, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 202, 0, 0, 0, 0, 0, 0, 237, 202, 0, 0, 0, 0, 0, 0, 237, 202, 0, 0, 0, 0, 0, 0, 237, 202, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next203 : Code → Fin 241 :=
  ![203, 237, 0, 0, 0, 0, 0, 0, 203, 237, 0, 0, 0, 0, 0, 0, 237, 203, 0, 0, 0, 0, 0, 0, 237, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 203, 237, 0, 0, 0, 0, 0, 0, 203, 237, 0, 0, 0, 0, 0, 0, 237, 203, 0, 0, 0, 0, 0, 0, 237, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next204 : Code → Fin 241 :=
  ![204, 237, 0, 0, 0, 0, 0, 0, 204, 237, 0, 0, 0, 0, 0, 0, 237, 204, 0, 0, 0, 0, 0, 0, 237, 204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 204, 0, 0, 0, 0, 0, 0, 237, 204, 0, 0, 0, 0, 0, 0, 204, 237, 0, 0, 0, 0, 0, 0, 204, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next205 : Code → Fin 241 :=
  ![205, 0, 0, 0, 239, 0, 0, 0, 205, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 205, 0, 0, 0, 239, 0, 0, 0, 205, 0, 0, 0, 205, 0, 0, 0, 239, 0, 0, 0, 205, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 205, 0, 0, 0, 239, 0, 0, 0, 205, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next206 : Code → Fin 241 :=
  ![206, 0, 0, 0, 239, 0, 0, 0, 206, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 206, 0, 0, 0, 239, 0, 0, 0, 206, 0, 0, 0, 239, 0, 0, 0, 206, 0, 0, 0, 239, 0, 0, 0, 206, 0, 0, 0, 206, 0, 0, 0, 239, 0, 0, 0, 206, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240]
def next207 : Code → Fin 241 :=
  ![207, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 207, 0, 0, 0, 0, 0, 0, 0, 207]
def next208 : Code → Fin 241 :=
  ![208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240]
def next209 : Code → Fin 241 :=
  ![209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next210 : Code → Fin 241 :=
  ![210, 238, 0, 0, 0, 0, 0, 0, 210, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 238, 0, 0, 0, 0, 0, 0, 210, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 238, 0, 0, 0, 0, 0, 0, 210, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 238, 0, 0, 0, 0, 0, 0, 210, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next211 : Code → Fin 241 :=
  ![211, 238, 0, 0, 0, 0, 0, 0, 211, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 211, 238, 0, 0, 0, 0, 0, 0, 211, 238, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 211, 0, 0, 0, 0, 0, 0, 238, 211, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 211, 0, 0, 0, 0, 0, 0, 238, 211, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240]
def next212 : Code → Fin 241 :=
  ![212, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 212]
def next213 : Code → Fin 241 :=
  ![213, 238, 0, 0, 0, 0, 0, 0, 213, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 213, 0, 0, 0, 0, 0, 0, 238, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213, 238, 0, 0, 0, 0, 0, 0, 213, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 213, 0, 0, 0, 0, 0, 0, 238, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next214 : Code → Fin 241 :=
  ![214, 238, 0, 0, 0, 0, 0, 0, 214, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 214, 0, 0, 0, 0, 0, 0, 238, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 214, 0, 0, 0, 0, 0, 0, 238, 214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 238, 0, 0, 0, 0, 0, 0, 214, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next215 : Code → Fin 241 :=
  ![215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240]
def next216 : Code → Fin 241 :=
  ![216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 216]
def next217 : Code → Fin 241 :=
  ![217, 237, 0, 0, 0, 0, 0, 0, 237, 217, 0, 0, 0, 0, 0, 0, 217, 237, 0, 0, 0, 0, 0, 0, 237, 217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 217, 237, 0, 0, 0, 0, 0, 0, 237, 217, 0, 0, 0, 0, 0, 0, 217, 237, 0, 0, 0, 0, 0, 0, 237, 217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next218 : Code → Fin 241 :=
  ![218, 237, 0, 0, 0, 0, 0, 0, 237, 218, 0, 0, 0, 0, 0, 0, 218, 237, 0, 0, 0, 0, 0, 0, 237, 218, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 218, 0, 0, 0, 0, 0, 0, 218, 237, 0, 0, 0, 0, 0, 0, 237, 218, 0, 0, 0, 0, 0, 0, 218, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next219 : Code → Fin 241 :=
  ![219, 237, 0, 0, 0, 0, 0, 0, 237, 219, 0, 0, 0, 0, 0, 0, 237, 219, 0, 0, 0, 0, 0, 0, 219, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 219, 237, 0, 0, 0, 0, 0, 0, 237, 219, 0, 0, 0, 0, 0, 0, 237, 219, 0, 0, 0, 0, 0, 0, 219, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next220 : Code → Fin 241 :=
  ![220, 237, 0, 0, 0, 0, 0, 0, 237, 220, 0, 0, 0, 0, 0, 0, 237, 220, 0, 0, 0, 0, 0, 0, 220, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 220, 0, 0, 0, 0, 0, 0, 220, 237, 0, 0, 0, 0, 0, 0, 220, 237, 0, 0, 0, 0, 0, 0, 237, 220, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next221 : Code → Fin 241 :=
  ![221, 238, 0, 0, 0, 0, 0, 0, 238, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 238, 0, 0, 0, 0, 0, 0, 238, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 238, 0, 0, 0, 0, 0, 0, 238, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 221, 0, 0, 0, 0, 0, 0, 221, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next222 : Code → Fin 241 :=
  ![222, 238, 0, 0, 0, 0, 0, 0, 238, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 238, 0, 0, 0, 0, 0, 0, 238, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 222, 0, 0, 0, 0, 0, 0, 222, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 238, 0, 0, 0, 0, 0, 0, 238, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next223 : Code → Fin 241 :=
  ![223, 238, 0, 0, 0, 0, 0, 0, 238, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 223, 0, 0, 0, 0, 0, 0, 223, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 238, 0, 0, 0, 0, 0, 0, 238, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 223, 238, 0, 0, 0, 0, 0, 0, 238, 223, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next224 : Code → Fin 241 :=
  ![224, 238, 0, 0, 0, 0, 0, 0, 238, 224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 224, 0, 0, 0, 0, 0, 0, 224, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 224, 0, 0, 0, 0, 0, 0, 224, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 224, 0, 0, 0, 0, 0, 0, 224, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next225 : Code → Fin 241 :=
  ![225, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 225, 0, 0, 0, 225, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next226 : Code → Fin 241 :=
  ![226, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 226, 0, 0, 0, 239, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 226, 0, 0, 0, 226, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next227 : Code → Fin 241 :=
  ![227, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 227, 0, 0, 0, 239, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 239, 0, 0, 0, 227, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 227, 0, 0, 0, 239, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next228 : Code → Fin 241 :=
  ![228, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 228, 0, 0, 0, 239, 0, 0, 0, 228, 0, 0, 0, 228, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 228, 0, 0, 0, 228, 0, 0, 0, 239, 0, 0, 0, 228, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 228, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next229 : Code → Fin 241 :=
  ![229, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 229, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 229]
def next230 : Code → Fin 241 :=
  ![230, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 230, 0, 0, 0, 0, 0, 0, 0, 240]
def next231 : Code → Fin 241 :=
  ![231, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 231]
def next232 : Code → Fin 241 :=
  ![232, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 232, 0, 0, 0, 0, 0, 0, 0, 240]
def next233 : Code → Fin 241 :=
  ![233, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 240]
def next234 : Code → Fin 241 :=
  ![234, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 234]
def next235 : Code → Fin 241 :=
  ![235, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 235, 0, 0, 0, 0, 0, 0, 0, 240]
def next236 : Code → Fin 241 :=
  ![236, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 236]
def next237 : Code → Fin 241 :=
  ![237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 237, 237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next238 : Code → Fin 241 :=
  ![238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 238, 238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next239 : Code → Fin 241 :=
  ![239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 239, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def next240 : Code → Fin 241 :=
  ![240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 240]

/-- Supplied output index; invalid extension pairs use the irrelevant value zero. -/
def nextRow (i : Fin 241) (c : Code) : Fin 241 :=
  (if i.val < 120 then
  (if i.val < 60 then
  (if i.val < 30 then
  (if i.val < 15 then
  (if i.val < 7 then
  (if i.val < 3 then
  (if i.val < 1 then
  (next000) else
  (if i.val < 2 then
  (next001) else
  (next002))) else
  (if i.val < 5 then
  (if i.val < 4 then
  (next003) else
  (next004)) else
  (if i.val < 6 then
  (next005) else
  (next006)))) else
  (if i.val < 11 then
  (if i.val < 9 then
  (if i.val < 8 then
  (next007) else
  (next008)) else
  (if i.val < 10 then
  (next009) else
  (next010))) else
  (if i.val < 13 then
  (if i.val < 12 then
  (next011) else
  (next012)) else
  (if i.val < 14 then
  (next013) else
  (next014))))) else
  (if i.val < 22 then
  (if i.val < 18 then
  (if i.val < 16 then
  (next015) else
  (if i.val < 17 then
  (next016) else
  (next017))) else
  (if i.val < 20 then
  (if i.val < 19 then
  (next018) else
  (next019)) else
  (if i.val < 21 then
  (next020) else
  (next021)))) else
  (if i.val < 26 then
  (if i.val < 24 then
  (if i.val < 23 then
  (next022) else
  (next023)) else
  (if i.val < 25 then
  (next024) else
  (next025))) else
  (if i.val < 28 then
  (if i.val < 27 then
  (next026) else
  (next027)) else
  (if i.val < 29 then
  (next028) else
  (next029)))))) else
  (if i.val < 45 then
  (if i.val < 37 then
  (if i.val < 33 then
  (if i.val < 31 then
  (next030) else
  (if i.val < 32 then
  (next031) else
  (next032))) else
  (if i.val < 35 then
  (if i.val < 34 then
  (next033) else
  (next034)) else
  (if i.val < 36 then
  (next035) else
  (next036)))) else
  (if i.val < 41 then
  (if i.val < 39 then
  (if i.val < 38 then
  (next037) else
  (next038)) else
  (if i.val < 40 then
  (next039) else
  (next040))) else
  (if i.val < 43 then
  (if i.val < 42 then
  (next041) else
  (next042)) else
  (if i.val < 44 then
  (next043) else
  (next044))))) else
  (if i.val < 52 then
  (if i.val < 48 then
  (if i.val < 46 then
  (next045) else
  (if i.val < 47 then
  (next046) else
  (next047))) else
  (if i.val < 50 then
  (if i.val < 49 then
  (next048) else
  (next049)) else
  (if i.val < 51 then
  (next050) else
  (next051)))) else
  (if i.val < 56 then
  (if i.val < 54 then
  (if i.val < 53 then
  (next052) else
  (next053)) else
  (if i.val < 55 then
  (next054) else
  (next055))) else
  (if i.val < 58 then
  (if i.val < 57 then
  (next056) else
  (next057)) else
  (if i.val < 59 then
  (next058) else
  (next059))))))) else
  (if i.val < 90 then
  (if i.val < 75 then
  (if i.val < 67 then
  (if i.val < 63 then
  (if i.val < 61 then
  (next060) else
  (if i.val < 62 then
  (next061) else
  (next062))) else
  (if i.val < 65 then
  (if i.val < 64 then
  (next063) else
  (next064)) else
  (if i.val < 66 then
  (next065) else
  (next066)))) else
  (if i.val < 71 then
  (if i.val < 69 then
  (if i.val < 68 then
  (next067) else
  (next068)) else
  (if i.val < 70 then
  (next069) else
  (next070))) else
  (if i.val < 73 then
  (if i.val < 72 then
  (next071) else
  (next072)) else
  (if i.val < 74 then
  (next073) else
  (next074))))) else
  (if i.val < 82 then
  (if i.val < 78 then
  (if i.val < 76 then
  (next075) else
  (if i.val < 77 then
  (next076) else
  (next077))) else
  (if i.val < 80 then
  (if i.val < 79 then
  (next078) else
  (next079)) else
  (if i.val < 81 then
  (next080) else
  (next081)))) else
  (if i.val < 86 then
  (if i.val < 84 then
  (if i.val < 83 then
  (next082) else
  (next083)) else
  (if i.val < 85 then
  (next084) else
  (next085))) else
  (if i.val < 88 then
  (if i.val < 87 then
  (next086) else
  (next087)) else
  (if i.val < 89 then
  (next088) else
  (next089)))))) else
  (if i.val < 105 then
  (if i.val < 97 then
  (if i.val < 93 then
  (if i.val < 91 then
  (next090) else
  (if i.val < 92 then
  (next091) else
  (next092))) else
  (if i.val < 95 then
  (if i.val < 94 then
  (next093) else
  (next094)) else
  (if i.val < 96 then
  (next095) else
  (next096)))) else
  (if i.val < 101 then
  (if i.val < 99 then
  (if i.val < 98 then
  (next097) else
  (next098)) else
  (if i.val < 100 then
  (next099) else
  (next100))) else
  (if i.val < 103 then
  (if i.val < 102 then
  (next101) else
  (next102)) else
  (if i.val < 104 then
  (next103) else
  (next104))))) else
  (if i.val < 112 then
  (if i.val < 108 then
  (if i.val < 106 then
  (next105) else
  (if i.val < 107 then
  (next106) else
  (next107))) else
  (if i.val < 110 then
  (if i.val < 109 then
  (next108) else
  (next109)) else
  (if i.val < 111 then
  (next110) else
  (next111)))) else
  (if i.val < 116 then
  (if i.val < 114 then
  (if i.val < 113 then
  (next112) else
  (next113)) else
  (if i.val < 115 then
  (next114) else
  (next115))) else
  (if i.val < 118 then
  (if i.val < 117 then
  (next116) else
  (next117)) else
  (if i.val < 119 then
  (next118) else
  (next119)))))))) else
  (if i.val < 180 then
  (if i.val < 150 then
  (if i.val < 135 then
  (if i.val < 127 then
  (if i.val < 123 then
  (if i.val < 121 then
  (next120) else
  (if i.val < 122 then
  (next121) else
  (next122))) else
  (if i.val < 125 then
  (if i.val < 124 then
  (next123) else
  (next124)) else
  (if i.val < 126 then
  (next125) else
  (next126)))) else
  (if i.val < 131 then
  (if i.val < 129 then
  (if i.val < 128 then
  (next127) else
  (next128)) else
  (if i.val < 130 then
  (next129) else
  (next130))) else
  (if i.val < 133 then
  (if i.val < 132 then
  (next131) else
  (next132)) else
  (if i.val < 134 then
  (next133) else
  (next134))))) else
  (if i.val < 142 then
  (if i.val < 138 then
  (if i.val < 136 then
  (next135) else
  (if i.val < 137 then
  (next136) else
  (next137))) else
  (if i.val < 140 then
  (if i.val < 139 then
  (next138) else
  (next139)) else
  (if i.val < 141 then
  (next140) else
  (next141)))) else
  (if i.val < 146 then
  (if i.val < 144 then
  (if i.val < 143 then
  (next142) else
  (next143)) else
  (if i.val < 145 then
  (next144) else
  (next145))) else
  (if i.val < 148 then
  (if i.val < 147 then
  (next146) else
  (next147)) else
  (if i.val < 149 then
  (next148) else
  (next149)))))) else
  (if i.val < 165 then
  (if i.val < 157 then
  (if i.val < 153 then
  (if i.val < 151 then
  (next150) else
  (if i.val < 152 then
  (next151) else
  (next152))) else
  (if i.val < 155 then
  (if i.val < 154 then
  (next153) else
  (next154)) else
  (if i.val < 156 then
  (next155) else
  (next156)))) else
  (if i.val < 161 then
  (if i.val < 159 then
  (if i.val < 158 then
  (next157) else
  (next158)) else
  (if i.val < 160 then
  (next159) else
  (next160))) else
  (if i.val < 163 then
  (if i.val < 162 then
  (next161) else
  (next162)) else
  (if i.val < 164 then
  (next163) else
  (next164))))) else
  (if i.val < 172 then
  (if i.val < 168 then
  (if i.val < 166 then
  (next165) else
  (if i.val < 167 then
  (next166) else
  (next167))) else
  (if i.val < 170 then
  (if i.val < 169 then
  (next168) else
  (next169)) else
  (if i.val < 171 then
  (next170) else
  (next171)))) else
  (if i.val < 176 then
  (if i.val < 174 then
  (if i.val < 173 then
  (next172) else
  (next173)) else
  (if i.val < 175 then
  (next174) else
  (next175))) else
  (if i.val < 178 then
  (if i.val < 177 then
  (next176) else
  (next177)) else
  (if i.val < 179 then
  (next178) else
  (next179))))))) else
  (if i.val < 210 then
  (if i.val < 195 then
  (if i.val < 187 then
  (if i.val < 183 then
  (if i.val < 181 then
  (next180) else
  (if i.val < 182 then
  (next181) else
  (next182))) else
  (if i.val < 185 then
  (if i.val < 184 then
  (next183) else
  (next184)) else
  (if i.val < 186 then
  (next185) else
  (next186)))) else
  (if i.val < 191 then
  (if i.val < 189 then
  (if i.val < 188 then
  (next187) else
  (next188)) else
  (if i.val < 190 then
  (next189) else
  (next190))) else
  (if i.val < 193 then
  (if i.val < 192 then
  (next191) else
  (next192)) else
  (if i.val < 194 then
  (next193) else
  (next194))))) else
  (if i.val < 202 then
  (if i.val < 198 then
  (if i.val < 196 then
  (next195) else
  (if i.val < 197 then
  (next196) else
  (next197))) else
  (if i.val < 200 then
  (if i.val < 199 then
  (next198) else
  (next199)) else
  (if i.val < 201 then
  (next200) else
  (next201)))) else
  (if i.val < 206 then
  (if i.val < 204 then
  (if i.val < 203 then
  (next202) else
  (next203)) else
  (if i.val < 205 then
  (next204) else
  (next205))) else
  (if i.val < 208 then
  (if i.val < 207 then
  (next206) else
  (next207)) else
  (if i.val < 209 then
  (next208) else
  (next209)))))) else
  (if i.val < 225 then
  (if i.val < 217 then
  (if i.val < 213 then
  (if i.val < 211 then
  (next210) else
  (if i.val < 212 then
  (next211) else
  (next212))) else
  (if i.val < 215 then
  (if i.val < 214 then
  (next213) else
  (next214)) else
  (if i.val < 216 then
  (next215) else
  (next216)))) else
  (if i.val < 221 then
  (if i.val < 219 then
  (if i.val < 218 then
  (next217) else
  (next218)) else
  (if i.val < 220 then
  (next219) else
  (next220))) else
  (if i.val < 223 then
  (if i.val < 222 then
  (next221) else
  (next222)) else
  (if i.val < 224 then
  (next223) else
  (next224))))) else
  (if i.val < 233 then
  (if i.val < 229 then
  (if i.val < 227 then
  (if i.val < 226 then
  (next225) else
  (next226)) else
  (if i.val < 228 then
  (next227) else
  (next228))) else
  (if i.val < 231 then
  (if i.val < 230 then
  (next229) else
  (next230)) else
  (if i.val < 232 then
  (next231) else
  (next232)))) else
  (if i.val < 237 then
  (if i.val < 235 then
  (if i.val < 234 then
  (next233) else
  (next234)) else
  (if i.val < 236 then
  (next235) else
  (next236))) else
  (if i.val < 239 then
  (if i.val < 238 then
  (next237) else
  (next238)) else
  (if i.val < 240 then
  (next239) else
  (next240))))))))) c

def conjugateWitness (i : Fin 241) : Fin 60 × Code :=
  if i.val < 120 then
  (if i.val < 60 then
  (if i.val < 30 then
  (if i.val < 15 then
  (if i.val < 7 then
  (if i.val < 3 then
  (if i.val < 1 then
  ((0, 0)) else
  (if i.val < 2 then
  ((0, 0)) else
  ((1, 0)))) else
  (if i.val < 5 then
  (if i.val < 4 then
  ((2, 0)) else
  ((1, 16))) else
  (if i.val < 6 then
  ((3, 0)) else
  ((4, 0))))) else
  (if i.val < 11 then
  (if i.val < 9 then
  (if i.val < 8 then
  ((1, 32)) else
  ((2, 64))) else
  (if i.val < 10 then
  ((1, 48)) else
  ((5, 0)))) else
  (if i.val < 13 then
  (if i.val < 12 then
  ((6, 0)) else
  ((5, 2))) else
  (if i.val < 14 then
  ((7, 0)) else
  ((6, 78)))))) else
  (if i.val < 22 then
  (if i.val < 18 then
  (if i.val < 16 then
  ((7, 2)) else
  (if i.val < 17 then
  ((2, 1)) else
  ((8, 0)))) else
  (if i.val < 20 then
  (if i.val < 19 then
  ((0, 4)) else
  ((2, 65))) else
  (if i.val < 21 then
  ((8, 2)) else
  ((4, 4))))) else
  (if i.val < 26 then
  (if i.val < 24 then
  (if i.val < 23 then
  ((5, 64)) else
  ((7, 66))) else
  (if i.val < 25 then
  ((6, 4)) else
  ((7, 64)))) else
  (if i.val < 28 then
  (if i.val < 27 then
  ((5, 66)) else
  ((6, 66))) else
  (if i.val < 29 then
  ((1, 1)) else
  ((9, 0))))))) else
  (if i.val < 45 then
  (if i.val < 37 then
  (if i.val < 33 then
  (if i.val < 31 then
  ((0, 2)) else
  (if i.val < 32 then
  ((1, 33)) else
  ((9, 4)))) else
  (if i.val < 35 then
  (if i.val < 34 then
  ((4, 2)) else
  ((6, 64))) else
  (if i.val < 36 then
  ((6, 6)) else
  ((1, 17))))) else
  (if i.val < 41 then
  (if i.val < 39 then
  (if i.val < 38 then
  ((9, 16)) else
  ((0, 6))) else
  (if i.val < 40 then
  ((1, 49)) else
  ((9, 20)))) else
  (if i.val < 43 then
  (if i.val < 42 then
  ((4, 6)) else
  ((6, 76))) else
  (if i.val < 44 then
  ((6, 2)) else
  ((10, 0)))))) else
  (if i.val < 52 then
  (if i.val < 48 then
  (if i.val < 46 then
  ((11, 0)) else
  (if i.val < 47 then
  ((12, 0)) else
  ((13, 0)))) else
  (if i.val < 50 then
  (if i.val < 49 then
  ((14, 0)) else
  ((12, 66))) else
  (if i.val < 51 then
  ((11, 66)) else
  ((15, 0))))) else
  (if i.val < 56 then
  (if i.val < 54 then
  (if i.val < 53 then
  ((16, 0)) else
  ((15, 16))) else
  (if i.val < 55 then
  ((16, 16)) else
  ((17, 0)))) else
  (if i.val < 58 then
  (if i.val < 57 then
  ((18, 0)) else
  ((17, 64))) else
  (if i.val < 59 then
  ((19, 0)) else
  ((19, 4)))))))) else
  (if i.val < 90 then
  (if i.val < 75 then
  (if i.val < 67 then
  (if i.val < 63 then
  (if i.val < 61 then
  ((20, 0)) else
  (if i.val < 62 then
  ((17, 32)) else
  ((21, 0)))) else
  (if i.val < 65 then
  (if i.val < 64 then
  ((22, 0)) else
  ((23, 0))) else
  (if i.val < 66 then
  ((23, 2)) else
  ((24, 0))))) else
  (if i.val < 71 then
  (if i.val < 69 then
  (if i.val < 68 then
  ((24, 2)) else
  ((18, 16))) else
  (if i.val < 70 then
  ((17, 96)) else
  ((19, 16)))) else
  (if i.val < 73 then
  (if i.val < 72 then
  ((19, 20)) else
  ((25, 0))) else
  (if i.val < 74 then
  ((26, 0)) else
  ((25, 2)))))) else
  (if i.val < 82 then
  (if i.val < 78 then
  (if i.val < 76 then
  ((20, 1)) else
  (if i.val < 77 then
  ((27, 0)) else
  ((10, 4)))) else
  (if i.val < 80 then
  (if i.val < 79 then
  ((25, 64)) else
  ((25, 66))) else
  (if i.val < 81 then
  ((26, 4)) else
  ((18, 1))))) else
  (if i.val < 86 then
  (if i.val < 84 then
  (if i.val < 83 then
  ((28, 0)) else
  ((10, 2))) else
  (if i.val < 85 then
  ((26, 6)) else
  ((18, 17)))) else
  (if i.val < 88 then
  (if i.val < 87 then
  ((28, 16)) else
  ((10, 6))) else
  (if i.val < 89 then
  ((26, 2)) else
  ((29, 0))))))) else
  (if i.val < 105 then
  (if i.val < 97 then
  (if i.val < 93 then
  (if i.val < 91 then
  ((30, 0)) else
  (if i.val < 92 then
  ((31, 0)) else
  ((14, 4)))) else
  (if i.val < 95 then
  (if i.val < 94 then
  ((30, 66)) else
  ((29, 66))) else
  (if i.val < 96 then
  ((32, 0)) else
  ((16, 2))))) else
  (if i.val < 101 then
  (if i.val < 99 then
  (if i.val < 98 then
  ((32, 16)) else
  ((16, 22))) else
  (if i.val < 100 then
  ((19, 32)) else
  ((19, 36)))) else
  (if i.val < 103 then
  (if i.val < 102 then
  ((24, 64)) else
  ((24, 66))) else
  (if i.val < 104 then
  ((23, 64)) else
  ((23, 66)))))) else
  (if i.val < 112 then
  (if i.val < 108 then
  (if i.val < 106 then
  ((21, 64)) else
  (if i.val < 107 then
  ((22, 64)) else
  ((19, 48)))) else
  (if i.val < 110 then
  (if i.val < 109 then
  ((19, 52)) else
  ((21, 1))) else
  (if i.val < 111 then
  ((33, 0)) else
  ((11, 4))))) else
  (if i.val < 116 then
  (if i.val < 114 then
  (if i.val < 113 then
  ((24, 65)) else
  ((34, 0))) else
  (if i.val < 115 then
  ((29, 4)) else
  ((35, 0)))) else
  (if i.val < 118 then
  (if i.val < 117 then
  ((12, 78)) else
  ((36, 0))) else
  (if i.val < 119 then
  ((29, 78)) else
  ((24, 1))))))))) else
  (if i.val < 180 then
  (if i.val < 150 then
  (if i.val < 135 then
  (if i.val < 127 then
  (if i.val < 123 then
  (if i.val < 121 then
  ((34, 2)) else
  (if i.val < 122 then
  ((21, 65)) else
  ((33, 2)))) else
  (if i.val < 125 then
  (if i.val < 124 then
  ((11, 2)) else
  ((29, 2))) else
  (if i.val < 126 then
  ((29, 6)) else
  ((11, 6))))) else
  (if i.val < 131 then
  (if i.val < 129 then
  (if i.val < 128 then
  ((22, 1)) else
  ((33, 66))) else
  (if i.val < 130 then
  ((12, 4)) else
  ((24, 67)))) else
  (if i.val < 133 then
  (if i.val < 132 then
  ((37, 0)) else
  ((30, 4))) else
  (if i.val < 134 then
  ((35, 66)) else
  ((11, 78)))))) else
  (if i.val < 142 then
  (if i.val < 138 then
  (if i.val < 136 then
  ((36, 4)) else
  (if i.val < 137 then
  ((30, 78)) else
  ((24, 3)))) else
  (if i.val < 140 then
  (if i.val < 139 then
  ((37, 2)) else
  ((22, 65))) else
  (if i.val < 141 then
  ((33, 64)) else
  ((12, 2))))) else
  (if i.val < 146 then
  (if i.val < 144 then
  (if i.val < 143 then
  ((30, 2)) else
  ((12, 6))) else
  (if i.val < 145 then
  ((30, 6)) else
  ((17, 1)))) else
  (if i.val < 148 then
  (if i.val < 147 then
  ((17, 33)) else
  ((38, 0))) else
  (if i.val < 149 then
  ((14, 2)) else
  ((38, 4))))))) else
  (if i.val < 165 then
  (if i.val < 157 then
  (if i.val < 153 then
  (if i.val < 151 then
  ((14, 6)) else
  (if i.val < 152 then
  ((36, 2)) else
  ((36, 6)))) else
  (if i.val < 155 then
  (if i.val < 154 then
  ((16, 4)) else
  ((15, 20))) else
  (if i.val < 156 then
  ((15, 4)) else
  ((16, 20))))) else
  (if i.val < 161 then
  (if i.val < 159 then
  (if i.val < 158 then
  ((17, 65)) else
  ((17, 97))) else
  (if i.val < 160 then
  ((38, 2)) else
  ((13, 2)))) else
  (if i.val < 163 then
  (if i.val < 162 then
  ((38, 6)) else
  ((31, 2))) else
  (if i.val < 164 then
  ((35, 64)) else
  ((35, 2)))))) else
  (if i.val < 172 then
  (if i.val < 168 then
  (if i.val < 166 then
  ((16, 6)) else
  (if i.val < 167 then
  ((16, 18)) else
  ((32, 4)))) else
  (if i.val < 170 then
  (if i.val < 169 then
  ((32, 20)) else
  ((11, 64))) else
  (if i.val < 171 then
  ((29, 64)) else
  ((11, 76))))) else
  (if i.val < 176 then
  (if i.val < 174 then
  (if i.val < 173 then
  ((29, 76)) else
  ((12, 64))) else
  (if i.val < 175 then
  ((30, 64)) else
  ((12, 76)))) else
  (if i.val < 178 then
  (if i.val < 177 then
  ((30, 76)) else
  ((39, 0))) else
  (if i.val < 179 then
  ((40, 0)) else
  ((39, 66)))))))) else
  (if i.val < 210 then
  (if i.val < 195 then
  (if i.val < 187 then
  (if i.val < 183 then
  (if i.val < 181 then
  ((41, 0)) else
  (if i.val < 182 then
  ((41, 16)) else
  ((42, 0)))) else
  (if i.val < 185 then
  (if i.val < 184 then
  ((43, 0)) else
  ((42, 66))) else
  (if i.val < 186 then
  ((44, 0)) else
  ((45, 0))))) else
  (if i.val < 191 then
  (if i.val < 189 then
  (if i.val < 188 then
  ((45, 4)) else
  ((45, 2))) else
  (if i.val < 190 then
  ((46, 0)) else
  ((47, 0)))) else
  (if i.val < 193 then
  (if i.val < 192 then
  ((48, 0)) else
  ((49, 0))) else
  (if i.val < 194 then
  ((50, 0)) else
  ((49, 64)))))) else
  (if i.val < 202 then
  (if i.val < 198 then
  (if i.val < 196 then
  ((51, 0)) else
  (if i.val < 197 then
  ((51, 2)) else
  ((52, 0)))) else
  (if i.val < 200 then
  (if i.val < 199 then
  ((52, 2)) else
  ((48, 16))) else
  (if i.val < 201 then
  ((49, 1)) else
  ((53, 0))))) else
  (if i.val < 206 then
  (if i.val < 204 then
  (if i.val < 203 then
  ((39, 4)) else
  ((54, 0))) else
  (if i.val < 205 then
  ((39, 78)) else
  ((49, 65)))) else
  (if i.val < 208 then
  (if i.val < 207 then
  ((53, 2)) else
  ((39, 2))) else
  (if i.val < 209 then
  ((39, 6)) else
  ((47, 1))))))) else
  (if i.val < 225 then
  (if i.val < 217 then
  (if i.val < 213 then
  (if i.val < 211 then
  ((55, 0)) else
  (if i.val < 212 then
  ((40, 2)) else
  ((54, 2)))) else
  (if i.val < 215 then
  (if i.val < 214 then
  ((41, 4)) else
  ((41, 20))) else
  (if i.val < 216 then
  ((39, 64)) else
  ((39, 76))))) else
  (if i.val < 221 then
  (if i.val < 219 then
  (if i.val < 218 then
  ((56, 0)) else
  ((43, 4))) else
  (if i.val < 220 then
  ((56, 66)) else
  ((44, 4)))) else
  (if i.val < 223 then
  (if i.val < 222 then
  ((46, 6)) else
  ((46, 2))) else
  (if i.val < 224 then
  ((46, 4)) else
  ((45, 6)))))) else
  (if i.val < 233 then
  (if i.val < 229 then
  (if i.val < 227 then
  (if i.val < 226 then
  ((51, 64)) else
  ((52, 66))) else
  (if i.val < 228 then
  ((52, 64)) else
  ((51, 66)))) else
  (if i.val < 231 then
  (if i.val < 230 then
  ((43, 2)) else
  ((43, 6))) else
  (if i.val < 232 then
  ((42, 2)) else
  ((56, 2))))) else
  (if i.val < 237 then
  (if i.val < 235 then
  (if i.val < 234 then
  ((44, 2)) else
  ((44, 6))) else
  (if i.val < 236 then
  ((42, 64)) else
  ((56, 64)))) else
  (if i.val < 239 then
  (if i.val < 238 then
  ((57, 0)) else
  ((58, 0))) else
  (if i.val < 240 then
  ((59, 0)) else
  ((57, 2)))))))))

/-- Includes zero as well as all nonidentity involutions. -/
def involutions : Finset Code := {0, 1, 2, 4, 6, 8, 9, 10, 12, 14, 16, 17, 20, 24, 25, 28, 32, 36, 37, 40, 44, 45, 48, 52, 53, 56, 60, 61, 64, 66, 67, 72, 74, 75, 83, 91, 96, 102, 103, 104, 110, 111, 119, 127}
end FiniteChecks

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
