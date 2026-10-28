module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.Words

/-!
# Explicit conjugating words for the two local eleven-elements

These straight-line words connect the local elements defined by the ATLAS
program J4G1-max7W1 to the prescribed 66A and 22B source words. The original
program and matrix representation are attributed in `Elevens.Words` and
`Model.Data` (R. A. Wilson, S. J. Nickerson and J. N. Bray).

The witnesses were found by aligning commuting involutions using odd dihedral
products, then meeting two orbits of cyclic projectors inside the resulting
involution centralizer. The central branch uses the intermediate centralizer
generators from J4G1-max7W1. The noncentral branch uses explicit Bray words.
The resulting exponents are 7 and 1. No centralizer order, class label, search
algorithm, or conjugacy table is assumed by the proof: `Matrices` checks the
final identities directly in the binary representation.

`WitnessGraph.json` records the shared straight-line program and `Generate.py`
regenerates the definitions and arithmetic witnesses.
-/

@[expose] public section
namespace Janko4.Simplicity.Elevens.BridgeCertificate

variable {G : Type*} [Group G]

def w000 (a _b : G) : G := a
def w001 (_a b : G) : G := b
def w002 (a b : G) : G := w000 a b * w001 a b
def w003 (a b : G) : G := w002 a b * w001 a b
def w004 (a b : G) : G := w002 a b * w003 a b
def w005 (a b : G) : G := w002 a b * w004 a b
def w006 (a b : G) : G := w005 a b * w003 a b
def w007 (a b : G) : G := w006 a b ^ 8
def w008 (a b : G) : G := (w007 a b)⁻¹
def w009 (a b : G) : G := w003 a b ^ 4
def w010 (a b : G) : G := w008 a b * w009 a b
def w011 (a b : G) : G := w010 a b * w007 a b
def w012 (a b : G) : G := w000 a b * w011 a b
def w013 (a b : G) : G := w012 a b ^ 6
def w014 (a b : G) : G := w012 a b * w011 a b
def w015 (a b : G) : G := w014 a b ^ 3
def w016 (a b : G) : G := w012 a b * w012 a b
def w017 (a b : G) : G := w015 a b * w016 a b
def w018 (a b : G) : G := w013 a b * w017 a b
def w019 (a b : G) : G := w018 a b ^ 8
def w020 (a b : G) : G := w018 a b ^ 20
def w021 (a b : G) : G := w001 a b * w020 a b
def w022 (a b : G) : G := (w021 a b)⁻¹
def w023 (a b : G) : G := w020 a b * w001 a b
def w024 (a b : G) : G := w022 a b * w023 a b
def w025 (a b : G) : G := w024 a b ^ 3
def w026 (a b : G) : G := (w018 a b)⁻¹
def w027 (a b : G) : G := w026 a b * w025 a b
def w028 (a b : G) : G := w025 a b * w027 a b
def w029 (a b : G) : G := w019 a b * w028 a b
def w030 (a b : G) : G := (w029 a b)⁻¹
def w031 (a b : G) : G := w018 a b * w025 a b
def w032 (a b : G) : G := w018 a b * w031 a b
def w033 (a b : G) : G := w032 a b ^ 7
def w034 (a b : G) : G := w030 a b * w033 a b
def w035 (a b : G) : G := w034 a b * w029 a b
def w036 (a b : G) : G := w000 a b * w018 a b
def w037 (a b : G) : G := w036 a b ^ 15
def w038 (a b : G) : G := w035 a b * w037 a b
def w039 (a b : G) : G := w038 a b ^ 2
def w040 (a b : G) : G := (w039 a b)⁻¹
def w041 (a b : G) : G := (w036 a b)⁻¹
def w042 (a b : G) : G := w041 a b * w039 a b
def w043 (a b : G) : G := w042 a b * w036 a b
def w044 (a b : G) : G := (w043 a b)⁻¹
def w045 (a b : G) : G := w040 a b * w044 a b
def w046 (a b : G) : G := w045 a b * w039 a b
def w047 (a b : G) : G := w046 a b * w043 a b
def w048 (a b : G) : G := w003 a b * w000 a b
def w049 (a b : G) : G := w048 a b * w001 a b
def w050 (a b : G) : G := w049 a b * w000 a b
def w051 (a b : G) : G := w050 a b * w001 a b
def w052 (a b : G) : G := w051 a b * w000 a b
def w053 (a b : G) : G := w052 a b * w001 a b
def w054 (a b : G) : G := w053 a b * w001 a b
def w055 (a b : G) : G := w054 a b ^ 6
def w056 (a b : G) : G := w054 a b ^ 33
def w057 (a b : G) : G := w001 a b * w000 a b
def w058 (a b : G) : G := w057 a b * w000 a b
def w059 (a b : G) : G := w058 a b * w000 a b
def w060 (a b : G) : G := w059 a b * w000 a b
def w061 (a b : G) : G := w060 a b * w000 a b
def w062 (a b : G) : G := w061 a b * w001 a b
def w063 (a b : G) : G := w062 a b * w001 a b
def w064 (a b : G) : G := w063 a b * w000 a b
def w065 (a b : G) : G := w064 a b * w001 a b
def w066 (a b : G) : G := w065 a b * w000 a b
def w067 (a b : G) : G := w066 a b * w000 a b
def w068 (a b : G) : G := w067 a b * w001 a b
def w069 (a b : G) : G := w068 a b * w001 a b
def w070 (a b : G) : G := w069 a b * w001 a b
def w071 (a b : G) : G := (w070 a b)⁻¹
def w072 (a b : G) : G := w071 a b * w020 a b
def w073 (a b : G) : G := w072 a b * w070 a b
def w074 (a b : G) : G := w056 a b * w073 a b
def w075 (a b : G) : G := w074 a b ^ 6
def w076 (a b : G) : G := w075 a b * w071 a b
def w077 (_a _b : G) : G := 1
def w078 (a b : G) : G := w077 a b * w018 a b
def w079 (a b : G) : G := w078 a b * w018 a b
def w080 (a b : G) : G := w079 a b * w018 a b
def w081 (a b : G) : G := w080 a b * w018 a b
def w082 (a b : G) : G := w081 a b * w025 a b
def w083 (a b : G) : G := w082 a b * w018 a b
def w084 (a b : G) : G := w083 a b * w025 a b
def w085 (a b : G) : G := w084 a b * w026 a b
def w086 (a b : G) : G := w085 a b * w026 a b
def w087 (a b : G) : G := w086 a b * w026 a b
def w088 (a b : G) : G := w087 a b * w025 a b
def w089 (a b : G) : G := w076 a b * w088 a b
def w090 (a b : G) : G := w077 a b * w025 a b
def w091 (a b : G) : G := w090 a b * w018 a b
def w092 (a b : G) : G := w091 a b * w025 a b
def w093 (a b : G) : G := w092 a b * w018 a b
def w094 (a b : G) : G := w093 a b * w018 a b
def w095 (a b : G) : G := w094 a b * w025 a b
def w096 (a b : G) : G := w095 a b * w026 a b
def w097 (a b : G) : G := w096 a b * w025 a b
def w098 (a b : G) : G := w097 a b * w026 a b
def w099 (a b : G) : G := w098 a b * w026 a b
def w100 (a b : G) : G := w099 a b * w026 a b
def w101 (a b : G) : G := w100 a b * w026 a b
def w102 (a b : G) : G := w101 a b * w026 a b
def w103 (a b : G) : G := (w102 a b)⁻¹
def w104 (a b : G) : G := w089 a b * w103 a b
def w105 (a b : G) : G := w047 a b ^ 7
def w106 (a b : G) : G := w104 a b * w105 a b
def w107 (a b : G) : G := (w104 a b)⁻¹
def w108 (a b : G) : G := w106 a b * w107 a b
def w109 (a b : G) : G := w054 a b * w000 a b
def w110 (a b : G) : G := w109 a b * w001 a b
def w111 (a b : G) : G := w110 a b * w000 a b
def w112 (a b : G) : G := w111 a b * w001 a b
def w113 (a b : G) : G := w112 a b * w000 a b
def w114 (a b : G) : G := w113 a b * w001 a b
def w115 (a b : G) : G := w114 a b * w001 a b
def w116 (a b : G) : G := w115 a b * w000 a b
def w117 (a b : G) : G := w116 a b * w001 a b
def w118 (a b : G) : G := w117 a b * w001 a b
def w119 (a b : G) : G := w118 a b * w000 a b
def w120 (a b : G) : G := w119 a b * w001 a b
def w121 (a b : G) : G := w120 a b * w000 a b
def w122 (a b : G) : G := w121 a b * w001 a b
def w123 (a b : G) : G := w122 a b * w000 a b
def w124 (a b : G) : G := w123 a b * w001 a b
def w125 (a b : G) : G := w124 a b * w001 a b
def w126 (a b : G) : G := w125 a b ^ 2
def w127 (a b : G) : G := w125 a b ^ 11
def w128 (a b : G) : G := w000 a b * w000 a b
def w129 (a b : G) : G := w128 a b * w001 a b
def w130 (a b : G) : G := w129 a b * w000 a b
def w131 (a b : G) : G := w130 a b * w001 a b
def w132 (a b : G) : G := w131 a b * w001 a b
def w133 (a b : G) : G := w132 a b * w000 a b
def w134 (a b : G) : G := w133 a b * w001 a b
def w135 (a b : G) : G := w134 a b * w001 a b
def w136 (a b : G) : G := w135 a b * w001 a b
def w137 (a b : G) : G := w136 a b * w000 a b
def w138 (a b : G) : G := w137 a b * w001 a b
def w139 (a b : G) : G := w138 a b * w000 a b
def w140 (a b : G) : G := w139 a b * w001 a b
def w141 (a b : G) : G := w140 a b * w001 a b
def w142 (a b : G) : G := (w141 a b)⁻¹
def w143 (a b : G) : G := w077 a b * w035 a b
def w144 (a b : G) : G := w143 a b * w035 a b
def w145 (a b : G) : G := w144 a b * w036 a b
def w146 (a b : G) : G := w145 a b * w035 a b
def w147 (a b : G) : G := w146 a b * w036 a b
def w148 (a b : G) : G := w036 a b * w035 a b
def w149 (a b : G) : G := w148 a b * w036 a b
def w150 (a b : G) : G := w149 a b * w036 a b
def w151 (a b : G) : G := w150 a b ^ 5
def w152 (a b : G) : G := w147 a b * w151 a b
def w153 (a b : G) : G := (w147 a b)⁻¹
def w154 (a b : G) : G := w152 a b * w153 a b
def w155 (a b : G) : G := w142 a b * w154 a b
def w156 (a b : G) : G := w155 a b * w141 a b
def w157 (a b : G) : G := w127 a b * w156 a b
def w158 (a b : G) : G := w157 a b ^ 19
def w159 (a b : G) : G := w158 a b * w142 a b
def w160 (a b : G) : G := w002 a b * w000 a b
def w161 (a b : G) : G := w160 a b * w000 a b
def w162 (a b : G) : G := w161 a b * w000 a b
def w163 (a b : G) : G := w162 a b * w001 a b
def w164 (a b : G) : G := w163 a b * w000 a b
def w165 (a b : G) : G := w164 a b * w000 a b
def w166 (a b : G) : G := w165 a b * w001 a b
def w167 (a b : G) : G := w166 a b * w000 a b
def w168 (a b : G) : G := w167 a b * w001 a b
def w169 (a b : G) : G := w168 a b * w001 a b
def w170 (a b : G) : G := w169 a b * w000 a b
def w171 (a b : G) : G := w170 a b * w000 a b
def w172 (a b : G) : G := w171 a b * w000 a b
def w173 (a b : G) : G := w172 a b * w001 a b
def w174 (a b : G) : G := w173 a b * w000 a b
def w175 (a b : G) : G := w174 a b * w000 a b
def w176 (a b : G) : G := w175 a b * w001 a b
def w177 (a b : G) : G := w176 a b * w001 a b
def w178 (a b : G) : G := w177 a b * w000 a b
def w179 (a b : G) : G := w178 a b * w000 a b
def w180 (a b : G) : G := (w179 a b)⁻¹
def w181 (a b : G) : G := w180 a b * w154 a b
def w182 (a b : G) : G := w181 a b * w179 a b
def w183 (a b : G) : G := w154 a b * w182 a b
def w184 (a b : G) : G := w183 a b ^ 12
def w185 (a b : G) : G := w184 a b * w180 a b
def w186 (a b : G) : G := w077 a b * w185 a b
def w187 (a b : G) : G := w186 a b * w185 a b
def w188 (a b : G) : G := w187 a b * w185 a b
def w189 (a b : G) : G := w057 a b * w001 a b
def w190 (a b : G) : G := w189 a b * w001 a b
def w191 (a b : G) : G := w190 a b * w001 a b
def w192 (a b : G) : G := w191 a b * w001 a b
def w193 (a b : G) : G := w192 a b * w000 a b
def w194 (a b : G) : G := w193 a b * w000 a b
def w195 (a b : G) : G := w194 a b * w001 a b
def w196 (a b : G) : G := w195 a b * w000 a b
def w197 (a b : G) : G := w196 a b * w001 a b
def w198 (a b : G) : G := w197 a b * w001 a b
def w199 (a b : G) : G := w198 a b * w000 a b
def w200 (a b : G) : G := w199 a b * w001 a b
def w201 (a b : G) : G := w200 a b * w001 a b
def w202 (a b : G) : G := w201 a b * w000 a b
def w203 (a b : G) : G := w202 a b * w000 a b
def w204 (a b : G) : G := w203 a b * w000 a b
def w205 (a b : G) : G := w204 a b * w000 a b
def w206 (a b : G) : G := w205 a b * w001 a b
def w207 (a b : G) : G := w206 a b * w000 a b
def w208 (a b : G) : G := w207 a b * w000 a b
def w209 (a b : G) : G := (w208 a b)⁻¹
def w210 (a b : G) : G := w209 a b * w154 a b
def w211 (a b : G) : G := w210 a b * w208 a b
def w212 (a b : G) : G := w154 a b * w211 a b
def w213 (a b : G) : G := w212 a b ^ 20
def w214 (a b : G) : G := w188 a b * w213 a b
def w215 (a b : G) : G := w128 a b * w000 a b
def w216 (a b : G) : G := w215 a b * w001 a b
def w217 (a b : G) : G := w216 a b * w000 a b
def w218 (a b : G) : G := w217 a b * w000 a b
def w219 (a b : G) : G := w218 a b * w001 a b
def w220 (a b : G) : G := w219 a b * w001 a b
def w221 (a b : G) : G := w220 a b * w000 a b
def w222 (a b : G) : G := w221 a b * w000 a b
def w223 (a b : G) : G := w222 a b * w001 a b
def w224 (a b : G) : G := w223 a b * w001 a b
def w225 (a b : G) : G := w224 a b * w001 a b
def w226 (a b : G) : G := w225 a b * w001 a b
def w227 (a b : G) : G := w226 a b * w001 a b
def w228 (a b : G) : G := w227 a b * w000 a b
def w229 (a b : G) : G := w228 a b * w001 a b
def w230 (a b : G) : G := w229 a b * w001 a b
def w231 (a b : G) : G := w230 a b * w001 a b
def w232 (a b : G) : G := w231 a b * w000 a b
def w233 (a b : G) : G := w232 a b * w001 a b
def w234 (a b : G) : G := w233 a b * w000 a b
def w235 (a b : G) : G := (w234 a b)⁻¹
def w236 (a b : G) : G := w235 a b * w154 a b
def w237 (a b : G) : G := w236 a b * w234 a b
def w238 (a b : G) : G := w154 a b * w237 a b
def w239 (a b : G) : G := w238 a b ^ 16
def w240 (a b : G) : G := w239 a b * w235 a b
def w241 (a b : G) : G := w214 a b * w240 a b
def w242 (a b : G) : G := w241 a b * w185 a b
def w243 (a b : G) : G := w159 a b * w242 a b
def w244 (a b : G) : G := w001 a b * w001 a b
def w245 (a b : G) : G := w244 a b * w001 a b
def w246 (a b : G) : G := w245 a b * w000 a b
def w247 (a b : G) : G := w246 a b * w001 a b
def w248 (a b : G) : G := w247 a b * w001 a b
def w249 (a b : G) : G := w248 a b * w001 a b
def w250 (a b : G) : G := w249 a b * w001 a b
def w251 (a b : G) : G := w250 a b * w001 a b
def w252 (a b : G) : G := w251 a b * w001 a b
def w253 (a b : G) : G := w252 a b * w000 a b
def w254 (a b : G) : G := w253 a b * w000 a b
def w255 (a b : G) : G := w254 a b * w000 a b
def w256 (a b : G) : G := w255 a b * w000 a b
def w257 (a b : G) : G := w256 a b * w001 a b
def w258 (a b : G) : G := w257 a b * w001 a b
def w259 (a b : G) : G := w258 a b * w001 a b
def w260 (a b : G) : G := w259 a b * w000 a b
def w261 (a b : G) : G := w260 a b * w001 a b
def w262 (a b : G) : G := w261 a b * w000 a b
def w263 (a b : G) : G := w262 a b * w000 a b
def w264 (a b : G) : G := w263 a b * w001 a b
def w265 (a b : G) : G := (w264 a b)⁻¹
def w266 (a b : G) : G := w265 a b * w154 a b
def w267 (a b : G) : G := w266 a b * w264 a b
def w268 (a b : G) : G := w154 a b * w267 a b
def w269 (a b : G) : G := w268 a b ^ 20
def w270 (a b : G) : G := w188 a b * w269 a b
def w271 (a b : G) : G := w270 a b * w185 a b
def w272 (a b : G) : G := w129 a b * w001 a b
def w273 (a b : G) : G := w272 a b * w000 a b
def w274 (a b : G) : G := w273 a b * w001 a b
def w275 (a b : G) : G := w274 a b * w000 a b
def w276 (a b : G) : G := w275 a b * w001 a b
def w277 (a b : G) : G := w276 a b * w001 a b
def w278 (a b : G) : G := w277 a b * w001 a b
def w279 (a b : G) : G := w278 a b * w001 a b
def w280 (a b : G) : G := w279 a b * w000 a b
def w281 (a b : G) : G := w280 a b * w001 a b
def w282 (a b : G) : G := w281 a b * w001 a b
def w283 (a b : G) : G := w282 a b * w001 a b
def w284 (a b : G) : G := w283 a b * w001 a b
def w285 (a b : G) : G := w284 a b * w001 a b
def w286 (a b : G) : G := w285 a b * w001 a b
def w287 (a b : G) : G := w286 a b * w000 a b
def w288 (a b : G) : G := w287 a b * w001 a b
def w289 (a b : G) : G := w288 a b * w001 a b
def w290 (a b : G) : G := w289 a b * w000 a b
def w291 (a b : G) : G := (w290 a b)⁻¹
def w292 (a b : G) : G := w291 a b * w154 a b
def w293 (a b : G) : G := w292 a b * w290 a b
def w294 (a b : G) : G := w154 a b * w293 a b
def w295 (a b : G) : G := w294 a b ^ 12
def w296 (a b : G) : G := w271 a b * w295 a b
def w297 (a b : G) : G := (w296 a b)⁻¹
def w298 (a b : G) : G := w243 a b * w297 a b
def w299 (a b : G) : G := w298 a b * w039 a b
def w300 (a b : G) : G := (w298 a b)⁻¹
def w301 (a b : G) : G := w299 a b * w300 a b

theorem localZ_eq (a b : G) : w047 a b = localZ a b := rfl
theorem localX_eq (a b : G) : w039 a b = localX a b := rfl

theorem target5_eq (a b : G) : w055 a b = primeRepresentative a b 5 := by
  simp [primeRepresentative, word, w000, w001, w002, w003, w048, w049, w050, w051, w052, w053, w054, w055, mul_assoc]

theorem target6_eq (a b : G) : w126 a b = primeRepresentative a b 6 := by
  simp [primeRepresentative, word, w000, w001, w002, w003, w048, w049, w050, w051, w052, w053, w054, w109, w110, w111, w112, w113, w114, w115, w116, w117, w118, w119, w120, w121, w122, w123, w124, w125, w126, mul_assoc]

end Janko4.Simplicity.Elevens.BridgeCertificate
