module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22

/-!
# Fi22 word witnesses for eight proposed centralizer images

Every word below belongs to the exact Fi22 carrier by construction. The
straight-line nodes are shared; their full word expansions are not needed.
The eight action comparisons with the fixed Fi23 permutations remain separate
certificate obligations, not consequences of membership of these words.

`source/image-words.g` and `source/prepare_words.py` reproduce these definitions
from the saved permutation images. GAP verifies the witnesses only as a
discovery aid. The Lean definitions depend on no asserted external equality.
The right-action GAP word has the same multiplication order after inverting
each source permutation to obtain the project's left-action convention.

Source application: GLS3 Table 5.3u; attribution and original numerical
sources are in `AtlasCarriers/source/README.md`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.ImageWords

def word1 : Fi22.Carrier :=
  ⟨Fi22.generatorA, Subgroup.subset_closure (by simp)⟩

def word2 : Fi22.Carrier :=
  ⟨Fi22.generatorB, Subgroup.subset_closure (by simp)⟩

def word3 : Fi22.Carrier := 1

def word4 : Fi22.Carrier := word2 * word2

def word5 : Fi22.Carrier := word4 * word1

def word6 : Fi22.Carrier := word5 * word2

def word7 : Fi22.Carrier := word6 * word1

def word8 : Fi22.Carrier := word7 * word2

def word9 : Fi22.Carrier := word8 * word2

def word10 : Fi22.Carrier := word9 * word2

def word11 : Fi22.Carrier := word10 * word1

def word12 : Fi22.Carrier := word11 * word2

def word13 : Fi22.Carrier := word12 * word1

def word14 : Fi22.Carrier := word13 * word2

def word15 : Fi22.Carrier := word14 * word2

def word16 : Fi22.Carrier := word15 * word2

def word17 : Fi22.Carrier := word16 * word1

def word18 : Fi22.Carrier := word17 * word2

def word19 : Fi22.Carrier := word18 * word2

def word20 : Fi22.Carrier := word19 * word2

def word21 : Fi22.Carrier := word20 * word1

def word22 : Fi22.Carrier := word21 * word2

def word23 : Fi22.Carrier := word22 * word2

def word24 : Fi22.Carrier := word23 * word1

def word25 : Fi22.Carrier := word24 * word2

def word26 : Fi22.Carrier := word25 * word1

def word27 : Fi22.Carrier := word1 * word26

def word28 : Fi22.Carrier := word27⁻¹

def word29 : Fi22.Carrier := word28 * word2

def word30 : Fi22.Carrier := word29 * word2

def word31 : Fi22.Carrier := word30 * word1

def word32 : Fi22.Carrier := word31 * word2

def word33 : Fi22.Carrier := word32 * word1

def word34 : Fi22.Carrier := word33 * word2

def word35 : Fi22.Carrier := word34 * word2

def word36 : Fi22.Carrier := word35 * word2

def word37 : Fi22.Carrier := word36 * word1

def word38 : Fi22.Carrier := word37 * word2

def word39 : Fi22.Carrier := word38 * word1

def word40 : Fi22.Carrier := word39 * word2

def word41 : Fi22.Carrier := word40 * word2

def word42 : Fi22.Carrier := word41 * word2

def word43 : Fi22.Carrier := word42 * word1

def word44 : Fi22.Carrier := word43 * word2

def word45 : Fi22.Carrier := word44 * word2

def word46 : Fi22.Carrier := word45 * word2

def word47 : Fi22.Carrier := word46 * word1

def word48 : Fi22.Carrier := word47 * word2

def word49 : Fi22.Carrier := word48 * word2

def word50 : Fi22.Carrier := word49 * word1

def word51 : Fi22.Carrier := word50 * word2

def word52 : Fi22.Carrier := word51 * word1

def word53 : Fi22.Carrier := word2 * word26

def word54 : Fi22.Carrier := word53⁻¹

def word55 : Fi22.Carrier := word54 * word1

def word56 : Fi22.Carrier := word55 * word2

def word57 : Fi22.Carrier := word56 * word1

def word58 : Fi22.Carrier := word57 * word2

def word59 : Fi22.Carrier := word58 * word1

def word60 : Fi22.Carrier := word59 * word2

def word61 : Fi22.Carrier := word60 * word1

def word62 : Fi22.Carrier := word61 * word2

def word63 : Fi22.Carrier := word62 * word2

def word64 : Fi22.Carrier := word63 * word2

def word65 : Fi22.Carrier := word64 * word2

def word66 : Fi22.Carrier := word65 * word2

def word67 : Fi22.Carrier := word66 * word2

def word68 : Fi22.Carrier := word67 * word1

def word69 : Fi22.Carrier := word68 * word2

def word70 : Fi22.Carrier := word69 * word2

def word71 : Fi22.Carrier := word70 * word2

def word72 : Fi22.Carrier := word71 * word2

def word73 : Fi22.Carrier := word72 * word2

def word74 : Fi22.Carrier := word73 * word1

def word75 : Fi22.Carrier := word74 * word2

def word76 : Fi22.Carrier := word75 * word75

def word77 : Fi22.Carrier := word76 * word52

def word78 : Fi22.Carrier := word77 * word75

def word79 : Fi22.Carrier := word78 * word75

def word80 : Fi22.Carrier := word79 * word75

def word81 : Fi22.Carrier := word80 * word75

def word82 : Fi22.Carrier := word81 * word75

def word83 : Fi22.Carrier := word82 * word75

def word84 : Fi22.Carrier := word83 * word75

def word85 : Fi22.Carrier := word84 * word75

def word86 : Fi22.Carrier := word85 * word52

def word87 : Fi22.Carrier := word86 * word75

def word88 : Fi22.Carrier := word87 * word52

def word89 : Fi22.Carrier := word88 * word75

def word90 : Fi22.Carrier := word89 * word75

def word91 : Fi22.Carrier := word90 * word52

def word92 : Fi22.Carrier := word91 * word75

def word93 : Fi22.Carrier := word52 * word92

def word94 : Fi22.Carrier := word93⁻¹

def word95 : Fi22.Carrier := word94 * word75

def word96 : Fi22.Carrier := word95 * word75

def word97 : Fi22.Carrier := word96 * word52

def word98 : Fi22.Carrier := word97 * word75

def word99 : Fi22.Carrier := word98 * word75

def word100 : Fi22.Carrier := word99 * word75

def word101 : Fi22.Carrier := word100 * word75

def word102 : Fi22.Carrier := word101 * word75

def word103 : Fi22.Carrier := word102 * word75

def word104 : Fi22.Carrier := word103 * word75

def word105 : Fi22.Carrier := word104 * word75

def word106 : Fi22.Carrier := word105 * word52

def word107 : Fi22.Carrier := word106 * word75

def word108 : Fi22.Carrier := word107 * word52

def word109 : Fi22.Carrier := word108 * word75

def word110 : Fi22.Carrier := word109 * word75

def word111 : Fi22.Carrier := word110 * word52

def word112 : Fi22.Carrier := word111 * word75

def word113 : Fi22.Carrier := word75 * word92

def word114 : Fi22.Carrier := word113⁻¹

def word115 : Fi22.Carrier := word114 * word52

def word116 : Fi22.Carrier := word115 * word75

def word117 : Fi22.Carrier := word116 * word52

def word118 : Fi22.Carrier := word117 * word75

def word119 : Fi22.Carrier := word118 * word75

def word120 : Fi22.Carrier := word119 * word52

def word121 : Fi22.Carrier := word120 * word75

def word122 : Fi22.Carrier := word121 * word75

def word123 : Fi22.Carrier := word122 * word75

def word124 : Fi22.Carrier := word123 * word75

def word125 : Fi22.Carrier := word75 * word52

def word126 : Fi22.Carrier := word125 * word75

def word127 : Fi22.Carrier := word126 * word75

def word128 : Fi22.Carrier := word127 * word75

def word129 : Fi22.Carrier := word128 * word75

def word130 : Fi22.Carrier := word129 * word75

def word131 : Fi22.Carrier := word130 * word75

def word132 : Fi22.Carrier := word131 * word75

def word133 : Fi22.Carrier := word132 * word75

def word134 : Fi22.Carrier := word133 * word52

def word135 : Fi22.Carrier := word134 * word75

def word136 : Fi22.Carrier := word135 * word52

def word137 : Fi22.Carrier := word136 * word75

def word138 : Fi22.Carrier := word137 * word75

def word139 : Fi22.Carrier := word138 * word52

def word140 : Fi22.Carrier := word139 * word75

def word141 : Fi22.Carrier := word52 * word140

def word142 : Fi22.Carrier := word141⁻¹

def word143 : Fi22.Carrier := word142 * word75

def word144 : Fi22.Carrier := word143 * word52

def word145 : Fi22.Carrier := word144 * word75

def word146 : Fi22.Carrier := word145 * word75

def word147 : Fi22.Carrier := word146 * word75

def word148 : Fi22.Carrier := word147 * word75

def word149 : Fi22.Carrier := word148 * word75

def word150 : Fi22.Carrier := word149 * word75

def word151 : Fi22.Carrier := word150 * word75

def word152 : Fi22.Carrier := word151 * word75

def word153 : Fi22.Carrier := word152 * word52

def word154 : Fi22.Carrier := word153 * word75

def word155 : Fi22.Carrier := word154 * word52

def word156 : Fi22.Carrier := word155 * word75

def word157 : Fi22.Carrier := word156 * word75

def word158 : Fi22.Carrier := word157 * word52

def word159 : Fi22.Carrier := word158 * word75

def word160 : Fi22.Carrier := word124 * word124

def word161 : Fi22.Carrier := word160 * word159

def word162 : Fi22.Carrier := word161 * word124

def word163 : Fi22.Carrier := word162 * word159

def word164 : Fi22.Carrier := word163 * word124

def word165 : Fi22.Carrier := word164 * word124

def word166 : Fi22.Carrier := word165 * word124

def word167 : Fi22.Carrier := word166 * word124

def word168 : Fi22.Carrier := word167 * word124

def word169 : Fi22.Carrier := word168 * word124

def word170 : Fi22.Carrier := word169 * word124

def word171 : Fi22.Carrier := word170 * word124

def word172 : Fi22.Carrier := word112 * word171

def word173 : Fi22.Carrier := word172⁻¹

def word174 : Fi22.Carrier := word173 * word124

def word175 : Fi22.Carrier := word174 * word124

def word176 : Fi22.Carrier := word175 * word159

def word177 : Fi22.Carrier := word176 * word124

def word178 : Fi22.Carrier := word177 * word159

def word179 : Fi22.Carrier := word178 * word124

def word180 : Fi22.Carrier := word179 * word124

def word181 : Fi22.Carrier := word180 * word124

def word182 : Fi22.Carrier := word181 * word124

def word183 : Fi22.Carrier := word182 * word124

def word184 : Fi22.Carrier := word183 * word124

def word185 : Fi22.Carrier := word184 * word124

def word186 : Fi22.Carrier := word185 * word124

def word187 : Fi22.Carrier := word124 * word171

def word188 : Fi22.Carrier := word187⁻¹

def word189 : Fi22.Carrier := word188 * word112

def word190 : Fi22.Carrier := word189 * word124

def word191 : Fi22.Carrier := word190 * word112

def word192 : Fi22.Carrier := word191 * word159

def word193 : Fi22.Carrier := word192 * word124

def word194 : Fi22.Carrier := word193 * word112

def word195 : Fi22.Carrier := word194 * word124

def word196 : Fi22.Carrier := word195 * word112

def word197 : Fi22.Carrier := word196 * word124

def word198 : Fi22.Carrier := word112 * word197

def word199 : Fi22.Carrier := word159 * word198

def word200 : Fi22.Carrier := word199⁻¹

def word201 : Fi22.Carrier := word200 * word112

def word202 : Fi22.Carrier := word201 * word197

def word203 : Fi22.Carrier := word76 * word75

def word204 : Fi22.Carrier := word203 * word75

def word205 : Fi22.Carrier := word204 * word75

def word206 : Fi22.Carrier := word205 * word75

def word207 : Fi22.Carrier := word206 * word75

def word208 : Fi22.Carrier := word207 * word75

def word209 : Fi22.Carrier := word208 * word75

def word210 : Fi22.Carrier := word209 * word52

def word211 : Fi22.Carrier := word210 * word75

def word212 : Fi22.Carrier := word211 * word52

def word213 : Fi22.Carrier := word212 * word75

def word214 : Fi22.Carrier := word213 * word75

def word215 : Fi22.Carrier := word214 * word52

def word216 : Fi22.Carrier := word215 * word75

def word217 : Fi22.Carrier := word52 * word216

def word218 : Fi22.Carrier := word217⁻¹

def word219 : Fi22.Carrier := word218 * word75

def word220 : Fi22.Carrier := word219 * word75

def word221 : Fi22.Carrier := word220 * word52

def word222 : Fi22.Carrier := word221 * word75

def word223 : Fi22.Carrier := word222 * word75

def word224 : Fi22.Carrier := word223 * word52

def word225 : Fi22.Carrier := word224 * word75

def word226 : Fi22.Carrier := word225 * word75

def word227 : Fi22.Carrier := word226 * word52

def word228 : Fi22.Carrier := word227 * word75

def word229 : Fi22.Carrier := word228 * word75

def word230 : Fi22.Carrier := word229 * word52

def word231 : Fi22.Carrier := word230 * word75

def word232 : Fi22.Carrier := word231 * word75

def word233 : Fi22.Carrier := word232 * word75

def word234 : Fi22.Carrier := word233 * word52

def word235 : Fi22.Carrier := word234 * word159

def word236 : Fi22.Carrier := word235 * word124

def word237 : Fi22.Carrier := word236 * word124

def word238 : Fi22.Carrier := word237 * word124

def word239 : Fi22.Carrier := word238 * word112

def word240 : Fi22.Carrier := word239 * word124

def word241 : Fi22.Carrier := word240 * word186

def word242 : Fi22.Carrier := word241 * word112

def word243 : Fi22.Carrier := word2 * word1

def word244 : Fi22.Carrier := word243 * word2

def word245 : Fi22.Carrier := word244 * word1

def word246 : Fi22.Carrier := word245 * word2

def word247 : Fi22.Carrier := word246 * word2

def word248 : Fi22.Carrier := word247 * word2

def word249 : Fi22.Carrier := word248 * word1

def word250 : Fi22.Carrier := word249 * word2

def word251 : Fi22.Carrier := word250 * word1

def word252 : Fi22.Carrier := word251 * word2

def word253 : Fi22.Carrier := word252 * word2

def word254 : Fi22.Carrier := word253 * word2

def word255 : Fi22.Carrier := word254 * word1

def word256 : Fi22.Carrier := word255 * word2

def word257 : Fi22.Carrier := word256 * word2

def word258 : Fi22.Carrier := word257 * word2

def word259 : Fi22.Carrier := word258 * word1

def word260 : Fi22.Carrier := word259 * word2

def word261 : Fi22.Carrier := word260 * word2

def word262 : Fi22.Carrier := word261 * word1

def word263 : Fi22.Carrier := word262 * word2

def word264 : Fi22.Carrier := word263 * word1

def word265 : Fi22.Carrier := word1 * word264

def word266 : Fi22.Carrier := word265⁻¹

def word267 : Fi22.Carrier := word266 * word2

def word268 : Fi22.Carrier := word267 * word1

def word269 : Fi22.Carrier := word268 * word2

def word270 : Fi22.Carrier := word269 * word1

def word271 : Fi22.Carrier := word270 * word2

def word272 : Fi22.Carrier := word271 * word2

def word273 : Fi22.Carrier := word272 * word2

def word274 : Fi22.Carrier := word273 * word1

def word275 : Fi22.Carrier := word274 * word2

def word276 : Fi22.Carrier := word275 * word1

def word277 : Fi22.Carrier := word276 * word2

def word278 : Fi22.Carrier := word277 * word2

def word279 : Fi22.Carrier := word278 * word2

def word280 : Fi22.Carrier := word279 * word1

def word281 : Fi22.Carrier := word280 * word2

def word282 : Fi22.Carrier := word281 * word2

def word283 : Fi22.Carrier := word282 * word2

def word284 : Fi22.Carrier := word283 * word1

def word285 : Fi22.Carrier := word284 * word2

def word286 : Fi22.Carrier := word285 * word2

def word287 : Fi22.Carrier := word286 * word1

def word288 : Fi22.Carrier := word287 * word2

def word289 : Fi22.Carrier := word288 * word1

def word290 : Fi22.Carrier := word203 * word289

def word291 : Fi22.Carrier := word290 * word52

def word292 : Fi22.Carrier := word291 * word75

def word293 : Fi22.Carrier := word292 * word289

def word294 : Fi22.Carrier := word293 * word75

def word295 : Fi22.Carrier := word294 * word75

def word296 : Fi22.Carrier := word295 * word75

def word297 : Fi22.Carrier := word296 * word75

def word298 : Fi22.Carrier := word297 * word75

def word299 : Fi22.Carrier := word298 * word52

def word300 : Fi22.Carrier := word299 * word75

def word301 : Fi22.Carrier := word300 * word75

def word302 : Fi22.Carrier := word301 * word75

def word303 : Fi22.Carrier := word302 * word75

def word304 : Fi22.Carrier := word303 * word75

def word305 : Fi22.Carrier := word304 * word75

def word306 : Fi22.Carrier := word305 * word75

def word307 : Fi22.Carrier := word306 * word52

def word308 : Fi22.Carrier := word307 * word75

def word309 : Fi22.Carrier := word52 * word308

def word310 : Fi22.Carrier := word309⁻¹

def word311 : Fi22.Carrier := word310 * word75

def word312 : Fi22.Carrier := word311 * word75

def word313 : Fi22.Carrier := word312 * word75

def word314 : Fi22.Carrier := word313 * word289

def word315 : Fi22.Carrier := word314 * word52

def word316 : Fi22.Carrier := word315 * word75

def word317 : Fi22.Carrier := word316 * word289

def word318 : Fi22.Carrier := word317 * word75

def word319 : Fi22.Carrier := word318 * word75

def word320 : Fi22.Carrier := word319 * word75

def word321 : Fi22.Carrier := word320 * word75

def word322 : Fi22.Carrier := word321 * word75

def word323 : Fi22.Carrier := word322 * word52

def word324 : Fi22.Carrier := word323 * word75

def word325 : Fi22.Carrier := word324 * word75

def word326 : Fi22.Carrier := word325 * word75

def word327 : Fi22.Carrier := word326 * word75

def word328 : Fi22.Carrier := word327 * word75

def word329 : Fi22.Carrier := word328 * word75

def word330 : Fi22.Carrier := word329 * word75

def word331 : Fi22.Carrier := word330 * word52

def word332 : Fi22.Carrier := word331 * word75

def word333 : Fi22.Carrier := word124 * word242

def word334 : Fi22.Carrier := word333 * word124

def word335 : Fi22.Carrier := word334 * word112

def word336 : Fi22.Carrier := word335 * word332

def word337 : Fi22.Carrier := word336 * word159

def word338 : Fi22.Carrier := word337 * word124

def word339 : Fi22.Carrier := word338 * word124

def word340 : Fi22.Carrier := word339 * word124

def word341 : Fi22.Carrier := word340 * word124

def word342 : Fi22.Carrier := word341 * word124

def word343 : Fi22.Carrier := word342 * word124

def word344 : Fi22.Carrier := word343 * word124

def word345 : Fi22.Carrier := word344 * word124

def word346 : Fi22.Carrier := word124 * word345

def word347 : Fi22.Carrier := word346⁻¹

def word348 : Fi22.Carrier := word347 * word159

def word349 : Fi22.Carrier := word348 * word124

def word350 : Fi22.Carrier := word349 * word112

def word351 : Fi22.Carrier := word350 * word332

def word352 : Fi22.Carrier := word351 * word159

def word353 : Fi22.Carrier := word352 * word124

def word354 : Fi22.Carrier := word353 * word124

def word355 : Fi22.Carrier := word354 * word124

def word356 : Fi22.Carrier := word355 * word124

def word357 : Fi22.Carrier := word356 * word124

def word358 : Fi22.Carrier := word357 * word124

def word359 : Fi22.Carrier := word358 * word124

def word360 : Fi22.Carrier := word359 * word124

def word361 : Fi22.Carrier := word360 * word360

def word362 : Fi22.Carrier := word361 * word242

def word363 : Fi22.Carrier := word362 * word159

def word364 : Fi22.Carrier := word363 * word186

def word365 : Fi22.Carrier := word112 * word364

def word366 : Fi22.Carrier := word365⁻¹

def word367 : Fi22.Carrier := word366 * word360

def word368 : Fi22.Carrier := word367 * word360

def word369 : Fi22.Carrier := word368 * word242

def word370 : Fi22.Carrier := word369 * word159

def word371 : Fi22.Carrier := word370 * word186

def word372 : Fi22.Carrier := word242 * word364

def word373 : Fi22.Carrier := word372⁻¹

def word374 : Fi22.Carrier := word373 * word360

def word375 : Fi22.Carrier := word374 * word159

def word376 : Fi22.Carrier := word375 * word186

def word377 : Fi22.Carrier := word246 * word1

def word378 : Fi22.Carrier := word377 * word2

def word379 : Fi22.Carrier := word378 * word2

def word380 : Fi22.Carrier := word379 * word2

def word381 : Fi22.Carrier := word380 * word1

def word382 : Fi22.Carrier := word381 * word2

def word383 : Fi22.Carrier := word382 * word2

def word384 : Fi22.Carrier := word383 * word2

def word385 : Fi22.Carrier := word384 * word52

def word386 : Fi22.Carrier := word385 * word75

def word387 : Fi22.Carrier := word386 * word75

def word388 : Fi22.Carrier := word387 * word52

def word389 : Fi22.Carrier := word388 * word289

def word390 : Fi22.Carrier := word389 * word52

def word391 : Fi22.Carrier := word390 * word75

def word392 : Fi22.Carrier := word391 * word75

def word393 : Fi22.Carrier := word392 * word75

def word394 : Fi22.Carrier := word393 * word75

def word395 : Fi22.Carrier := word394 * word52

def word396 : Fi22.Carrier := word395 * word75

def word397 : Fi22.Carrier := word396 * word75

def word398 : Fi22.Carrier := word397 * word75

def word399 : Fi22.Carrier := word398 * word52

def word400 : Fi22.Carrier := word399 * word75

def word401 : Fi22.Carrier := word400 * word112

def word402 : Fi22.Carrier := word401 * word332

def word403 : Fi22.Carrier := word402 * word124

def word404 : Fi22.Carrier := word403 * word124

def word405 : Fi22.Carrier := word404 * word159

def word406 : Fi22.Carrier := word405 * word124

def word407 : Fi22.Carrier := word406 * word124

def word408 : Fi22.Carrier := word407 * word124

def word409 : Fi22.Carrier := word408 * word112

def word410 : Fi22.Carrier := word409 * word124

def word411 : Fi22.Carrier := word410 * word202

def word412 : Fi22.Carrier := word411 * word376

def word413 : Fi22.Carrier := word412 * word371

def word414 : Fi22.Carrier := word413 * word159

def word415 : Fi22.Carrier := word414 * word202

def word416 : Fi22.Carrier := word415 * word242

def word417 : Fi22.Carrier := word416 * word159

def word418 : Fi22.Carrier := word417⁻¹

def word419 : Fi22.Carrier := word1 * word2

def word420 : Fi22.Carrier := word419 * word1

def word421 : Fi22.Carrier := word420 * word2

def word422 : Fi22.Carrier := word421 * word1

def word423 : Fi22.Carrier := word422 * word2

def word424 : Fi22.Carrier := word423 * word1

def word425 : Fi22.Carrier := word424 * word2

def word426 : Fi22.Carrier := word425 * word1

def word427 : Fi22.Carrier := word426 * word2

def word428 : Fi22.Carrier := word427 * word1

def word429 : Fi22.Carrier := word428 * word2

def word430 : Fi22.Carrier := word429 * word2

def word431 : Fi22.Carrier := word430 * word1

def word432 : Fi22.Carrier := word431 * word2

def word433 : Fi22.Carrier := word432 * word1

def word434 : Fi22.Carrier := word433 * word2

def word435 : Fi22.Carrier := word434 * word2

def word436 : Fi22.Carrier := word435 * word1

def word437 : Fi22.Carrier := word436 * word289

def word438 : Fi22.Carrier := word437 * word75

def word439 : Fi22.Carrier := word438 * word75

def word440 : Fi22.Carrier := word439 * word289

def word441 : Fi22.Carrier := word440 * word75

def word442 : Fi22.Carrier := word441 * word75

def word443 : Fi22.Carrier := word442 * word52

def word444 : Fi22.Carrier := word443 * word75

def word445 : Fi22.Carrier := word444 * word75

def word446 : Fi22.Carrier := word445 * word52

def word447 : Fi22.Carrier := word446 * word75

def word448 : Fi22.Carrier := word447 * word75

def word449 : Fi22.Carrier := word448 * word52

def word450 : Fi22.Carrier := word449 * word75

def word451 : Fi22.Carrier := word450 * word75

def word452 : Fi22.Carrier := word451 * word75

def word453 : Fi22.Carrier := word452 * word75

def word454 : Fi22.Carrier := word453 * word112

def word455 : Fi22.Carrier := word454 * word332

def word456 : Fi22.Carrier := word455 * word124

def word457 : Fi22.Carrier := word456 * word112

def word458 : Fi22.Carrier := word457 * word124

def word459 : Fi22.Carrier := word458 * word159

def word460 : Fi22.Carrier := word459 * word124

def word461 : Fi22.Carrier := word460 * word124

def word462 : Fi22.Carrier := word461 * word124

def word463 : Fi22.Carrier := word462 * word124

def word464 : Fi22.Carrier := word463 * word124

def word465 : Fi22.Carrier := word464 * word186

def word466 : Fi22.Carrier := word465 * word112

def word467 : Fi22.Carrier := word466 * word376

def word468 : Fi22.Carrier := word467 * word242

def word469 : Fi22.Carrier := word468 * word242

def word470 : Fi22.Carrier := word469 * word242

def word471 : Fi22.Carrier := word470 * word159

def word472 : Fi22.Carrier := word471⁻¹

def word473 : Fi22.Carrier := word159 * word186

def word474 : Fi22.Carrier := word112 * word473

def word475 : Fi22.Carrier := word474⁻¹

def word476 : Fi22.Carrier := word475 * word159

def word477 : Fi22.Carrier := word476 * word186

def word478 : Fi22.Carrier := word244 * word2

def word479 : Fi22.Carrier := word478 * word2

def word480 : Fi22.Carrier := word479 * word2

def word481 : Fi22.Carrier := word480 * word1

def word482 : Fi22.Carrier := word481 * word2

def word483 : Fi22.Carrier := word482 * word1

def word484 : Fi22.Carrier := word483 * word2

def word485 : Fi22.Carrier := word484 * word1

def word486 : Fi22.Carrier := word485 * word2

def word487 : Fi22.Carrier := word486 * word1

def word488 : Fi22.Carrier := word487 * word2

def word489 : Fi22.Carrier := word488 * word2

def word490 : Fi22.Carrier := word489 * word75

def word491 : Fi22.Carrier := word490 * word75

def word492 : Fi22.Carrier := word491 * word289

def word493 : Fi22.Carrier := word492 * word75

def word494 : Fi22.Carrier := word493 * word75

def word495 : Fi22.Carrier := word494 * word289

def word496 : Fi22.Carrier := word495 * word52

def word497 : Fi22.Carrier := word496 * word75

def word498 : Fi22.Carrier := word497 * word75

def word499 : Fi22.Carrier := word498 * word52

def word500 : Fi22.Carrier := word499 * word75

def word501 : Fi22.Carrier := word500 * word75

def word502 : Fi22.Carrier := word501 * word75

def word503 : Fi22.Carrier := word502 * word75

def word504 : Fi22.Carrier := word503 * word52

def word505 : Fi22.Carrier := word504 * word332

def word506 : Fi22.Carrier := word505 * word124

def word507 : Fi22.Carrier := word506 * word124

def word508 : Fi22.Carrier := word507 * word159

def word509 : Fi22.Carrier := word508 * word124

def word510 : Fi22.Carrier := word509 * word124

def word511 : Fi22.Carrier := word510 * word124

def word512 : Fi22.Carrier := word511 * word112

def word513 : Fi22.Carrier := word512 * word124

def word514 : Fi22.Carrier := word513 * word242

def word515 : Fi22.Carrier := word514 * word360

def word516 : Fi22.Carrier := word515 * word186

def word517 : Fi22.Carrier := word516 * word112

def word518 : Fi22.Carrier := word517 * word242

def word519 : Fi22.Carrier := word518 * word376

def word520 : Fi22.Carrier := word519 * word371

def word521 : Fi22.Carrier := word520 * word242

def word522 : Fi22.Carrier := word521 * word242

def word523 : Fi22.Carrier := word522 * word477

def word524 : Fi22.Carrier := word523 * word159

def word525 : Fi22.Carrier := word524⁻¹

def word526 : Fi22.Carrier := word4 * word2

def word527 : Fi22.Carrier := word526 * word2

def word528 : Fi22.Carrier := word527 * word2

def word529 : Fi22.Carrier := word528 * word2

def word530 : Fi22.Carrier := word529 * word2

def word531 : Fi22.Carrier := word530 * word2

def word532 : Fi22.Carrier := word531 * word2

def word533 : Fi22.Carrier := word532 * word2

def word534 : Fi22.Carrier := word533 * word1

def word535 : Fi22.Carrier := word534 * word2

def word536 : Fi22.Carrier := word535 * word1

def word537 : Fi22.Carrier := word536 * word2

def word538 : Fi22.Carrier := word537 * word2

def word539 : Fi22.Carrier := word538 * word2

def word540 : Fi22.Carrier := word539 * word1

def word541 : Fi22.Carrier := word540 * word2

def word542 : Fi22.Carrier := word541 * word2

def word543 : Fi22.Carrier := word542 * word75

def word544 : Fi22.Carrier := word543 * word75

def word545 : Fi22.Carrier := word544 * word289

def word546 : Fi22.Carrier := word545 * word75

def word547 : Fi22.Carrier := word546 * word75

def word548 : Fi22.Carrier := word547 * word75

def word549 : Fi22.Carrier := word548 * word75

def word550 : Fi22.Carrier := word549 * word52

def word551 : Fi22.Carrier := word550 * word75

def word552 : Fi22.Carrier := word551 * word75

def word553 : Fi22.Carrier := word552 * word75

def word554 : Fi22.Carrier := word553 * word52

def word555 : Fi22.Carrier := word554 * word75

def word556 : Fi22.Carrier := word555 * word242

def word557 : Fi22.Carrier := word556 * word159

def word558 : Fi22.Carrier := word557 * word332

def word559 : Fi22.Carrier := word558 * word124

def word560 : Fi22.Carrier := word559 * word124

def word561 : Fi22.Carrier := word560 * word124

def word562 : Fi22.Carrier := word561 * word112

def word563 : Fi22.Carrier := word562 * word124

def word564 : Fi22.Carrier := word563 * word197

def word565 : Fi22.Carrier := word564 * word360

def word566 : Fi22.Carrier := word565 * word112

def word567 : Fi22.Carrier := word566 * word371

def word568 : Fi22.Carrier := word567 * word202

def word569 : Fi22.Carrier := word568 * word242

def word570 : Fi22.Carrier := word569 * word477

def word571 : Fi22.Carrier := word570 * word159

def word572 : Fi22.Carrier := word571⁻¹

def word573 : Fi22.Carrier := word535 * word2

def word574 : Fi22.Carrier := word573 * word2

def word575 : Fi22.Carrier := word574 * word1

def word576 : Fi22.Carrier := word575 * word2

def word577 : Fi22.Carrier := word576 * word1

def word578 : Fi22.Carrier := word577 * word52

def word579 : Fi22.Carrier := word578 * word75

def word580 : Fi22.Carrier := word579 * word75

def word581 : Fi22.Carrier := word580 * word75

def word582 : Fi22.Carrier := word581 * word52

def word583 : Fi22.Carrier := word582 * word289

def word584 : Fi22.Carrier := word583 * word75

def word585 : Fi22.Carrier := word584 * word75

def word586 : Fi22.Carrier := word585 * word52

def word587 : Fi22.Carrier := word586 * word75

def word588 : Fi22.Carrier := word587 * word52

def word589 : Fi22.Carrier := word588 * word75

def word590 : Fi22.Carrier := word589 * word75

def word591 : Fi22.Carrier := word590 * word124

def word592 : Fi22.Carrier := word591 * word332

def word593 : Fi22.Carrier := word592 * word124

def word594 : Fi22.Carrier := word593 * word124

def word595 : Fi22.Carrier := word594 * word112

def word596 : Fi22.Carrier := word595 * word202

def word597 : Fi22.Carrier := word596 * word376

def word598 : Fi22.Carrier := word597 * word371

def word599 : Fi22.Carrier := word598 * word202

def word600 : Fi22.Carrier := word599 * word159

def word601 : Fi22.Carrier := word600⁻¹

def word602 : Fi22.Carrier := word379 * word1

def word603 : Fi22.Carrier := word602 * word2

def word604 : Fi22.Carrier := word603 * word2

def word605 : Fi22.Carrier := word604 * word1

def word606 : Fi22.Carrier := word605 * word2

def word607 : Fi22.Carrier := word606 * word1

def word608 : Fi22.Carrier := word607 * word75

def word609 : Fi22.Carrier := word608 * word52

def word610 : Fi22.Carrier := word609 * word75

def word611 : Fi22.Carrier := word610 * word75

def word612 : Fi22.Carrier := word611 * word52

def word613 : Fi22.Carrier := word612 * word75

def word614 : Fi22.Carrier := word613 * word75

def word615 : Fi22.Carrier := word614 * word75

def word616 : Fi22.Carrier := word615 * word52

def word617 : Fi22.Carrier := word616 * word75

def word618 : Fi22.Carrier := word617 * word75

def word619 : Fi22.Carrier := word618 * word75

def word620 : Fi22.Carrier := word619 * word52

def word621 : Fi22.Carrier := word620 * word75

def word622 : Fi22.Carrier := word621 * word159

def word623 : Fi22.Carrier := word622 * word124

def word624 : Fi22.Carrier := word623 * word124

def word625 : Fi22.Carrier := word624 * word124

def word626 : Fi22.Carrier := word625 * word186

def word627 : Fi22.Carrier := word626 * word360

def word628 : Fi22.Carrier := word627 * word242

def word629 : Fi22.Carrier := word628 * word112

def word630 : Fi22.Carrier := word629 * word202

def word631 : Fi22.Carrier := word630 * word376

def word632 : Fi22.Carrier := word631 * word371

def word633 : Fi22.Carrier := word632 * word202

def word634 : Fi22.Carrier := word633 * word242

def word635 : Fi22.Carrier := word634 * word477

def word636 : Fi22.Carrier := word635 * word159

def word637 : Fi22.Carrier := word636⁻¹

def word638 : Fi22.Carrier := word423 * word2

def word639 : Fi22.Carrier := word638 * word1

def word640 : Fi22.Carrier := word639 * word2

def word641 : Fi22.Carrier := word640 * word1

def word642 : Fi22.Carrier := word641 * word2

def word643 : Fi22.Carrier := word642 * word2

def word644 : Fi22.Carrier := word643 * word2

def word645 : Fi22.Carrier := word644 * word1

def word646 : Fi22.Carrier := word645 * word2

def word647 : Fi22.Carrier := word646 * word2

def word648 : Fi22.Carrier := word647 * word289

def word649 : Fi22.Carrier := word648 * word52

def word650 : Fi22.Carrier := word649 * word75

def word651 : Fi22.Carrier := word650 * word289

def word652 : Fi22.Carrier := word651 * word75

def word653 : Fi22.Carrier := word652 * word75

def word654 : Fi22.Carrier := word653 * word75

def word655 : Fi22.Carrier := word654 * word75

def word656 : Fi22.Carrier := word655 * word52

def word657 : Fi22.Carrier := word656 * word75

def word658 : Fi22.Carrier := word657 * word75

def word659 : Fi22.Carrier := word658 * word75

def word660 : Fi22.Carrier := word659 * word75

def word661 : Fi22.Carrier := word660 * word75

def word662 : Fi22.Carrier := word661 * word52

def word663 : Fi22.Carrier := word662 * word242

def word664 : Fi22.Carrier := word663 * word124

def word665 : Fi22.Carrier := word664 * word112

def word666 : Fi22.Carrier := word665 * word332

def word667 : Fi22.Carrier := word666 * word159

def word668 : Fi22.Carrier := word667 * word124

def word669 : Fi22.Carrier := word668 * word124

def word670 : Fi22.Carrier := word669 * word124

def word671 : Fi22.Carrier := word670 * word124

def word672 : Fi22.Carrier := word671 * word124

def word673 : Fi22.Carrier := word672 * word124

def word674 : Fi22.Carrier := word673 * word124

def word675 : Fi22.Carrier := word674 * word124

def word676 : Fi22.Carrier := word675 * word197

def word677 : Fi22.Carrier := word676 * word112

def word678 : Fi22.Carrier := word677 * word202

def word679 : Fi22.Carrier := word678 * word376

def word680 : Fi22.Carrier := word679 * word202

def word681 : Fi22.Carrier := word680 * word242

def word682 : Fi22.Carrier := word681 * word477

def word683 : Fi22.Carrier := word682 * word159

def word684 : Fi22.Carrier := word683⁻¹

/-- Proposed images, with exact Fi22 membership built into their type. -/
def image : Fin 8 → Fi22.Carrier
  | 0 => word3
  | 1 => word418
  | 2 => word472
  | 3 => word525
  | 4 => word572
  | 5 => word601
  | 6 => word637
  | 7 => word684

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.ImageWords
