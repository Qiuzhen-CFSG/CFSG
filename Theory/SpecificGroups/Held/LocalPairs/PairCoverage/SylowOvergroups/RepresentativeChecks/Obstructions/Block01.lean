module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.CachedActions
import Mathlib.Tactic.FinCases

/-!
# Prime-order obstructions for Held representatives 256 through 511

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
private theorem obstruction_0256 : HasPrimeObstruction (representative 256) := by
  apply obstruction_of_cachedAction 256 [5] 5 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0257 : HasPrimeObstruction (representative 257) := by
  apply obstruction_of_cachedAction 257 [5] 7 1
    (by decide) (by decide) (by decide) 114
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0258 : HasPrimeObstruction (representative 258) := by
  apply obstruction_of_cachedAction 258 [5, 1] 7 1
    (by decide) (by decide) (by decide) 140
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0259 : HasPrimeObstruction (representative 259) := by
  apply obstruction_of_cachedAction 259 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0260 : HasPrimeObstruction (representative 260) := by
  apply obstruction_of_cachedAction 260 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0261 : HasPrimeObstruction (representative 261) := by
  apply obstruction_of_cachedAction 261 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0262 : HasPrimeObstruction (representative 262) := by
  apply obstruction_of_cachedAction 262 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0263 : HasPrimeObstruction (representative 263) := by
  apply obstruction_of_cachedAction 263 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0264 : HasPrimeObstruction (representative 264) := by
  apply obstruction_of_cachedAction 264 [5] 5 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0265 : HasPrimeObstruction (representative 265) := by
  apply obstruction_of_cachedAction 265 [5] 7 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0266 : HasPrimeObstruction (representative 266) := by
  apply obstruction_of_cachedAction 266 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0267 : HasPrimeObstruction (representative 267) := by
  apply obstruction_of_cachedAction 267 [5] 7 1
    (by decide) (by decide) (by decide) 52
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0268 : HasPrimeObstruction (representative 268) := by
  apply obstruction_of_cachedAction 268 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0269 : HasPrimeObstruction (representative 269) := by
  apply obstruction_of_cachedAction 269 [5, 1] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0270 : HasPrimeObstruction (representative 270) := by
  apply obstruction_of_cachedAction 270 [5] 7 1
    (by decide) (by decide) (by decide) 197
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0271 : HasPrimeObstruction (representative 271) := by
  apply obstruction_of_cachedAction 271 [5, 2] 7 1
    (by decide) (by decide) (by decide) 153
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0272 : HasPrimeObstruction (representative 272) := by
  apply obstruction_of_cachedAction 272 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0273 : HasPrimeObstruction (representative 273) := by
  apply obstruction_of_cachedAction 273 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0274 : HasPrimeObstruction (representative 274) := by
  apply obstruction_of_cachedAction 274 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0275 : HasPrimeObstruction (representative 275) := by
  apply obstruction_of_cachedAction 275 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0276 : HasPrimeObstruction (representative 276) := by
  apply obstruction_of_cachedAction 276 [5, 3] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0277 : HasPrimeObstruction (representative 277) := by
  apply obstruction_of_cachedAction 277 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0278 : HasPrimeObstruction (representative 278) := by
  apply obstruction_of_cachedAction 278 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0279 : HasPrimeObstruction (representative 279) := by
  apply obstruction_of_cachedAction 279 [5, 3] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0280 : HasPrimeObstruction (representative 280) := by
  apply obstruction_of_cachedAction 280 [5, 1] 7 1
    (by decide) (by decide) (by decide) 94
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0281 : HasPrimeObstruction (representative 281) := by
  apply obstruction_of_cachedAction 281 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0282 : HasPrimeObstruction (representative 282) := by
  apply obstruction_of_cachedAction 282 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0283 : HasPrimeObstruction (representative 283) := by
  apply obstruction_of_cachedAction 283 [5, 1] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0284 : HasPrimeObstruction (representative 284) := by
  apply obstruction_of_cachedAction 284 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0285 : HasPrimeObstruction (representative 285) := by
  apply obstruction_of_cachedAction 285 [5] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0286 : HasPrimeObstruction (representative 286) := by
  apply obstruction_of_cachedAction 286 [5, 4] 5 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0287 : HasPrimeObstruction (representative 287) := by
  apply obstruction_of_cachedAction 287 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0288 : HasPrimeObstruction (representative 288) := by
  apply obstruction_of_cachedAction 288 [5, 1] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0289 : HasPrimeObstruction (representative 289) := by
  apply obstruction_of_cachedAction 289 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0290 : HasPrimeObstruction (representative 290) := by
  apply obstruction_of_cachedAction 290 [5, 2] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0291 : HasPrimeObstruction (representative 291) := by
  apply obstruction_of_cachedAction 291 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0292 : HasPrimeObstruction (representative 292) := by
  apply obstruction_of_cachedAction 292 [5, 1] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0293 : HasPrimeObstruction (representative 293) := by
  apply obstruction_of_cachedAction 293 [5, 4] 5 1
    (by decide) (by decide) (by decide) 193
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0294 : HasPrimeObstruction (representative 294) := by
  apply obstruction_of_cachedAction 294 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0295 : HasPrimeObstruction (representative 295) := by
  apply obstruction_of_cachedAction 295 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0296 : HasPrimeObstruction (representative 296) := by
  apply obstruction_of_cachedAction 296 [5, 1] 7 1
    (by decide) (by decide) (by decide) 39
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0297 : HasPrimeObstruction (representative 297) := by
  apply obstruction_of_cachedAction 297 [5, 1] 5 1
    (by decide) (by decide) (by decide) 44
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0298 : HasPrimeObstruction (representative 298) := by
  apply obstruction_of_cachedAction 298 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0299 : HasPrimeObstruction (representative 299) := by
  apply obstruction_of_cachedAction 299 [5] 7 1
    (by decide) (by decide) (by decide) 48
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0300 : HasPrimeObstruction (representative 300) := by
  apply obstruction_of_cachedAction 300 [5] 5 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0301 : HasPrimeObstruction (representative 301) := by
  apply obstruction_of_cachedAction 301 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0302 : HasPrimeObstruction (representative 302) := by
  apply obstruction_of_cachedAction 302 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0303 : HasPrimeObstruction (representative 303) := by
  apply obstruction_of_cachedAction 303 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0304 : HasPrimeObstruction (representative 304) := by
  apply obstruction_of_cachedAction 304 [5] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0305 : HasPrimeObstruction (representative 305) := by
  apply obstruction_of_cachedAction 305 [5] 7 1
    (by decide) (by decide) (by decide) 221
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0306 : HasPrimeObstruction (representative 306) := by
  apply obstruction_of_cachedAction 306 [5] 5 1
    (by decide) (by decide) (by decide) 115
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0307 : HasPrimeObstruction (representative 307) := by
  apply obstruction_of_cachedAction 307 [5] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0308 : HasPrimeObstruction (representative 308) := by
  apply obstruction_of_cachedAction 308 [5] 5 1
    (by decide) (by decide) (by decide) 129
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0309 : HasPrimeObstruction (representative 309) := by
  apply obstruction_of_cachedAction 309 [5] 7 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0310 : HasPrimeObstruction (representative 310) := by
  apply obstruction_of_cachedAction 310 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0311 : HasPrimeObstruction (representative 311) := by
  apply obstruction_of_cachedAction 311 [5] 7 1
    (by decide) (by decide) (by decide) 70
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0312 : HasPrimeObstruction (representative 312) := by
  apply obstruction_of_cachedAction 312 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0313 : HasPrimeObstruction (representative 313) := by
  apply obstruction_of_cachedAction 313 [5] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0314 : HasPrimeObstruction (representative 314) := by
  apply obstruction_of_cachedAction 314 [5, 1] 5 1
    (by decide) (by decide) (by decide) 44
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0315 : HasPrimeObstruction (representative 315) := by
  apply obstruction_of_cachedAction 315 [5, 1] 5 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0316 : HasPrimeObstruction (representative 316) := by
  apply obstruction_of_cachedAction 316 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0317 : HasPrimeObstruction (representative 317) := by
  apply obstruction_of_cachedAction 317 [5, 1] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0318 : HasPrimeObstruction (representative 318) := by
  apply obstruction_of_cachedAction 318 [5, 2] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0319 : HasPrimeObstruction (representative 319) := by
  apply obstruction_of_cachedAction 319 [5] 7 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0320 : HasPrimeObstruction (representative 320) := by
  apply obstruction_of_cachedAction 320 [5] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0321 : HasPrimeObstruction (representative 321) := by
  apply obstruction_of_cachedAction 321 [5] 7 1
    (by decide) (by decide) (by decide) 96
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0322 : HasPrimeObstruction (representative 322) := by
  apply obstruction_of_cachedAction 322 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0323 : HasPrimeObstruction (representative 323) := by
  apply obstruction_of_cachedAction 323 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0324 : HasPrimeObstruction (representative 324) := by
  apply obstruction_of_cachedAction 324 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0325 : HasPrimeObstruction (representative 325) := by
  apply obstruction_of_cachedAction 325 [5, 2] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0326 : HasPrimeObstruction (representative 326) := by
  apply obstruction_of_cachedAction 326 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0327 : HasPrimeObstruction (representative 327) := by
  apply obstruction_of_cachedAction 327 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0328 : HasPrimeObstruction (representative 328) := by
  apply obstruction_of_cachedAction 328 [5] 7 1
    (by decide) (by decide) (by decide) 151
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0329 : HasPrimeObstruction (representative 329) := by
  apply obstruction_of_cachedAction 329 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0330 : HasPrimeObstruction (representative 330) := by
  apply obstruction_of_cachedAction 330 [5] 7 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0331 : HasPrimeObstruction (representative 331) := by
  apply obstruction_of_cachedAction 331 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0332 : HasPrimeObstruction (representative 332) := by
  apply obstruction_of_cachedAction 332 [5, 4] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0333 : HasPrimeObstruction (representative 333) := by
  apply obstruction_of_cachedAction 333 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0334 : HasPrimeObstruction (representative 334) := by
  apply obstruction_of_cachedAction 334 [5, 3] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0335 : HasPrimeObstruction (representative 335) := by
  apply obstruction_of_cachedAction 335 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0336 : HasPrimeObstruction (representative 336) := by
  apply obstruction_of_cachedAction 336 [5, 1] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0337 : HasPrimeObstruction (representative 337) := by
  apply obstruction_of_cachedAction 337 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0338 : HasPrimeObstruction (representative 338) := by
  apply obstruction_of_cachedAction 338 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0339 : HasPrimeObstruction (representative 339) := by
  apply obstruction_of_cachedAction 339 [5, 2] 7 1
    (by decide) (by decide) (by decide) 323
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0340 : HasPrimeObstruction (representative 340) := by
  apply obstruction_of_cachedAction 340 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0341 : HasPrimeObstruction (representative 341) := by
  apply obstruction_of_cachedAction 341 [5] 7 1
    (by decide) (by decide) (by decide) 84
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0342 : HasPrimeObstruction (representative 342) := by
  apply obstruction_of_cachedAction 342 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0343 : HasPrimeObstruction (representative 343) := by
  apply obstruction_of_cachedAction 343 [5] 7 1
    (by decide) (by decide) (by decide) 77
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0344 : HasPrimeObstruction (representative 344) := by
  apply obstruction_of_cachedAction 344 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0345 : HasPrimeObstruction (representative 345) := by
  apply obstruction_of_cachedAction 345 [5, 1] 7 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0346 : HasPrimeObstruction (representative 346) := by
  apply obstruction_of_cachedAction 346 [5, 2] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0347 : HasPrimeObstruction (representative 347) := by
  apply obstruction_of_cachedAction 347 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0348 : HasPrimeObstruction (representative 348) := by
  apply obstruction_of_cachedAction 348 [5] 7 1
    (by decide) (by decide) (by decide) 633
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0349 : HasPrimeObstruction (representative 349) := by
  apply obstruction_of_cachedAction 349 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0350 : HasPrimeObstruction (representative 350) := by
  apply obstruction_of_cachedAction 350 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0351 : HasPrimeObstruction (representative 351) := by
  apply obstruction_of_cachedAction 351 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0352 : HasPrimeObstruction (representative 352) := by
  apply obstruction_of_cachedAction 352 [5, 1] 7 1
    (by decide) (by decide) (by decide) 99
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0353 : HasPrimeObstruction (representative 353) := by
  apply obstruction_of_cachedAction 353 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0354 : HasPrimeObstruction (representative 354) := by
  apply obstruction_of_cachedAction 354 [5, 3] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0355 : HasPrimeObstruction (representative 355) := by
  apply obstruction_of_cachedAction 355 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0356 : HasPrimeObstruction (representative 356) := by
  apply obstruction_of_cachedAction 356 [5] 7 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0357 : HasPrimeObstruction (representative 357) := by
  apply obstruction_of_cachedAction 357 [5] 5 1
    (by decide) (by decide) (by decide) 163
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0358 : HasPrimeObstruction (representative 358) := by
  apply obstruction_of_cachedAction 358 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0359 : HasPrimeObstruction (representative 359) := by
  apply obstruction_of_cachedAction 359 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0360 : HasPrimeObstruction (representative 360) := by
  apply obstruction_of_cachedAction 360 [5] 7 1
    (by decide) (by decide) (by decide) 203
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0361 : HasPrimeObstruction (representative 361) := by
  apply obstruction_of_cachedAction 361 [5] 7 1
    (by decide) (by decide) (by decide) 53
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0362 : HasPrimeObstruction (representative 362) := by
  apply obstruction_of_cachedAction 362 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0363 : HasPrimeObstruction (representative 363) := by
  apply obstruction_of_cachedAction 363 [5] 7 1
    (by decide) (by decide) (by decide) 249
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0364 : HasPrimeObstruction (representative 364) := by
  apply obstruction_of_cachedAction 364 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0365 : HasPrimeObstruction (representative 365) := by
  apply obstruction_of_cachedAction 365 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0366 : HasPrimeObstruction (representative 366) := by
  apply obstruction_of_cachedAction 366 [5, 1] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0367 : HasPrimeObstruction (representative 367) := by
  apply obstruction_of_cachedAction 367 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0368 : HasPrimeObstruction (representative 368) := by
  apply obstruction_of_cachedAction 368 [5] 5 1
    (by decide) (by decide) (by decide) 61
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0369 : HasPrimeObstruction (representative 369) := by
  apply obstruction_of_cachedAction 369 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0370 : HasPrimeObstruction (representative 370) := by
  apply obstruction_of_cachedAction 370 [5] 7 1
    (by decide) (by decide) (by decide) 52
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0371 : HasPrimeObstruction (representative 371) := by
  apply obstruction_of_cachedAction 371 [5] 7 1
    (by decide) (by decide) (by decide) 79
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0372 : HasPrimeObstruction (representative 372) := by
  apply obstruction_of_cachedAction 372 [5] 7 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0373 : HasPrimeObstruction (representative 373) := by
  apply obstruction_of_cachedAction 373 [5, 2] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0374 : HasPrimeObstruction (representative 374) := by
  apply obstruction_of_cachedAction 374 [5, 2] 5 1
    (by decide) (by decide) (by decide) 91
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0375 : HasPrimeObstruction (representative 375) := by
  apply obstruction_of_cachedAction 375 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0376 : HasPrimeObstruction (representative 376) := by
  apply obstruction_of_cachedAction 376 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0377 : HasPrimeObstruction (representative 377) := by
  apply obstruction_of_cachedAction 377 [5, 3] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0378 : HasPrimeObstruction (representative 378) := by
  apply obstruction_of_cachedAction 378 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0379 : HasPrimeObstruction (representative 379) := by
  apply obstruction_of_cachedAction 379 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0380 : HasPrimeObstruction (representative 380) := by
  apply obstruction_of_cachedAction 380 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0381 : HasPrimeObstruction (representative 381) := by
  apply obstruction_of_cachedAction 381 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0382 : HasPrimeObstruction (representative 382) := by
  apply obstruction_of_cachedAction 382 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0383 : HasPrimeObstruction (representative 383) := by
  apply obstruction_of_cachedAction 383 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0384 : HasPrimeObstruction (representative 384) := by
  apply obstruction_of_cachedAction 384 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0385 : HasPrimeObstruction (representative 385) := by
  apply obstruction_of_cachedAction 385 [5, 1] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0386 : HasPrimeObstruction (representative 386) := by
  apply obstruction_of_cachedAction 386 [5] 5 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0387 : HasPrimeObstruction (representative 387) := by
  apply obstruction_of_cachedAction 387 [5, 2] 5 1
    (by decide) (by decide) (by decide) 149
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0388 : HasPrimeObstruction (representative 388) := by
  apply obstruction_of_cachedAction 388 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0389 : HasPrimeObstruction (representative 389) := by
  apply obstruction_of_cachedAction 389 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0390 : HasPrimeObstruction (representative 390) := by
  apply obstruction_of_cachedAction 390 [5, 4] 7 1
    (by decide) (by decide) (by decide) 45
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0391 : HasPrimeObstruction (representative 391) := by
  apply obstruction_of_cachedAction 391 [5, 2] 5 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0392 : HasPrimeObstruction (representative 392) := by
  apply obstruction_of_cachedAction 392 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0393 : HasPrimeObstruction (representative 393) := by
  apply obstruction_of_cachedAction 393 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0394 : HasPrimeObstruction (representative 394) := by
  apply obstruction_of_cachedAction 394 [5] 7 1
    (by decide) (by decide) (by decide) 104
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0395 : HasPrimeObstruction (representative 395) := by
  apply obstruction_of_cachedAction 395 [5] 5 1
    (by decide) (by decide) (by decide) 89
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0396 : HasPrimeObstruction (representative 396) := by
  apply obstruction_of_cachedAction 396 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0397 : HasPrimeObstruction (representative 397) := by
  apply obstruction_of_cachedAction 397 [5] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0398 : HasPrimeObstruction (representative 398) := by
  apply obstruction_of_cachedAction 398 [5] 7 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0399 : HasPrimeObstruction (representative 399) := by
  apply obstruction_of_cachedAction 399 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0400 : HasPrimeObstruction (representative 400) := by
  apply obstruction_of_cachedAction 400 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0401 : HasPrimeObstruction (representative 401) := by
  apply obstruction_of_cachedAction 401 [5, 1] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0402 : HasPrimeObstruction (representative 402) := by
  apply obstruction_of_cachedAction 402 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0403 : HasPrimeObstruction (representative 403) := by
  apply obstruction_of_cachedAction 403 [5, 2] 7 1
    (by decide) (by decide) (by decide) 229
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0404 : HasPrimeObstruction (representative 404) := by
  apply obstruction_of_cachedAction 404 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0405 : HasPrimeObstruction (representative 405) := by
  apply obstruction_of_cachedAction 405 [5, 1] 7 1
    (by decide) (by decide) (by decide) 78
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0406 : HasPrimeObstruction (representative 406) := by
  apply obstruction_of_cachedAction 406 [5] 7 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0407 : HasPrimeObstruction (representative 407) := by
  apply obstruction_of_cachedAction 407 [5, 1] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0408 : HasPrimeObstruction (representative 408) := by
  apply obstruction_of_cachedAction 408 [5, 1] 7 1
    (by decide) (by decide) (by decide) 193
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0409 : HasPrimeObstruction (representative 409) := by
  apply obstruction_of_cachedAction 409 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0410 : HasPrimeObstruction (representative 410) := by
  apply obstruction_of_cachedAction 410 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0411 : HasPrimeObstruction (representative 411) := by
  apply obstruction_of_cachedAction 411 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0412 : HasPrimeObstruction (representative 412) := by
  apply obstruction_of_cachedAction 412 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0413 : HasPrimeObstruction (representative 413) := by
  apply obstruction_of_cachedAction 413 [5] 7 1
    (by decide) (by decide) (by decide) 194
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0414 : HasPrimeObstruction (representative 414) := by
  apply obstruction_of_cachedAction 414 [5] 7 1
    (by decide) (by decide) (by decide) 48
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0415 : HasPrimeObstruction (representative 415) := by
  apply obstruction_of_cachedAction 415 [5, 2] 7 1
    (by decide) (by decide) (by decide) 142
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0416 : HasPrimeObstruction (representative 416) := by
  apply obstruction_of_cachedAction 416 [5, 4] 7 1
    (by decide) (by decide) (by decide) 336
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0417 : HasPrimeObstruction (representative 417) := by
  apply obstruction_of_cachedAction 417 [5, 1] 7 1
    (by decide) (by decide) (by decide) 61
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0418 : HasPrimeObstruction (representative 418) := by
  apply obstruction_of_cachedAction 418 [5, 3] 7 1
    (by decide) (by decide) (by decide) 736
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0419 : HasPrimeObstruction (representative 419) := by
  apply obstruction_of_cachedAction 419 [5] 7 1
    (by decide) (by decide) (by decide) 85
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0420 : HasPrimeObstruction (representative 420) := by
  apply obstruction_of_cachedAction 420 [5] 7 1
    (by decide) (by decide) (by decide) 25
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0421 : HasPrimeObstruction (representative 421) := by
  apply obstruction_of_cachedAction 421 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0422 : HasPrimeObstruction (representative 422) := by
  apply obstruction_of_cachedAction 422 [5] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0423 : HasPrimeObstruction (representative 423) := by
  apply obstruction_of_cachedAction 423 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0424 : HasPrimeObstruction (representative 424) := by
  apply obstruction_of_cachedAction 424 [5] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0425 : HasPrimeObstruction (representative 425) := by
  apply obstruction_of_cachedAction 425 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0426 : HasPrimeObstruction (representative 426) := by
  apply obstruction_of_cachedAction 426 [5] 7 1
    (by decide) (by decide) (by decide) 239
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0427 : HasPrimeObstruction (representative 427) := by
  apply obstruction_of_cachedAction 427 [5] 7 1
    (by decide) (by decide) (by decide) 88
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0428 : HasPrimeObstruction (representative 428) := by
  apply obstruction_of_cachedAction 428 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0429 : HasPrimeObstruction (representative 429) := by
  apply obstruction_of_cachedAction 429 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0430 : HasPrimeObstruction (representative 430) := by
  apply obstruction_of_cachedAction 430 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0431 : HasPrimeObstruction (representative 431) := by
  apply obstruction_of_cachedAction 431 [5, 3] 7 1
    (by decide) (by decide) (by decide) 72
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0432 : HasPrimeObstruction (representative 432) := by
  apply obstruction_of_cachedAction 432 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0433 : HasPrimeObstruction (representative 433) := by
  apply obstruction_of_cachedAction 433 [5] 5 1
    (by decide) (by decide) (by decide) 86
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0434 : HasPrimeObstruction (representative 434) := by
  apply obstruction_of_cachedAction 434 [5] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0435 : HasPrimeObstruction (representative 435) := by
  apply obstruction_of_cachedAction 435 [5] 7 1
    (by decide) (by decide) (by decide) 136
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0436 : HasPrimeObstruction (representative 436) := by
  apply obstruction_of_cachedAction 436 [5, 3] 5 1
    (by decide) (by decide) (by decide) 47
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0437 : HasPrimeObstruction (representative 437) := by
  apply obstruction_of_cachedAction 437 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0438 : HasPrimeObstruction (representative 438) := by
  apply obstruction_of_cachedAction 438 [5] 5 1
    (by decide) (by decide) (by decide) 78
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0439 : HasPrimeObstruction (representative 439) := by
  apply obstruction_of_cachedAction 439 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0440 : HasPrimeObstruction (representative 440) := by
  apply obstruction_of_cachedAction 440 [5] 7 1
    (by decide) (by decide) (by decide) 40
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0441 : HasPrimeObstruction (representative 441) := by
  apply obstruction_of_cachedAction 441 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0442 : HasPrimeObstruction (representative 442) := by
  apply obstruction_of_cachedAction 442 [5, 1] 7 1
    (by decide) (by decide) (by decide) 56
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0443 : HasPrimeObstruction (representative 443) := by
  apply obstruction_of_cachedAction 443 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0444 : HasPrimeObstruction (representative 444) := by
  apply obstruction_of_cachedAction 444 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0445 : HasPrimeObstruction (representative 445) := by
  apply obstruction_of_cachedAction 445 [5] 7 1
    (by decide) (by decide) (by decide) 100
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0446 : HasPrimeObstruction (representative 446) := by
  apply obstruction_of_cachedAction 446 [5] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0447 : HasPrimeObstruction (representative 447) := by
  apply obstruction_of_cachedAction 447 [5] 7 1
    (by decide) (by decide) (by decide) 74
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0448 : HasPrimeObstruction (representative 448) := by
  apply obstruction_of_cachedAction 448 [5] 7 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0449 : HasPrimeObstruction (representative 449) := by
  apply obstruction_of_cachedAction 449 [5, 4] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0450 : HasPrimeObstruction (representative 450) := by
  apply obstruction_of_cachedAction 450 [5, 4] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0451 : HasPrimeObstruction (representative 451) := by
  apply obstruction_of_cachedAction 451 [5, 3] 5 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0452 : HasPrimeObstruction (representative 452) := by
  apply obstruction_of_cachedAction 452 [5, 3] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0453 : HasPrimeObstruction (representative 453) := by
  apply obstruction_of_cachedAction 453 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0454 : HasPrimeObstruction (representative 454) := by
  apply obstruction_of_cachedAction 454 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0455 : HasPrimeObstruction (representative 455) := by
  apply obstruction_of_cachedAction 455 [5, 4] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0456 : HasPrimeObstruction (representative 456) := by
  apply obstruction_of_cachedAction 456 [5, 2] 7 1
    (by decide) (by decide) (by decide) 79
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0457 : HasPrimeObstruction (representative 457) := by
  apply obstruction_of_cachedAction 457 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0458 : HasPrimeObstruction (representative 458) := by
  apply obstruction_of_cachedAction 458 [5, 2] 5 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0459 : HasPrimeObstruction (representative 459) := by
  apply obstruction_of_cachedAction 459 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0460 : HasPrimeObstruction (representative 460) := by
  apply obstruction_of_cachedAction 460 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0461 : HasPrimeObstruction (representative 461) := by
  apply obstruction_of_cachedAction 461 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0462 : HasPrimeObstruction (representative 462) := by
  apply obstruction_of_cachedAction 462 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0463 : HasPrimeObstruction (representative 463) := by
  apply obstruction_of_cachedAction 463 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0464 : HasPrimeObstruction (representative 464) := by
  apply obstruction_of_cachedAction 464 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0465 : HasPrimeObstruction (representative 465) := by
  apply obstruction_of_cachedAction 465 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0466 : HasPrimeObstruction (representative 466) := by
  apply obstruction_of_cachedAction 466 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0467 : HasPrimeObstruction (representative 467) := by
  apply obstruction_of_cachedAction 467 [5, 1] 5 1
    (by decide) (by decide) (by decide) 37
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0468 : HasPrimeObstruction (representative 468) := by
  apply obstruction_of_cachedAction 468 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0469 : HasPrimeObstruction (representative 469) := by
  apply obstruction_of_cachedAction 469 [5, 1] 7 1
    (by decide) (by decide) (by decide) 50
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0470 : HasPrimeObstruction (representative 470) := by
  apply obstruction_of_cachedAction 470 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0471 : HasPrimeObstruction (representative 471) := by
  apply obstruction_of_cachedAction 471 [5, 2] 5 1
    (by decide) (by decide) (by decide) 94
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0472 : HasPrimeObstruction (representative 472) := by
  apply obstruction_of_cachedAction 472 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0473 : HasPrimeObstruction (representative 473) := by
  apply obstruction_of_cachedAction 473 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0474 : HasPrimeObstruction (representative 474) := by
  apply obstruction_of_cachedAction 474 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0475 : HasPrimeObstruction (representative 475) := by
  apply obstruction_of_cachedAction 475 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0476 : HasPrimeObstruction (representative 476) := by
  apply obstruction_of_cachedAction 476 [5, 1] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0477 : HasPrimeObstruction (representative 477) := by
  apply obstruction_of_cachedAction 477 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0478 : HasPrimeObstruction (representative 478) := by
  apply obstruction_of_cachedAction 478 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0479 : HasPrimeObstruction (representative 479) := by
  apply obstruction_of_cachedAction 479 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0480 : HasPrimeObstruction (representative 480) := by
  apply obstruction_of_cachedAction 480 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0481 : HasPrimeObstruction (representative 481) := by
  apply obstruction_of_cachedAction 481 [5] 7 1
    (by decide) (by decide) (by decide) 97
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0482 : HasPrimeObstruction (representative 482) := by
  apply obstruction_of_cachedAction 482 [5, 3] 5 1
    (by decide) (by decide) (by decide) 96
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0483 : HasPrimeObstruction (representative 483) := by
  apply obstruction_of_cachedAction 483 [5] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0484 : HasPrimeObstruction (representative 484) := by
  apply obstruction_of_cachedAction 484 [5] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0485 : HasPrimeObstruction (representative 485) := by
  apply obstruction_of_cachedAction 485 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0486 : HasPrimeObstruction (representative 486) := by
  apply obstruction_of_cachedAction 486 [5, 3] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0487 : HasPrimeObstruction (representative 487) := by
  apply obstruction_of_cachedAction 487 [5] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0488 : HasPrimeObstruction (representative 488) := by
  apply obstruction_of_cachedAction 488 [5] 5 1
    (by decide) (by decide) (by decide) 43
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0489 : HasPrimeObstruction (representative 489) := by
  apply obstruction_of_cachedAction 489 [5, 2] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0490 : HasPrimeObstruction (representative 490) := by
  apply obstruction_of_cachedAction 490 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0491 : HasPrimeObstruction (representative 491) := by
  apply obstruction_of_cachedAction 491 [5] 7 1
    (by decide) (by decide) (by decide) 64
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0492 : HasPrimeObstruction (representative 492) := by
  apply obstruction_of_cachedAction 492 [5, 3] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0493 : HasPrimeObstruction (representative 493) := by
  apply obstruction_of_cachedAction 493 [5] 5 1
    (by decide) (by decide) (by decide) 74
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0494 : HasPrimeObstruction (representative 494) := by
  apply obstruction_of_cachedAction 494 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0495 : HasPrimeObstruction (representative 495) := by
  apply obstruction_of_cachedAction 495 [5, 3] 5 1
    (by decide) (by decide) (by decide) 37
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0496 : HasPrimeObstruction (representative 496) := by
  apply obstruction_of_cachedAction 496 [5] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0497 : HasPrimeObstruction (representative 497) := by
  apply obstruction_of_cachedAction 497 [5, 1] 7 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0498 : HasPrimeObstruction (representative 498) := by
  apply obstruction_of_cachedAction 498 [5] 7 1
    (by decide) (by decide) (by decide) 184
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0499 : HasPrimeObstruction (representative 499) := by
  apply obstruction_of_cachedAction 499 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0500 : HasPrimeObstruction (representative 500) := by
  apply obstruction_of_cachedAction 500 [5, 3] 7 1
    (by decide) (by decide) (by decide) 134
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0501 : HasPrimeObstruction (representative 501) := by
  apply obstruction_of_cachedAction 501 [5, 4] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0502 : HasPrimeObstruction (representative 502) := by
  apply obstruction_of_cachedAction 502 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0503 : HasPrimeObstruction (representative 503) := by
  apply obstruction_of_cachedAction 503 [5] 5 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0504 : HasPrimeObstruction (representative 504) := by
  apply obstruction_of_cachedAction 504 [5, 1] 7 1
    (by decide) (by decide) (by decide) 314
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0505 : HasPrimeObstruction (representative 505) := by
  apply obstruction_of_cachedAction 505 [5] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0506 : HasPrimeObstruction (representative 506) := by
  apply obstruction_of_cachedAction 506 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0507 : HasPrimeObstruction (representative 507) := by
  apply obstruction_of_cachedAction 507 [5, 2] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0508 : HasPrimeObstruction (representative 508) := by
  apply obstruction_of_cachedAction 508 [5] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0509 : HasPrimeObstruction (representative 509) := by
  apply obstruction_of_cachedAction 509 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0510 : HasPrimeObstruction (representative 510) := by
  apply obstruction_of_cachedAction 510 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0511 : HasPrimeObstruction (representative 511) := by
  apply obstruction_of_cachedAction 511 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

/-- Every nonlocal representative in this interval has a forbidden prime order. -/
public theorem obstruction_block01 (j : Fin 256)
    (h : localBranch ⟨256 + j.val, by omega⟩ = none) :
    HasPrimeObstruction (representative ⟨256 + j.val, by omega⟩) := by
  fin_cases j
  · exact obstruction_0256
  · exact obstruction_0257
  · exact obstruction_0258
  · exact obstruction_0259
  · exact obstruction_0260
  · exact obstruction_0261
  · exact obstruction_0262
  · exact obstruction_0263
  · exact obstruction_0264
  · exact obstruction_0265
  · exact obstruction_0266
  · exact obstruction_0267
  · exact obstruction_0268
  · exact obstruction_0269
  · exact obstruction_0270
  · exact obstruction_0271
  · exact obstruction_0272
  · exact obstruction_0273
  · exact obstruction_0274
  · exact obstruction_0275
  · exact obstruction_0276
  · exact obstruction_0277
  · exact obstruction_0278
  · exact obstruction_0279
  · exact obstruction_0280
  · exact obstruction_0281
  · exact obstruction_0282
  · exact obstruction_0283
  · exact obstruction_0284
  · exact obstruction_0285
  · exact obstruction_0286
  · exact obstruction_0287
  · exact obstruction_0288
  · exact obstruction_0289
  · exact obstruction_0290
  · exact obstruction_0291
  · exact obstruction_0292
  · exact obstruction_0293
  · exact obstruction_0294
  · exact obstruction_0295
  · exact obstruction_0296
  · exact obstruction_0297
  · exact obstruction_0298
  · exact obstruction_0299
  · exact obstruction_0300
  · exact obstruction_0301
  · exact obstruction_0302
  · exact obstruction_0303
  · exact obstruction_0304
  · exact obstruction_0305
  · exact obstruction_0306
  · exact obstruction_0307
  · exact obstruction_0308
  · exact obstruction_0309
  · exact obstruction_0310
  · exact obstruction_0311
  · exact obstruction_0312
  · exact obstruction_0313
  · exact obstruction_0314
  · exact obstruction_0315
  · exact obstruction_0316
  · exact obstruction_0317
  · exact obstruction_0318
  · exact obstruction_0319
  · exact obstruction_0320
  · exact obstruction_0321
  · exact obstruction_0322
  · exact obstruction_0323
  · exact obstruction_0324
  · exact obstruction_0325
  · exact obstruction_0326
  · exact obstruction_0327
  · exact obstruction_0328
  · exact obstruction_0329
  · exact obstruction_0330
  · exact obstruction_0331
  · exact obstruction_0332
  · exact obstruction_0333
  · exact obstruction_0334
  · exact obstruction_0335
  · exact obstruction_0336
  · exact obstruction_0337
  · exact obstruction_0338
  · exact obstruction_0339
  · exact obstruction_0340
  · exact obstruction_0341
  · exact obstruction_0342
  · exact obstruction_0343
  · exact obstruction_0344
  · exact obstruction_0345
  · exact obstruction_0346
  · exact obstruction_0347
  · exact obstruction_0348
  · exact obstruction_0349
  · exact obstruction_0350
  · exact obstruction_0351
  · exact obstruction_0352
  · exact obstruction_0353
  · exact obstruction_0354
  · exact obstruction_0355
  · exact obstruction_0356
  · exact obstruction_0357
  · exact obstruction_0358
  · exact obstruction_0359
  · exact obstruction_0360
  · exact obstruction_0361
  · exact obstruction_0362
  · exact obstruction_0363
  · exact obstruction_0364
  · exact obstruction_0365
  · exact obstruction_0366
  · exact obstruction_0367
  · exact obstruction_0368
  · exact obstruction_0369
  · exact obstruction_0370
  · exact obstruction_0371
  · exact obstruction_0372
  · exact obstruction_0373
  · exact obstruction_0374
  · exact obstruction_0375
  · exact obstruction_0376
  · exact obstruction_0377
  · exact obstruction_0378
  · exact obstruction_0379
  · exact obstruction_0380
  · exact obstruction_0381
  · exact obstruction_0382
  · exact obstruction_0383
  · exact obstruction_0384
  · exact obstruction_0385
  · exact obstruction_0386
  · exact obstruction_0387
  · exact obstruction_0388
  · exact obstruction_0389
  · exact obstruction_0390
  · exact obstruction_0391
  · exact obstruction_0392
  · exact obstruction_0393
  · exact obstruction_0394
  · exact obstruction_0395
  · exact obstruction_0396
  · exact obstruction_0397
  · exact obstruction_0398
  · exact obstruction_0399
  · exact obstruction_0400
  · exact obstruction_0401
  · exact obstruction_0402
  · exact obstruction_0403
  · exact obstruction_0404
  · exact obstruction_0405
  · exact obstruction_0406
  · exact obstruction_0407
  · exact obstruction_0408
  · exact obstruction_0409
  · exact obstruction_0410
  · exact obstruction_0411
  · exact obstruction_0412
  · exact obstruction_0413
  · exact obstruction_0414
  · exact obstruction_0415
  · exact obstruction_0416
  · exact obstruction_0417
  · exact obstruction_0418
  · exact obstruction_0419
  · exact obstruction_0420
  · exact obstruction_0421
  · exact obstruction_0422
  · exact obstruction_0423
  · exact obstruction_0424
  · exact obstruction_0425
  · exact obstruction_0426
  · exact obstruction_0427
  · exact obstruction_0428
  · exact obstruction_0429
  · exact obstruction_0430
  · exact obstruction_0431
  · exact obstruction_0432
  · exact obstruction_0433
  · exact obstruction_0434
  · exact obstruction_0435
  · exact obstruction_0436
  · exact obstruction_0437
  · exact obstruction_0438
  · exact obstruction_0439
  · exact obstruction_0440
  · exact obstruction_0441
  · exact obstruction_0442
  · exact obstruction_0443
  · exact obstruction_0444
  · exact obstruction_0445
  · exact obstruction_0446
  · exact obstruction_0447
  · exact obstruction_0448
  · exact obstruction_0449
  · exact obstruction_0450
  · exact obstruction_0451
  · exact obstruction_0452
  · exact obstruction_0453
  · exact obstruction_0454
  · exact obstruction_0455
  · exact obstruction_0456
  · exact obstruction_0457
  · exact obstruction_0458
  · exact obstruction_0459
  · exact obstruction_0460
  · exact obstruction_0461
  · exact obstruction_0462
  · exact obstruction_0463
  · exact obstruction_0464
  · exact obstruction_0465
  · exact obstruction_0466
  · exact obstruction_0467
  · exact obstruction_0468
  · exact obstruction_0469
  · exact obstruction_0470
  · exact obstruction_0471
  · exact obstruction_0472
  · exact obstruction_0473
  · exact obstruction_0474
  · exact obstruction_0475
  · exact obstruction_0476
  · exact obstruction_0477
  · exact obstruction_0478
  · exact obstruction_0479
  · exact obstruction_0480
  · exact obstruction_0481
  · exact obstruction_0482
  · exact obstruction_0483
  · exact obstruction_0484
  · exact obstruction_0485
  · exact obstruction_0486
  · exact obstruction_0487
  · exact obstruction_0488
  · exact obstruction_0489
  · exact obstruction_0490
  · exact obstruction_0491
  · exact obstruction_0492
  · exact obstruction_0493
  · exact obstruction_0494
  · exact obstruction_0495
  · exact obstruction_0496
  · exact obstruction_0497
  · exact obstruction_0498
  · exact obstruction_0499
  · exact obstruction_0500
  · exact obstruction_0501
  · exact obstruction_0502
  · exact obstruction_0503
  · exact obstruction_0504
  · exact obstruction_0505
  · exact obstruction_0506
  · exact obstruction_0507
  · exact obstruction_0508
  · exact obstruction_0509
  · exact obstruction_0510
  · exact obstruction_0511

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
