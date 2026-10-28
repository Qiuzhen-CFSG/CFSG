module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA301To310
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA311To320
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA321To330
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA331To340
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA341To350
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA351To360
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA361To370
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA371To380
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA381To390
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA391To399

/-!
# Maximal-subgroup classification for small even descent nodes 301–399

Each imported block checks short generating families and all binary Schreier
signatures using `NodeData.Valid`. The soundness theorem turns these finite
equations into core containment, an outside centralizer witness, or equality
with an edge. Case analysis joins the blocks without changing node or edge
numbering.

Source: Shinoda (1975), (2.3), pp. 81–82; the root-word conventions and input
provenance in `SmallEvenDescentEdgeData` and the certificate soundness proof in
`SmallEvenMaximalClassificationUpperSupport`.
-/

public section
namespace ReeTwo.SylowModel.SmallEvenUpperCertificates

/-- Every maximal subgroup of a node numbered 301 through 399 is classified. -/
theorem classified301To399 (i : Fin 600) (hlo : 301 ≤ i.val) (hhi : i.val < 400)
    (H : Subgroup SylowModel) (h : H ⋖ smallEvenDescentNode i) : Classified H := by
  rcases i with ⟨i, hi⟩
  change 301 ≤ i at hlo
  change i < 400 at hhi
  interval_cases i
  · exact classified301 H h
  · exact classified302 H h
  · exact classified303 H h
  · exact classified304 H h
  · exact classified305 H h
  · exact classified306 H h
  · exact classified307 H h
  · exact classified308 H h
  · exact classified309 H h
  · exact classified310 H h
  · exact classified311 H h
  · exact classified312 H h
  · exact classified313 H h
  · exact classified314 H h
  · exact classified315 H h
  · exact classified316 H h
  · exact classified317 H h
  · exact classified318 H h
  · exact classified319 H h
  · exact classified320 H h
  · exact classified321 H h
  · exact classified322 H h
  · exact classified323 H h
  · exact classified324 H h
  · exact classified325 H h
  · exact classified326 H h
  · exact classified327 H h
  · exact classified328 H h
  · exact classified329 H h
  · exact classified330 H h
  · exact classified331 H h
  · exact classified332 H h
  · exact classified333 H h
  · exact classified334 H h
  · exact classified335 H h
  · exact classified336 H h
  · exact classified337 H h
  · exact classified338 H h
  · exact classified339 H h
  · exact classified340 H h
  · exact classified341 H h
  · exact classified342 H h
  · exact classified343 H h
  · exact classified344 H h
  · exact classified345 H h
  · exact classified346 H h
  · exact classified347 H h
  · exact classified348 H h
  · exact classified349 H h
  · exact classified350 H h
  · exact classified351 H h
  · exact classified352 H h
  · exact classified353 H h
  · exact classified354 H h
  · exact classified355 H h
  · exact classified356 H h
  · exact classified357 H h
  · exact classified358 H h
  · exact classified359 H h
  · exact classified360 H h
  · exact classified361 H h
  · exact classified362 H h
  · exact classified363 H h
  · exact classified364 H h
  · exact classified365 H h
  · exact classified366 H h
  · exact classified367 H h
  · exact classified368 H h
  · exact classified369 H h
  · exact classified370 H h
  · exact classified371 H h
  · exact classified372 H h
  · exact classified373 H h
  · exact classified374 H h
  · exact classified375 H h
  · exact classified376 H h
  · exact classified377 H h
  · exact classified378 H h
  · exact classified379 H h
  · exact classified380 H h
  · exact classified381 H h
  · exact classified382 H h
  · exact classified383 H h
  · exact classified384 H h
  · exact classified385 H h
  · exact classified386 H h
  · exact classified387 H h
  · exact classified388 H h
  · exact classified389 H h
  · exact classified390 H h
  · exact classified391 H h
  · exact classified392 H h
  · exact classified393 H h
  · exact classified394 H h
  · exact classified395 H h
  · exact classified396 H h
  · exact classified397 H h
  · exact classified398 H h
  · exact classified399 H h

end ReeTwo.SylowModel.SmallEvenUpperCertificates
