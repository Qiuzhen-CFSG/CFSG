module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Check

/-!
# Forward v and r checks on the range starting at 16384

Each block checks 64 labels by kernel reduction. The balanced checker joins
these blocks to certify a range of 4096 consecutive indices. The last range
uses `Fin.ofNat` beyond 31670; those repeated labels do not affect coverage.

Source: the literal words and retained ATLAS tables described in `VAndR.Check`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

-- Each reduction cache is released before the next declaration is elaborated.
set_option Elab.async false

private theorem block256 : checkPow pointTest 16384 6 = true := by
  decide +kernel

private theorem block257 : checkPow pointTest 16448 6 = true := by
  decide +kernel

private theorem block258 : checkPow pointTest 16512 6 = true := by
  decide +kernel

private theorem block259 : checkPow pointTest 16576 6 = true := by
  decide +kernel

private theorem block260 : checkPow pointTest 16640 6 = true := by
  decide +kernel

private theorem block261 : checkPow pointTest 16704 6 = true := by
  decide +kernel

private theorem block262 : checkPow pointTest 16768 6 = true := by
  decide +kernel

private theorem block263 : checkPow pointTest 16832 6 = true := by
  decide +kernel

private theorem block264 : checkPow pointTest 16896 6 = true := by
  decide +kernel

private theorem block265 : checkPow pointTest 16960 6 = true := by
  decide +kernel

private theorem block266 : checkPow pointTest 17024 6 = true := by
  decide +kernel

private theorem block267 : checkPow pointTest 17088 6 = true := by
  decide +kernel

private theorem block268 : checkPow pointTest 17152 6 = true := by
  decide +kernel

private theorem block269 : checkPow pointTest 17216 6 = true := by
  decide +kernel

private theorem block270 : checkPow pointTest 17280 6 = true := by
  decide +kernel

private theorem block271 : checkPow pointTest 17344 6 = true := by
  decide +kernel

private theorem block272 : checkPow pointTest 17408 6 = true := by
  decide +kernel

private theorem block273 : checkPow pointTest 17472 6 = true := by
  decide +kernel

private theorem block274 : checkPow pointTest 17536 6 = true := by
  decide +kernel

private theorem block275 : checkPow pointTest 17600 6 = true := by
  decide +kernel

private theorem block276 : checkPow pointTest 17664 6 = true := by
  decide +kernel

private theorem block277 : checkPow pointTest 17728 6 = true := by
  decide +kernel

private theorem block278 : checkPow pointTest 17792 6 = true := by
  decide +kernel

private theorem block279 : checkPow pointTest 17856 6 = true := by
  decide +kernel

private theorem block280 : checkPow pointTest 17920 6 = true := by
  decide +kernel

private theorem block281 : checkPow pointTest 17984 6 = true := by
  decide +kernel

private theorem block282 : checkPow pointTest 18048 6 = true := by
  decide +kernel

private theorem block283 : checkPow pointTest 18112 6 = true := by
  decide +kernel

private theorem block284 : checkPow pointTest 18176 6 = true := by
  decide +kernel

private theorem block285 : checkPow pointTest 18240 6 = true := by
  decide +kernel

private theorem block286 : checkPow pointTest 18304 6 = true := by
  decide +kernel

private theorem block287 : checkPow pointTest 18368 6 = true := by
  decide +kernel

private theorem block288 : checkPow pointTest 18432 6 = true := by
  decide +kernel

private theorem block289 : checkPow pointTest 18496 6 = true := by
  decide +kernel

private theorem block290 : checkPow pointTest 18560 6 = true := by
  decide +kernel

private theorem block291 : checkPow pointTest 18624 6 = true := by
  decide +kernel

private theorem block292 : checkPow pointTest 18688 6 = true := by
  decide +kernel

private theorem block293 : checkPow pointTest 18752 6 = true := by
  decide +kernel

private theorem block294 : checkPow pointTest 18816 6 = true := by
  decide +kernel

private theorem block295 : checkPow pointTest 18880 6 = true := by
  decide +kernel

private theorem block296 : checkPow pointTest 18944 6 = true := by
  decide +kernel

private theorem block297 : checkPow pointTest 19008 6 = true := by
  decide +kernel

private theorem block298 : checkPow pointTest 19072 6 = true := by
  decide +kernel

private theorem block299 : checkPow pointTest 19136 6 = true := by
  decide +kernel

private theorem block300 : checkPow pointTest 19200 6 = true := by
  decide +kernel

private theorem block301 : checkPow pointTest 19264 6 = true := by
  decide +kernel

private theorem block302 : checkPow pointTest 19328 6 = true := by
  decide +kernel

private theorem block303 : checkPow pointTest 19392 6 = true := by
  decide +kernel

private theorem block304 : checkPow pointTest 19456 6 = true := by
  decide +kernel

private theorem block305 : checkPow pointTest 19520 6 = true := by
  decide +kernel

private theorem block306 : checkPow pointTest 19584 6 = true := by
  decide +kernel

private theorem block307 : checkPow pointTest 19648 6 = true := by
  decide +kernel

private theorem block308 : checkPow pointTest 19712 6 = true := by
  decide +kernel

private theorem block309 : checkPow pointTest 19776 6 = true := by
  decide +kernel

private theorem block310 : checkPow pointTest 19840 6 = true := by
  decide +kernel

private theorem block311 : checkPow pointTest 19904 6 = true := by
  decide +kernel

private theorem block312 : checkPow pointTest 19968 6 = true := by
  decide +kernel

private theorem block313 : checkPow pointTest 20032 6 = true := by
  decide +kernel

private theorem block314 : checkPow pointTest 20096 6 = true := by
  decide +kernel

private theorem block315 : checkPow pointTest 20160 6 = true := by
  decide +kernel

private theorem block316 : checkPow pointTest 20224 6 = true := by
  decide +kernel

private theorem block317 : checkPow pointTest 20288 6 = true := by
  decide +kernel

private theorem block318 : checkPow pointTest 20352 6 = true := by
  decide +kernel

private theorem block319 : checkPow pointTest 20416 6 = true := by
  decide +kernel

/-- The two word actions on a complete 4096-index range. -/
theorem checked4 : checkPow pointTest 16384 12 = true :=
  (checkPow_join pointTest 11 16384
    (checkPow_join pointTest 10 16384
    (checkPow_join pointTest 9 16384
    (checkPow_join pointTest 8 16384
    (checkPow_join pointTest 7 16384
    (checkPow_join pointTest 6 16384
    block256
    block257)
    (checkPow_join pointTest 6 16512
    block258
    block259))
    (checkPow_join pointTest 7 16640
    (checkPow_join pointTest 6 16640
    block260
    block261)
    (checkPow_join pointTest 6 16768
    block262
    block263)))
    (checkPow_join pointTest 8 16896
    (checkPow_join pointTest 7 16896
    (checkPow_join pointTest 6 16896
    block264
    block265)
    (checkPow_join pointTest 6 17024
    block266
    block267))
    (checkPow_join pointTest 7 17152
    (checkPow_join pointTest 6 17152
    block268
    block269)
    (checkPow_join pointTest 6 17280
    block270
    block271))))
    (checkPow_join pointTest 9 17408
    (checkPow_join pointTest 8 17408
    (checkPow_join pointTest 7 17408
    (checkPow_join pointTest 6 17408
    block272
    block273)
    (checkPow_join pointTest 6 17536
    block274
    block275))
    (checkPow_join pointTest 7 17664
    (checkPow_join pointTest 6 17664
    block276
    block277)
    (checkPow_join pointTest 6 17792
    block278
    block279)))
    (checkPow_join pointTest 8 17920
    (checkPow_join pointTest 7 17920
    (checkPow_join pointTest 6 17920
    block280
    block281)
    (checkPow_join pointTest 6 18048
    block282
    block283))
    (checkPow_join pointTest 7 18176
    (checkPow_join pointTest 6 18176
    block284
    block285)
    (checkPow_join pointTest 6 18304
    block286
    block287)))))
    (checkPow_join pointTest 10 18432
    (checkPow_join pointTest 9 18432
    (checkPow_join pointTest 8 18432
    (checkPow_join pointTest 7 18432
    (checkPow_join pointTest 6 18432
    block288
    block289)
    (checkPow_join pointTest 6 18560
    block290
    block291))
    (checkPow_join pointTest 7 18688
    (checkPow_join pointTest 6 18688
    block292
    block293)
    (checkPow_join pointTest 6 18816
    block294
    block295)))
    (checkPow_join pointTest 8 18944
    (checkPow_join pointTest 7 18944
    (checkPow_join pointTest 6 18944
    block296
    block297)
    (checkPow_join pointTest 6 19072
    block298
    block299))
    (checkPow_join pointTest 7 19200
    (checkPow_join pointTest 6 19200
    block300
    block301)
    (checkPow_join pointTest 6 19328
    block302
    block303))))
    (checkPow_join pointTest 9 19456
    (checkPow_join pointTest 8 19456
    (checkPow_join pointTest 7 19456
    (checkPow_join pointTest 6 19456
    block304
    block305)
    (checkPow_join pointTest 6 19584
    block306
    block307))
    (checkPow_join pointTest 7 19712
    (checkPow_join pointTest 6 19712
    block308
    block309)
    (checkPow_join pointTest 6 19840
    block310
    block311)))
    (checkPow_join pointTest 8 19968
    (checkPow_join pointTest 7 19968
    (checkPow_join pointTest 6 19968
    block312
    block313)
    (checkPow_join pointTest 6 20096
    block314
    block315))
    (checkPow_join pointTest 7 20224
    (checkPow_join pointTest 6 20224
    block316
    block317)
    (checkPow_join pointTest 6 20352
    block318
    block319))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
