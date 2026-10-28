module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Check

/-!
# Forward v and r checks on the range starting at 12288

Each block checks 64 labels by kernel reduction. The balanced checker joins
these blocks to certify a range of 4096 consecutive indices. The last range
uses `Fin.ofNat` beyond 31670; those repeated labels do not affect coverage.

Source: the literal words and retained ATLAS tables described in `VAndR.Check`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

-- Each reduction cache is released before the next declaration is elaborated.
set_option Elab.async false

private theorem block192 : checkPow pointTest 12288 6 = true := by
  decide +kernel

private theorem block193 : checkPow pointTest 12352 6 = true := by
  decide +kernel

private theorem block194 : checkPow pointTest 12416 6 = true := by
  decide +kernel

private theorem block195 : checkPow pointTest 12480 6 = true := by
  decide +kernel

private theorem block196 : checkPow pointTest 12544 6 = true := by
  decide +kernel

private theorem block197 : checkPow pointTest 12608 6 = true := by
  decide +kernel

private theorem block198 : checkPow pointTest 12672 6 = true := by
  decide +kernel

private theorem block199 : checkPow pointTest 12736 6 = true := by
  decide +kernel

private theorem block200 : checkPow pointTest 12800 6 = true := by
  decide +kernel

private theorem block201 : checkPow pointTest 12864 6 = true := by
  decide +kernel

private theorem block202 : checkPow pointTest 12928 6 = true := by
  decide +kernel

private theorem block203 : checkPow pointTest 12992 6 = true := by
  decide +kernel

private theorem block204 : checkPow pointTest 13056 6 = true := by
  decide +kernel

private theorem block205 : checkPow pointTest 13120 6 = true := by
  decide +kernel

private theorem block206 : checkPow pointTest 13184 6 = true := by
  decide +kernel

private theorem block207 : checkPow pointTest 13248 6 = true := by
  decide +kernel

private theorem block208 : checkPow pointTest 13312 6 = true := by
  decide +kernel

private theorem block209 : checkPow pointTest 13376 6 = true := by
  decide +kernel

private theorem block210 : checkPow pointTest 13440 6 = true := by
  decide +kernel

private theorem block211 : checkPow pointTest 13504 6 = true := by
  decide +kernel

private theorem block212 : checkPow pointTest 13568 6 = true := by
  decide +kernel

private theorem block213 : checkPow pointTest 13632 6 = true := by
  decide +kernel

private theorem block214 : checkPow pointTest 13696 6 = true := by
  decide +kernel

private theorem block215 : checkPow pointTest 13760 6 = true := by
  decide +kernel

private theorem block216 : checkPow pointTest 13824 6 = true := by
  decide +kernel

private theorem block217 : checkPow pointTest 13888 6 = true := by
  decide +kernel

private theorem block218 : checkPow pointTest 13952 6 = true := by
  decide +kernel

private theorem block219 : checkPow pointTest 14016 6 = true := by
  decide +kernel

private theorem block220 : checkPow pointTest 14080 6 = true := by
  decide +kernel

private theorem block221 : checkPow pointTest 14144 6 = true := by
  decide +kernel

private theorem block222 : checkPow pointTest 14208 6 = true := by
  decide +kernel

private theorem block223 : checkPow pointTest 14272 6 = true := by
  decide +kernel

private theorem block224 : checkPow pointTest 14336 6 = true := by
  decide +kernel

private theorem block225 : checkPow pointTest 14400 6 = true := by
  decide +kernel

private theorem block226 : checkPow pointTest 14464 6 = true := by
  decide +kernel

private theorem block227 : checkPow pointTest 14528 6 = true := by
  decide +kernel

private theorem block228 : checkPow pointTest 14592 6 = true := by
  decide +kernel

private theorem block229 : checkPow pointTest 14656 6 = true := by
  decide +kernel

private theorem block230 : checkPow pointTest 14720 6 = true := by
  decide +kernel

private theorem block231 : checkPow pointTest 14784 6 = true := by
  decide +kernel

private theorem block232 : checkPow pointTest 14848 6 = true := by
  decide +kernel

private theorem block233 : checkPow pointTest 14912 6 = true := by
  decide +kernel

private theorem block234 : checkPow pointTest 14976 6 = true := by
  decide +kernel

private theorem block235 : checkPow pointTest 15040 6 = true := by
  decide +kernel

private theorem block236 : checkPow pointTest 15104 6 = true := by
  decide +kernel

private theorem block237 : checkPow pointTest 15168 6 = true := by
  decide +kernel

private theorem block238 : checkPow pointTest 15232 6 = true := by
  decide +kernel

private theorem block239 : checkPow pointTest 15296 6 = true := by
  decide +kernel

private theorem block240 : checkPow pointTest 15360 6 = true := by
  decide +kernel

private theorem block241 : checkPow pointTest 15424 6 = true := by
  decide +kernel

private theorem block242 : checkPow pointTest 15488 6 = true := by
  decide +kernel

private theorem block243 : checkPow pointTest 15552 6 = true := by
  decide +kernel

private theorem block244 : checkPow pointTest 15616 6 = true := by
  decide +kernel

private theorem block245 : checkPow pointTest 15680 6 = true := by
  decide +kernel

private theorem block246 : checkPow pointTest 15744 6 = true := by
  decide +kernel

private theorem block247 : checkPow pointTest 15808 6 = true := by
  decide +kernel

private theorem block248 : checkPow pointTest 15872 6 = true := by
  decide +kernel

private theorem block249 : checkPow pointTest 15936 6 = true := by
  decide +kernel

private theorem block250 : checkPow pointTest 16000 6 = true := by
  decide +kernel

private theorem block251 : checkPow pointTest 16064 6 = true := by
  decide +kernel

private theorem block252 : checkPow pointTest 16128 6 = true := by
  decide +kernel

private theorem block253 : checkPow pointTest 16192 6 = true := by
  decide +kernel

private theorem block254 : checkPow pointTest 16256 6 = true := by
  decide +kernel

private theorem block255 : checkPow pointTest 16320 6 = true := by
  decide +kernel

/-- The two word actions on a complete 4096-index range. -/
theorem checked3 : checkPow pointTest 12288 12 = true :=
  (checkPow_join pointTest 11 12288
    (checkPow_join pointTest 10 12288
    (checkPow_join pointTest 9 12288
    (checkPow_join pointTest 8 12288
    (checkPow_join pointTest 7 12288
    (checkPow_join pointTest 6 12288
    block192
    block193)
    (checkPow_join pointTest 6 12416
    block194
    block195))
    (checkPow_join pointTest 7 12544
    (checkPow_join pointTest 6 12544
    block196
    block197)
    (checkPow_join pointTest 6 12672
    block198
    block199)))
    (checkPow_join pointTest 8 12800
    (checkPow_join pointTest 7 12800
    (checkPow_join pointTest 6 12800
    block200
    block201)
    (checkPow_join pointTest 6 12928
    block202
    block203))
    (checkPow_join pointTest 7 13056
    (checkPow_join pointTest 6 13056
    block204
    block205)
    (checkPow_join pointTest 6 13184
    block206
    block207))))
    (checkPow_join pointTest 9 13312
    (checkPow_join pointTest 8 13312
    (checkPow_join pointTest 7 13312
    (checkPow_join pointTest 6 13312
    block208
    block209)
    (checkPow_join pointTest 6 13440
    block210
    block211))
    (checkPow_join pointTest 7 13568
    (checkPow_join pointTest 6 13568
    block212
    block213)
    (checkPow_join pointTest 6 13696
    block214
    block215)))
    (checkPow_join pointTest 8 13824
    (checkPow_join pointTest 7 13824
    (checkPow_join pointTest 6 13824
    block216
    block217)
    (checkPow_join pointTest 6 13952
    block218
    block219))
    (checkPow_join pointTest 7 14080
    (checkPow_join pointTest 6 14080
    block220
    block221)
    (checkPow_join pointTest 6 14208
    block222
    block223)))))
    (checkPow_join pointTest 10 14336
    (checkPow_join pointTest 9 14336
    (checkPow_join pointTest 8 14336
    (checkPow_join pointTest 7 14336
    (checkPow_join pointTest 6 14336
    block224
    block225)
    (checkPow_join pointTest 6 14464
    block226
    block227))
    (checkPow_join pointTest 7 14592
    (checkPow_join pointTest 6 14592
    block228
    block229)
    (checkPow_join pointTest 6 14720
    block230
    block231)))
    (checkPow_join pointTest 8 14848
    (checkPow_join pointTest 7 14848
    (checkPow_join pointTest 6 14848
    block232
    block233)
    (checkPow_join pointTest 6 14976
    block234
    block235))
    (checkPow_join pointTest 7 15104
    (checkPow_join pointTest 6 15104
    block236
    block237)
    (checkPow_join pointTest 6 15232
    block238
    block239))))
    (checkPow_join pointTest 9 15360
    (checkPow_join pointTest 8 15360
    (checkPow_join pointTest 7 15360
    (checkPow_join pointTest 6 15360
    block240
    block241)
    (checkPow_join pointTest 6 15488
    block242
    block243))
    (checkPow_join pointTest 7 15616
    (checkPow_join pointTest 6 15616
    block244
    block245)
    (checkPow_join pointTest 6 15744
    block246
    block247)))
    (checkPow_join pointTest 8 15872
    (checkPow_join pointTest 7 15872
    (checkPow_join pointTest 6 15872
    block248
    block249)
    (checkPow_join pointTest 6 16000
    block250
    block251))
    (checkPow_join pointTest 7 16128
    (checkPow_join pointTest 6 16128
    block252
    block253)
    (checkPow_join pointTest 6 16256
    block254
    block255))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
