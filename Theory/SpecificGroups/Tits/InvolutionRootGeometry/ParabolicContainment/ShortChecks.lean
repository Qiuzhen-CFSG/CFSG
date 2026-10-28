module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.ParabolicContainment.ShortTest

/-!
# Complete short-root coset exclusion certificate

All 4717 immutable words from the certified R₁ cover are checked, each at
five rotation exponents and against the four possible Sylow conjugates of
s₄. Each exclusion uses only points zero and one. The accepted words contain
no r₁, and have rotation exponent zero, so they lie in the second parabolic.

The bounded checks use direct point evaluation with a proved interpretation
in `ShortTest`. They are elaborated sequentially to bound the memory used by
kernel reduction. No native decision procedure or external computation is
trusted. Source: Parrott (1972), §5, p.683; Aschbacher--Smith 16.1.4(1), p.1171.
-/

namespace Tits.InvolutionRootGeometry.ParabolicContainment.Certificate

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check0000 :
    (Tits.R1Certificate.input.reps.toList.drop 0 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check0256 :
    (Tits.R1Certificate.input.reps.toList.drop 256 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check0512 :
    (Tits.R1Certificate.input.reps.toList.drop 512 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check0768 :
    (Tits.R1Certificate.input.reps.toList.drop 768 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check1024 :
    (Tits.R1Certificate.input.reps.toList.drop 1024 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check1280 :
    (Tits.R1Certificate.input.reps.toList.drop 1280 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check1536 :
    (Tits.R1Certificate.input.reps.toList.drop 1536 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check1792 :
    (Tits.R1Certificate.input.reps.toList.drop 1792 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check2048 :
    (Tits.R1Certificate.input.reps.toList.drop 2048 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check2304 :
    (Tits.R1Certificate.input.reps.toList.drop 2304 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check2560 :
    (Tits.R1Certificate.input.reps.toList.drop 2560 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check2816 :
    (Tits.R1Certificate.input.reps.toList.drop 2816 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check3072 :
    (Tits.R1Certificate.input.reps.toList.drop 3072 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check3328 :
    (Tits.R1Certificate.input.reps.toList.drop 3328 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check3584 :
    (Tits.R1Certificate.input.reps.toList.drop 3584 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check3840 :
    (Tits.R1Certificate.input.reps.toList.drop 3840 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check4096 :
    (Tits.R1Certificate.input.reps.toList.drop 4096 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check4352 :
    (Tits.R1Certificate.input.reps.toList.drop 4352 |>.take 256).all pointTest = true := by
  decide +kernel

set_option Elab.async false in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
public theorem check4608 :
    (Tits.R1Certificate.input.reps.toList.drop 4608 |>.take 256).all pointTest = true := by
  decide +kernel

end Tits.InvolutionRootGeometry.ParabolicContainment.Certificate
