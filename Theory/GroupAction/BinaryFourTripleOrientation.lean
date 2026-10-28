module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# An oriented automorphism of a binary four-space with a trilinear form

In the ordered bases (a,b,c,d) and (t,v,u,w), the alternating bilinear
commutator table has columns t, vt, u, uv, v, wu for the pairs ab, ac,
ad, bc, bd, cd. The pairing of these two spaces is antidiagonal.
Composing them gives the trilinear form below.

A transformation preserving this form and interchanging a,d must send
b to b+c+d and c to a+c+d. In fact five tensor identities already force
these two images, without any injectivity hypothesis. The finite certificate
is checked by kernel reduction over the 256 possible pairs of images.
This is a statement about the displayed tensor; transporting it to a group
requires proving its commutator table and invariance there.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.678–681, equations (2), (3), (5), (10)–(15), and (23).
-/

namespace Theory.GroupAction.BinaryFourTripleOrientation

/-- Binary coordinates in the ordered basis a,b,c,d. -/
public abbrev V := Fin 4 → ZMod 2

/-- The specified alternating commutator table, in the basis t,v,u,w. -/
@[expose] public def bracket (x y : V) : V :=
  ![x 0 * y 1 + x 1 * y 0 + x 0 * y 2 + x 2 * y 0,
    x 0 * y 2 + x 2 * y 0 + x 1 * y 2 + x 2 * y 1 + x 1 * y 3 + x 3 * y 1,
    x 0 * y 3 + x 3 * y 0 + x 1 * y 2 + x 2 * y 1 + x 2 * y 3 + x 3 * y 2,
    x 2 * y 3 + x 3 * y 2]

/-- The antidiagonal pairing between the core and derived coordinates. -/
@[expose] public def pairing (x u : V) : ZMod 2 :=
  x 0 * u 3 + x 1 * u 2 + x 2 * u 1 + x 3 * u 0

/-- The scalar triple commutator associated to the two specified tables. -/
@[expose] public def tensor (x y z : V) : ZMod 2 := pairing z (bracket x y)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Five invariant triple commutators force both remaining oriented images. -/
public theorem remaining_images (b c : V)
    (h012 : tensor ![0,0,0,1] b c = 0)
    (h021 : tensor ![0,0,0,1] c b = 0)
    (h032 : tensor ![0,0,0,1] ![1,0,0,0] c = 0)
    (h122 : tensor b c c = 1)
    (h123 : tensor b c ![1,0,0,0] = 0) :
    b = ![0,1,1,1] ∧ c = ![1,0,1,1] := by
  exact (by decide +kernel : ∀ b c : V,
    tensor ![0,0,0,1] b c = 0 →
    tensor ![0,0,0,1] c b = 0 →
    tensor ![0,0,0,1] ![1,0,0,0] c = 0 →
    tensor b c c = 1 → tensor b c ![1,0,0,0] = 0 →
    b = ![0,1,1,1] ∧ c = ![1,0,1,1]) b c h012 h021 h032 h122 h123

end Theory.GroupAction.BinaryFourTripleOrientation
