module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.CoreCoordinates
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.ReMarking
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Generation
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Center

/-!
# The outer M₁₂ second parabolic and compatible whole-overlap markings

For the fixed degree-24 carrier and an `InnerModel`, the normalizer of the
natural four has order 384, two-core of order 64, and quotient S₃. Its
intersection with C(z) is the actual Sylow two-subgroup of order 128; its
local Sylow normalizer is that intersection, and the two parabolics generate
the carrier. The center and central first omega have image ⟨z⟩.

The injective quaternion-swap map and `SecondGeometry` witness retain both
whole-overlap cosets, the literal twist, and the generating actor's four
action equations. Explicit quaternion basis changes identify both factors,
their core and their marked plane with the published lifted M₁₂ marks.
The second two-core has its own embedded centralizer and 64-coordinate
presentation; it is not identified with the quaternion-swap image.

These are conditional model calculations. The outer-model assembly owner
supplies `InnerModel` and the identification with Aut(M₁₂).
Source: Aschbacher--Smith, F.1.12(I)(13), printed p.263, and 14.2.21,
printed p.988; ATLAS coordinates are attributed in `Extension.Seeds`.
-/
