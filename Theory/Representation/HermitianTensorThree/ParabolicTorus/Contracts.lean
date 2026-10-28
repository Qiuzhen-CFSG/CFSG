module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Overgroups
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.Representation.BinaryOffender.Basic

/-!
# Odd actors preserving a Hermitian tensor parabolic

The two parabolics below are the literal images of the stabilizers of the
standard point and plane in the natural SL₃ module. Their conjugates cover
both types of maximal parabolic. Preservation means normalization of these
image subgroups by the original binary linear actor.

Two separate model calculations are needed for the application to
Aschbacher–Smith 8.2.3. An odd actor fixing more than one third of the
Hermitian space must preserve the fixed-field scalars. An odd, fixed-field
linear actor preserving a maximal parabolic has order dividing
`2^(4*n)-1`. This is the nonsplit parabolic bound; preservation alone does
not put the actor in a split torus of order `2^(2*n)-1`.

These are explicit contracts, not assertions that the calculations have been
proved. The Chapter 8 consumer combines them with the E.2.14 degree and
fixed-space identities and the H.4.4(3) bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.4.2 setup, printed p.380, and Proposition 8.2.3, printed pp.715–716.
-/

@[expose] public section
noncomputable section

namespace Representation.HermitianTensorThree.ParabolicTorus
open ImageOuter BinaryOffender
variable (n : ℕ) [NeZero n]

/-- The original binary automorphism group of the descended space. -/
abbrev BinaryAut := Space n ≃ₗ[ZMod 2] Space n

/-- The point stabilizer's image under the actual descended action. -/
def pointParabolicImage : Subgroup (BinaryAut n) :=
  (coverPointParabolic n).map (binaryActionHom n)

/-- The plane stabilizer's image under the actual descended action. -/
def planeParabolicImage : Subgroup (BinaryAut n) :=
  (coverPlaneParabolic n).map (binaryActionHom n)

/-- Compatibility with the previously marked parabolic and image equivalence. -/
theorem pointParabolicImage_eq :
    pointParabolicImage n = (pointParabolic n).map
      ((binaryImage n).subtype.comp (binaryImageEquiv n).toMonoidHom) := by
  simp only [pointParabolicImage, pointParabolic, Subgroup.map_map]
  congr 1

/-- The plane image uses the same literal image equivalence as the source model. -/
theorem planeParabolicImage_eq :
    planeParabolicImage n = (planeParabolic n).map
      ((binaryImage n).subtype.comp (binaryImageEquiv n).toMonoidHom) := by
  simp only [planeParabolicImage, planeParabolic, Subgroup.map_map]
  congr 1

/-- Preservation of an actual maximal parabolic, allowing both natural types. -/
def PreservesMaximalParabolic (e : BinaryAut n) : Prop :=
  ∃ c : Cover n,
    e ∈ Subgroup.normalizer
      ((pointParabolicImage n).map (MulAut.conj (binaryActionHom n c)).toMonoidHom :
        Set (BinaryAut n)) ∨
    e ∈ Subgroup.normalizer
      ((planeParabolicImage n).map (MulAut.conj (binaryActionHom n c)).toMonoidHom :
        Set (BinaryAut n))

/-- Linearity over the actual fixed field, with the original action unchanged. -/
def IsFixedFieldLinear (e : BinaryAut n) : Prop :=
  ∀ (c : F n) (v : Space n), e (c • v) = c • e v

/-- The fixed-space estimate must allow composite odd order and a nonfaithful
action of the cyclic group on the coefficient field. -/
def LargeOddFixedSpaceLinearity : Prop :=
  ∀ (M : Subgroup (BinaryAut n)) (x : M),
    x.val ∈ binaryNormalizer n → Odd (orderOf x) →
    3 * n < Module.finrank (ZMod 2)
      (fixedSpace (overgroupAction n M) (Subgroup.zpowers x)) →
    IsFixedFieldLinear n x.val ∧
      n ∣ Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n M) (Subgroup.zpowers x))

/-- The odd exponent of a parabolic in the full fixed-field linear normalizer.
The exponent is `2^(4*n)-1`, including nonsplit two-dimensional Levi tori. -/
def OddLinearParabolicExponent : Prop :=
  ∀ e : BinaryAut n, e ∈ binaryNormalizer n → Odd (orderOf e) →
    IsFixedFieldLinear n e → PreservesMaximalParabolic n e →
      orderOf e ∣ 2 ^ (4 * n) - 1

end Representation.HermitianTensorThree.ParabolicTorus
