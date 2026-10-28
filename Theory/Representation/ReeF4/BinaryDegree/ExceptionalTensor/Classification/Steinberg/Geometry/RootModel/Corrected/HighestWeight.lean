module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Characters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters

/-!
# The concrete left-character boundary for highest weights

A left torus eigenvector with integral coordinates `a` has eigenvalue `t^(a i)`
on the existing representation coroot word. Thus the source's nonnegative
highest-weight coefficients agree with left character coordinates. This module
compares actual eigenvalue equations, preserving the existing positive root
labels and highest-weight predicates; it asserts no existence of modules.
Source: GLS3 1.14 and Steinberg, Endomorphisms, Section 13.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance highestWeightTorusGroup : AlgebraicGroup (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup

/-- A left torus eigenvector has the positive eigenvalue on the literal representation coroot. -/
theorem leftEigenvector_representationCoroot (B : AlgebraicFactor F)
    (a : Fin 4 → ℤ) (v : B.Space)
    (hv : ∀ s : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety,
      (B.action.action ((F4Chevalley.splitTorus (k := F)).includePoint s) :
        Module.End F B.Space) v = (leftCharacter a).pointCharacter s • v)
    (i : Fin 4) (t : Fˣ) :
    (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ a i • v := by
  let q : Variety.Point (KMult F) := (dPointEquiv 1).symm (fun _ => t)
  have hq : dPointEquiv 1 q 0 = t := by simp [q]
  have h := hv ((F4Chevalley.splitTorusSimpleCoroot i).onPoints q)
  change (B.action.action ((F4Chevalley.splitTorus (k := F)).inclusion.onPoints
    ((F4Chevalley.splitTorusSimpleCoroot i).onPoints q)) : Module.End F B.Space) v = _ at h
  rw [splitTorusSimpleCoroot_eq_algebraicCoroot, leftCharacter_representationCoroot,
    hq] at h
  exact h

/-- A nonzero left eigenvector fixed by the actual positive roots has the existing
highest weight, with exactly the source's nonnegative coefficients. -/
theorem hasHighestWeight_of_leftEigenvector (B : AlgebraicFactor F)
    (a : Weight) (v : B.Space) (hne : v ≠ 0)
    (hpos : ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v)
    (hv : ∀ s : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety,
      (B.action.action ((F4Chevalley.splitTorus (k := F)).includePoint s) :
        Module.End F B.Space) v = (leftCharacter (fun i => (a i : ℤ))).pointCharacter s • v) :
    HasHighestWeight B a := by
  refine ⟨v, hne, hpos, ?_⟩
  intro i t
  simpa only [zpow_natCast] using leftEigenvector_representationCoroot B _ v hv i t

/-- The basic-weight specialization uses the existing basic predicate. -/
theorem hasBasicHighestWeight_of_leftEigenvector (B : AlgebraicFactor F)
    (a : BasicWeight) (v : B.Space) (hne : v ≠ 0)
    (hpos : ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v)
    (hv : ∀ s : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety,
      (B.action.action ((F4Chevalley.splitTorus (k := F)).includePoint s) :
        Module.End F B.Space) v =
          (leftCharacter (fun i => (basicCoefficient a i : ℤ))).pointCharacter s • v) :
    HasBasicHighestWeight B a :=
  (hasHighestWeight_basic_iff B a).mp
    (hasHighestWeight_of_leftEigenvector B (basicCoefficient a) v hne hpos hv)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
