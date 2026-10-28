module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.Inputs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Action.Hom

/-!
# Descent of the actual torus-normalizer action

Conjugation gives an action of the actual normalizer on the chosen torus.
Its kernel is the actual centralizer. A surjective normalizer map to the D4
Weyl group whose kernel centralizes the torus therefore descends this action.
Actual lifts of simple reflections give the prescribed point formula, and
normalizer control of ambient fusion gives precisely `WeylGeometry`.

`NormalizerRealization` and `NormalizerControlsFusion` remain geometric proof
obligations. This module proves their conditional assembly; it does not assert
their existence from `Geometry`. In particular every orbit move constructed
here comes from an ambient conjugator, not only a lattice automorphism.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, §§6.1--6.4 and the
proof of 14.8(a). The conjugation action is `g * t * g⁻¹`; the reflection
formula uses the actual root and coroot of `Coordinates.simpleReflection`,
which already incorporates the project's inverse-conjugation root convention.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The normalizer of the actual chosen torus in the ambient point group. -/
abbrev TorusNormalizer (S : Geometry K) :=
  Subgroup.normalizer (S.torus.toSubgroup : Set (Variety.Point K))

/-- Conjugation on actual torus points, transported along their subgroup equivalence. -/
def normalizerPerm (S : Geometry K) :
    TorusNormalizer S →* Equiv.Perm (Variety.Point S.torus.carrierVariety) :=
  S.torus.pointEquiv.symm.permCongrHom.toMonoidHom.comp
    ((MulAut.toPerm _).comp S.torus.toSubgroup.normalizerMonoidHom)

/-- The transported permutation is literal ambient conjugation. -/
theorem normalizerPerm_include (S : Geometry K) (g : TorusNormalizer S)
    (t : Variety.Point S.torus.carrierVariety) :
    S.torus.includePoint (normalizerPerm S g t) =
      (g : Variety.Point K) * S.torus.includePoint t * (g : Variety.Point K)⁻¹ := by
  change (S.torus.pointEquiv (S.torus.pointEquiv.symm _)).val = _
  rw [S.torus.pointEquiv.apply_symm_apply]
  rfl

/-- Exactly the elements centralizing the torus act trivially on its points. -/
theorem normalizerPerm_ker (S : Geometry K) :
    (normalizerPerm S).ker =
      (Subgroup.centralizer (S.torus.toSubgroup : Set (Variety.Point K))).subgroupOf
        (TorusNormalizer S) := by
  ext g
  change normalizerPerm S g = 1 ↔ _
  rw [Equiv.Perm.ext_iff]
  constructor
  · intro hg
    change (g : Variety.Point K) ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let t := S.torus.pointEquiv.symm ⟨x, hx⟩
    have h := congrArg S.torus.includePoint (hg t)
    rw [normalizerPerm_include] at h
    have ht : S.torus.includePoint t = x := by
      exact congrArg Subtype.val (S.torus.pointEquiv.apply_symm_apply ⟨x, hx⟩)
    rw [ht] at h
    exact ((mul_inv_eq_iff_eq_mul).mp h).symm
  · intro hg t
    apply S.torus.inclusion_injective
    change S.torus.includePoint (normalizerPerm S g t) = S.torus.includePoint t
    rw [normalizerPerm_include]
    have h := (Subgroup.mem_centralizer_iff.mp hg)
      (S.torus.includePoint t) (S.torus.pointEquiv t).property
    change S.torus.includePoint t * (g : Variety.Point K) =
      (g : Variety.Point K) * S.torus.includePoint t at h
    rw [← h, mul_inv_cancel_right]

/-- The normalizer-to-Weyl comparison and actual simple-reflection lifts.
The kernel condition is the precise condition needed for descent; proving that
this kernel equals the torus is unnecessary for the present consumer.
No fusion conclusion or point action is a field of this structure. -/
structure NormalizerRealization (S : Geometry K) where
  toWeyl : TorusNormalizer S →* Weyl
  surjective : Function.Surjective toWeyl
  kernel_centralizes : toWeyl.ker ≤
    (Subgroup.centralizer (S.torus.toSubgroup : Set (Variety.Point K))).subgroupOf
      (TorusNormalizer S)
  simple_lift : ∀ i : Fin 4, ∃ g : TorusNormalizer S,
    toWeyl g = RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
      (typeDSimpleRootIndex 2 i) ∧
    ∀ t : Variety.Point S.torus.carrierVariety,
      (g : Variety.Point K) * S.torus.includePoint t * (g : Variety.Point K)⁻¹ =
        S.torus.includePoint (simpleReflection S i t)

/-- Descend the actual normalizer permutations through the surjective Weyl map. -/
def NormalizerRealization.perm {S : Geometry K} (R : NormalizerRealization S) :
    Weyl →* Equiv.Perm (Variety.Point S.torus.carrierVariety) :=
  R.toWeyl.liftOfSurjective R.surjective
    ⟨normalizerPerm S, by rw [normalizerPerm_ker]; exact R.kernel_centralizes⟩

/-- Descent preserves the permutation supplied by every ambient representative. -/
theorem NormalizerRealization.perm_toWeyl {S : Geometry K}
    (R : NormalizerRealization S) (g : TorusNormalizer S) :
    R.perm (R.toWeyl g) = normalizerPerm S g := by
  apply MonoidHom.liftOfRightInverse_comp_apply

/-- The descended action on the actual torus. -/
abbrev NormalizerRealization.action {S : Geometry K} (R : NormalizerRealization S) :
    MulAction Weyl (Variety.Point S.torus.carrierVariety) :=
  MulAction.compHom _ R.perm

/-- Every represented Weyl action is the same actual ambient conjugation. -/
theorem NormalizerRealization.smul_include {S : Geometry K}
    (R : NormalizerRealization S) (g : TorusNormalizer S)
    (t : Variety.Point S.torus.carrierVariety) :
    letI := R.action
    S.torus.includePoint (R.toWeyl g • t) =
      (g : Variety.Point K) * S.torus.includePoint t * (g : Variety.Point K)⁻¹ := by
  change S.torus.includePoint (R.perm (R.toWeyl g) t) = _
  rw [R.perm_toWeyl, normalizerPerm_include]

/-- The specified geometric reflection lifts give the root--coroot point formula. -/
theorem NormalizerRealization.reflection_point {S : Geometry K}
    (R : NormalizerRealization S) (i : Fin 4)
    (t : Variety.Point S.torus.carrierVariety) :
    letI := R.action
    (RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i)) • t =
      simpleReflection S i t := by
  let := R.action
  obtain ⟨g, hg, ht⟩ := R.simple_lift i
  apply S.torus.inclusion_injective
  change S.torus.includePoint
    ((RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i)) • t) = _
  rw [← hg, R.smul_include]
  exact ht t

/-- Weyl orbits are exactly orbits under actual torus-normalizer conjugation. -/
theorem NormalizerRealization.orbit_iff_normalizer {S : Geometry K}
    (R : NormalizerRealization S) (t u : Variety.Point S.torus.carrierVariety) :
    letI := R.action
    (∃ w : Weyl, w • t = u) ↔ ∃ g : TorusNormalizer S,
      (g : Variety.Point K) * S.torus.includePoint t * (g : Variety.Point K)⁻¹ =
        S.torus.includePoint u := by
  let := R.action
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨g, rfl⟩ := R.surjective w
    exact ⟨g, (R.smul_include g t).symm.trans (congrArg S.torus.includePoint hw)⟩
  · rintro ⟨g, hg⟩
    refine ⟨R.toWeyl g, S.torus.inclusion_injective ?_⟩
    exact (R.smul_include g t).trans hg

/-- Each Weyl orbit is contained in one ambient conjugacy class. -/
theorem NormalizerRealization.isConj_of_orbit {S : Geometry K}
    (R : NormalizerRealization S) (t u : Variety.Point S.torus.carrierVariety)
    (h : letI := R.action; ∃ w : Weyl, w • t = u) :
    IsConj (S.torus.includePoint t) (S.torus.includePoint u) := by
  obtain ⟨g, hg⟩ := (R.orbit_iff_normalizer t u).mp h
  exact isConj_iff.mpr ⟨g, hg⟩

/-- Ambient fusion of torus points is controlled by the actual normalizer.
This is independent of a Weyl-group identification and remains to be proved. -/
def NormalizerControlsFusion (S : Geometry K) : Prop :=
  ∀ t u : Variety.Point S.torus.carrierVariety,
    IsConj (S.torus.includePoint t) (S.torus.includePoint u) →
    ∃ g : TorusNormalizer S,
      (g : Variety.Point K) * S.torus.includePoint t * (g : Variety.Point K)⁻¹ =
        S.torus.includePoint u

/-- Conditional assembly from the normalizer comparison and its control of
ambient fusion. Both geometric premises must be discharged for existence. -/
def NormalizerRealization.weylGeometry {S : Geometry K}
    (R : NormalizerRealization S) (hfusion : NormalizerControlsFusion S) :
    WeylGeometry S where
  action := R.action
  reflection_point := R.reflection_point
  conjugate_iff := by
    intro t u
    constructor
    · intro h
      exact (R.orbit_iff_normalizer t u).mpr (hfusion t u h)
    · exact R.isConj_of_orbit t u

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
