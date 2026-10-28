module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.ShortA2
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.WeylTransport.RootTransport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Geometry

/-!
# Weyl translates of the exceptional F4 end-node highest vector

The actual normalizer word for each entry of the orbit table translates the
input highest vector into that full coroot weight space. Invertibility preserves
nonvanishing. For entry eight, the inverse word sends the two short simple roots
to positive roots, so the translated vector is also fixed by their root groups.
Both conjugation and positivity assertions used for fixation are proved in
`WeylTransport.RootTransport`.

The coroot-normalizer equation is the actual carrier identity proved in
`ZeroAndMiddle.Geometry`. It uses the positive-coroot convention
`n(t) * n(1)⁻¹`. Together these identities discharge every transport premise;
no multiplicity or highest-weight classification theorem is used.

Source: GLS3, Theorem 1.12.1 and Section 1.14, with Definition 2.8.1(b).
The resulting end-node bound is used on printed p.356 of Quasithin.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- Applying an actual carrier element preserves nonvanishing. -/
theorem action_ne_zero (B : AlgebraicFactor F)
    (g : Variety.Point (F4Chevalley.Carrier (k := F)))
    {v : B.Space} (hv : v ≠ 0) : (B.action.action g : Module.End F B.Space) v ≠ 0 := by
  intro he
  apply hv
  have h := congrArg (fun w => (B.action.action g⁻¹ : Module.End F B.Space) w) he
  simpa only [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, inv_mul_cancel,
    map_one, Units.val_one, Module.End.one_apply, map_zero] using h

/-- One actual normalizer translate has the reflected integral coroot weight. -/
theorem n_mem_reflectWeight (B : AlgebraicFactor F)
    (i : Fin 4) {μ : Weight} {v : B.Space} (hv : v ∈ corootWeightSpace B μ) :
    (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
      Module.End F B.Space) v ∈ corootWeightSpace B (reflectWeight i μ) := by
  have hv' := (mem_corootWeightSpace B μ v).mp hv
  apply (mem_corootWeightSpace B _ _).mpr
  intro j t
  have he := congrArg (fun g => (B.action.action g : Module.End F B.Space) v) (ZeroAndMiddle.coroot_n_commute i j t)
  simp only [map_mul, Units.val_mul, Module.End.mul_apply, hv', map_smul,
    smul_smul] at he
  rw [he]
  congr 1
  rw [Units.val_zpow_eq_zpow_val, ← zpow_mul, ← zpow_add₀ t.ne_zero]
  congr 1
  simp only [reflectWeight]
  ring

/-- A left-to-right normalizer word realizes the entire reflected weight tuple. -/
theorem normalizerWord_mem_weight (B : AlgebraicFactor F)
    (w : List (Fin 4)) {μ : Weight} {v : B.Space} (hv : v ∈ corootWeightSpace B μ) :
    (B.action.action (normalizerWord w) : Module.End F B.Space) v ∈
      corootWeightSpace B (w.foldl (fun ν i => reflectWeight i ν) μ) := by
  induction w generalizing μ v with
  | nil => simpa only [normalizerWord, map_one, Units.val_one, Module.End.one_apply,
      List.foldl_nil] using hv
  | cons i w ih =>
    simpa only [normalizerWord, map_mul, Units.val_mul, Module.End.mul_apply,
      List.foldl_cons] using ih (n_mem_reflectWeight B i hv)

/-- The actual normalizer word in table entry `i` produces a nonzero vector of
its tabulated weight. -/
theorem endOrbitWeight_occurs
    (B : AlgebraicFactor F)
    (h : B.HasBasicHighestWeight (0, 1)) (i : Fin 24) :
    corootWeightSpace B (endOrbitWeight i) ≠ ⊥ := by
  obtain ⟨v, hv⟩ := h
  have hm : v ∈ corootWeightSpace B endHighestWeight := by
    rw [endHighestWeight_eq_basicCoefficient]
    exact basicHighestWeightVector_mem_corootWeightSpace hv
  have hmv := normalizerWord_mem_weight B (endOrbitWord i) hm
  rw [endOrbitWord_spec] at hmv
  intro hz
  rw [hz, Submodule.mem_bot] at hmv
  exact action_ne_zero B (normalizerWord (endOrbitWord i)) hv.1 hmv

/-- A root subgroup fixes the translate whenever its inverse image fixes the
original vector. The conjugation equation is proved in the actual carrier. -/
theorem normalizerWord_fixed [CharP F 2] (B : AlgebraicFactor F)
    (w : List (Fin 4)) (r : F4Chevalley.Root) (v : B.Space)
    (hfix : ∀ t : F, (B.action.action (algebraicRootElement (inverseRootWord w r) t) :
      Module.End F B.Space) v = v) (t : F) :
    (B.action.action (algebraicRootElement r t) : Module.End F B.Space)
      ((B.action.action (normalizerWord w) : Module.End F B.Space) v) =
        (B.action.action (normalizerWord w) : Module.End F B.Space) v := by
  have h := congrArg (fun g => (B.action.action g : Module.End F B.Space) v)
    (root_normalizerWord_commute w r t)
  simpa only [map_mul, Units.val_mul, Module.End.mul_apply, hfix] using h

/-- Entry eight yields the short A2 highest vector from the input highest
vector. The full F4 weight and both positive-root fixation equations are proved. -/
theorem hasShortA2HighestVector [CharP F 2]
    (B : AlgebraicFactor F)
    (h : B.HasBasicHighestWeight (0, 1)) : HasShortA2HighestVector B := by
  obtain ⟨v, hv⟩ := h
  refine ⟨(B.action.action (normalizerWord (endOrbitWord 8)) : Module.End F B.Space) v,
    action_ne_zero B _ hv.1, ?_, ?_, ?_⟩
  · have hm : v ∈ corootWeightSpace B endHighestWeight := by
      rw [endHighestWeight_eq_basicCoefficient]
      exact basicHighestWeightVector_mem_corootWeightSpace hv
    have hmv := normalizerWord_mem_weight B (endOrbitWord 8) hm
    simpa only [endOrbitWord_spec, endOrbitWeight_eight] using hmv
  · exact normalizerWord_fixed B (endOrbitWord 8) (typeF4SimpleRootIndex 2) v
      (hv.2.1 _ inverseRootWord_eight_two_isPos)
  · exact normalizerWord_fixed B (endOrbitWord 8) (typeF4SimpleRootIndex 3) v
      (hv.2.1 _ inverseRootWord_eight_three_isPos)

end ReeF4.BinaryDegree.ExceptionalTensor.EndNode
