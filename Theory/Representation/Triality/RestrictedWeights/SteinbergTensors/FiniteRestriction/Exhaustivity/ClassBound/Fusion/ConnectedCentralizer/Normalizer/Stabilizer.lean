module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Characters
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Stabilizer.Lattice
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Stabilizer.Factorizations
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels

/-!
# Displacement weights and the actual D4 torus stabilizer

The based root pairing identifies every actual root character with its
integral simple-coroot coordinates. A Weyl element fixing a torus point
annihilates the displacement of every weight under its integral action.
Thus a root whose double is a displacement has value one: a field of
characteristic two has no nontrivial square root of one.

The checked D4 lattice factorizations express each Weyl element as a product
of reflections whose doubled root weights are displacements. The final
theorem applies them to the integral representation constructed from the
actual torus action, proving `ReflectionGeneration` for every torus point.
In particular, it applies to the odd-order points in the centralizer argument.
No centralizer connectedness, normalizer representatives or splitting of an
isogeny is used.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 4.2, 4.10', 5.3, 6.4(b),
8.2(6)--(7) and 8.3(c).
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight
namespace ConnectedCentralizer.Normalizer.Stabilizer

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
/-- Every actual root character has the coordinates of its specified D4 root.
This extends the simple-root comparison to all roots without a choice of lifts. -/
theorem actual_rootWeight (S : Geometry K) (r : S.roots.Root) :
    S.roots.rootWeight r = S.weight (Multiplicative.ofAdd (rootWeight (S.rootIndex r))) := by
  apply AmbientCount.TorusGeometry.character_ext S
  intro i
  rw [S.realized.weightPairing_rootWeight, S.weight_coordinate]
  apply Int.cast_injective (α := ℝ)
  rw [S.based.1, S.simpleRoot_index]
  exact ((typeDRootPairing 2).algebraMap_pairingIn ℤ _ _).symm

/-- Evaluation at a fixed torus point is invariant under the integral Weyl
action. Inversion accounts for the contravariance of character pullback. -/
theorem evaluation_fixed (S : Geometry K) {n : ℕ} (D : AmbientCount.TorusData S n)
    (ρ : AmbientCount.WeightRepresentation) (hρ : AmbientCount.ReflectionCompatible ρ)
    (t : Variety.Point S.torus.carrierVariety) (w : AmbientCount.Weyl)
    (hw : letI := D.action; w ∈ MulAction.stabilizer AmbientCount.Weyl t)
    (a : Weight) :
    AmbientCount.weightEvaluation S t (ρ w a) = AmbientCount.weightEvaluation S t a := by
  let := D.action
  have hfix : w⁻¹ • t = t := (MulAction.stabilizer AmbientCount.Weyl t).inv_mem hw
  have h := AmbientCount.weightEvaluation_weyl D ρ hρ w⁻¹ t a
  rw [inv_inv, hfix] at h
  exact h.symm

/-- A doubled root in the displacement lattice evaluates to one at a fixed
torus point. Squaring injectivity removes the factor two. -/
theorem rootValue_one_of_doubled_image (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n) (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ)
    (t : Variety.Point S.torus.carrierVariety) (w : AmbientCount.Weyl)
    (hw : letI := D.action; w ∈ MulAction.stabilizer AmbientCount.Weyl t)
    (r : S.roots.Root) (a : Weight)
    (ha : ρ w a - a = (2 : ℤ) • rootWeight (S.rootIndex r)) :
    (S.roots.rootWeight r).pointCharacter t = 1 := by
  have hz : AmbientCount.weightEvaluation S t
      ((2 : ℤ) • rootWeight (S.rootIndex r)) = 0 := by
    rw [← ha, map_sub, evaluation_fixed S D ρ hρ t w hw, sub_self]
  rw [two_smul, map_add] at hz
  have hsq := congrArg (fun x : Additive kˣ => (x.toMul : k)) hz
  change (↑((AmbientCount.weightEvaluation S t (rootWeight (S.rootIndex r))).toMul) : k) *
    ↑((AmbientCount.weightEvaluation S t (rootWeight (S.rootIndex r))).toMul) = 1 at hsq
  rw [← pow_two] at hsq
  rw [AmbientCount.weightEvaluation_apply, ← actual_rootWeight] at hsq
  apply CharTwo.sq_injective
  simpa only [one_pow] using hsq

/-- Transfer the finite D4 displacement factorizations to the actual torus.
The lattice existence premise is separate from this character argument. -/
theorem reflectionGeneration_of_doubledRootFactorizations (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n) (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ)
    (hfactor : ∀ w, DoubledRootFactorization ρ w)
    (t : Variety.Point S.torus.carrierVariety) : ReflectionGeneration D t := by
  let := D.action
  intro w hw
  obtain ⟨l, hl, hroots⟩ := hfactor w
  rw [← hl]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  obtain ⟨a, ha⟩ := hroots r hr
  apply Subgroup.subset_closure
  refine ⟨S.rootIndex.symm r, ?_, ?_⟩
  · apply rootValue_one_of_doubled_image S D ρ hρ t w hw (S.rootIndex.symm r) a
    simpa only [Equiv.apply_symm_apply] using ha
  · simp only [rootReflection, Equiv.apply_symm_apply]

/-- The stabilizer of any actual torus point is contained in the subgroup
generated by root reflections whose actual root characters have value one.
Characteristic two suffices; the point need not have finite order. -/
theorem reflectionGeneration (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (t : Variety.Point S.torus.carrierVariety) : ReflectionGeneration D t := by
  exact reflectionGeneration_of_doubledRootFactorizations S D
    (AmbientCount.torusWeightRepresentation D)
    (AmbientCount.torusWeightRepresentation_compatible D)
    (doubledRootFactorization _ (AmbientCount.torusWeightRepresentation_compatible D)) t

/-- The odd-order specialization used by the centralizing-normalizer proof. -/
theorem reflectionGeneration_of_odd_order (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (t : Variety.Point S.torus.carrierVariety)
    (_ht : ¬ 2 ∣ orderOf (S.torus.includePoint t)) : ReflectionGeneration D t :=
  reflectionGeneration S D t

end ConnectedCentralizer.Normalizer.Stabilizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
