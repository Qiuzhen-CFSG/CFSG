module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.Coordinates

/-!
# D4 simple reflections on the actual torus

The supplied character equations determine the simple-reflection point maps.
Evaluating a fundamental weight shows that a simple reflection fixes a torus
point precisely when its root character has value one. The full character
lattice is used through `S.weight` and its actual coroot coordinates, without
splitting any isogeny.

These are local character consequences. Generation of an arbitrary stabilizer
by such reflections remains the separate `ReflectionGeneration` obligation.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 6.4(b) and 8.2(7).
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace ConnectedCentralizer.Normalizer
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Actual fundamental-weight coordinates separate torus points. -/
theorem torusPoint_ext (S : Geometry K) {t u : Variety.Point S.torus.carrierVariety}
    (h : ∀ a : Weight, (S.weight (Multiplicative.ofAdd a)).pointCharacter t =
      (S.weight (Multiplicative.ofAdd a)).pointCharacter u) : t = u := by
  apply (torusPointEval_bijective S.maximalTorus.1).injective
  apply MonoidHom.ext
  intro χ
  apply Units.ext
  obtain ⟨a, rfl⟩ := S.weight.surjective χ
  exact h a.toAdd

/-- The simple reflections in `TorusData` have the actual root/coroot point
formula. Equality of all character evaluations proves equality of points. -/
theorem simple_reflection_point (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n) (i : Fin 4)
    (t : Variety.Point S.torus.carrierVariety) :
    let := D.action
    rootReflection S (S.simpleRoot i).val • t =
      AmbientCount.TorusGeometry.simpleReflection S i t := by
  let := D.action
  apply torusPoint_ext S
  intro a
  rw [rootReflection, S.simpleRoot_index, D.reflection_weight,
    AmbientCount.TorusGeometry.simpleReflection_weight]

/-- A simple reflection fixes the torus point exactly when the actual simple
root has value one. The forward implication uses a fundamental weight, not a
claim that an arbitrary incoming isogeny splits. -/
theorem simple_reflection_fixed_iff (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n) (i : Fin 4)
    (t : Variety.Point S.torus.carrierVariety) :
    let := D.action
    rootReflection S (S.simpleRoot i).val • t = t ↔
      (S.roots.rootWeight (S.simpleRoot i).val).pointCharacter t = 1 := by
  let := D.action
  constructor
  · intro hfix
    let a : Weight := Pi.single i 1
    have h := D.reflection_weight i a t
    have hfix' : RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
        (typeDSimpleRootIndex 2 i) • t = t := by
      simpa only [rootReflection, S.simpleRoot_index] using hfix
    rw [hfix', AmbientCount.TorusGeometry.reflection_character] at h
    change (S.weight (Multiplicative.ofAdd a)).pointCharacter t =
      ((torusPointEval S.torus.carrierVariety t
        (S.weight (Multiplicative.ofAdd a) *
          S.roots.rootWeight (S.simpleRoot i).val ^ (-a i))) : k) at h
    rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val] at h
    have hχ : (torusPointEval S.torus.carrierVariety t
        (S.weight (Multiplicative.ofAdd a)) : k) ≠ 0 := Units.ne_zero _
    have hroot := mul_left_cancel₀ hχ (h.symm.trans (mul_one _).symm)
    have hr : torusPointEval S.torus.carrierVariety t
        (S.roots.rootWeight (S.simpleRoot i).val) = 1 := by
      simpa [a] using hroot
    exact congrArg Units.val hr
  · intro ha
    apply torusPoint_ext S
    intro a
    rw [rootReflection, S.simpleRoot_index, D.reflection_weight,
      AmbientCount.TorusGeometry.reflection_character]
    change ((torusPointEval S.torus.carrierVariety t
      (S.weight (Multiplicative.ofAdd a) *
        S.roots.rootWeight (S.simpleRoot i).val ^ (-a i))) : k) = _
    rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]
    change (S.weight (Multiplicative.ofAdd a)).pointCharacter t *
      (S.roots.rootWeight (S.simpleRoot i).val).pointCharacter t ^ (-a i) = _
    rw [ha, one_zpow, mul_one]

end ConnectedCentralizer.Normalizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
