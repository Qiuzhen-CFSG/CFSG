module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.Presentation
public import Theory.GroupTheory.CentralThreeInvertedPlane
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Cubic lifts of the six marked unitary roots

The short-root inverter and the long-root inverter are actual determinant-one
unitary matrices. Commutators of their lifts with root lifts give cubic lifts
of all six coordinate generators. Centrality makes this construction independent
of the preimages chosen. The short-root and mixed commuting pairs also give two
actual central cubic elements, without an exponent assumption on the kernel.

This does not assert that these two elements control every lifted relation.
That is the remaining exceptional-multiplier calculation for Aschbacher--Smith
I.1.4(5), printed p.408; GLS3 §6.1.
-/
@[expose] public noncomputable section
open scoped commutatorElement
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts

variable {E : Type*} [Group E]

/-- Cubic lifts of the actual six marked roots; no inter-root relation is assumed. -/
structure CubicRootLifts (f : E →* S) where
  gen : Fin 6 → E
  projects : ∀ r, f (gen r) = root r
  cubes : ∀ r, gen r ^ 3 = 1

/-- The normalized commutator, formed with the marked torus inverter. -/
def normalizedRoot (f : E →* S) (hf : Function.Surjective f) (r : Fin 6) : E :=
  ⁅(hf (torus (inverterIndex r))).choose, (hf (root r)).choose⁆

theorem normalizedRoot_projects_cube (f : E →* S) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (r : Fin 6) :
    f (normalizedRoot f hf r) = root r ∧ normalizedRoot f hf r ^ 3 = 1 := by
  have h := f.inverted_cubic_commutator_lift hk (hf (root r)).choose
    (hf (torus (inverterIndex r))).choose
    (by rw [(hf (root r)).choose_spec]; exact root_cube r)
    (by rw [(hf (root r)).choose_spec, (hf (torus (inverterIndex r))).choose_spec]
        exact torus_inverts r)
  exact ⟨h.1.trans (hf (root r)).choose_spec, h.2⟩

/-- Both arbitrary choices disappear from the normalized commutator. -/
theorem normalizedRoot_eq_commutator (f : E →* S) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (r : Fin 6) (a b : E)
    (ha : f a = torus (inverterIndex r)) (hb : f b = root r) :
    normalizedRoot f hf r = ⁅a,b⁆ :=
  CentralExtension.commutator_eq_of_image_eq f hk
    ((hf _).choose_spec.trans ha.symm) ((hf _).choose_spec.trans hb.symm)

/-- All six cubic lifts are constructed for every surjective central extension. -/
def normalizedRoots (f : E →* S) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : CubicRootLifts f where
  gen := normalizedRoot f hf
  projects r := (normalizedRoot_projects_cube f hf hk r).1
  cubes r := (normalizedRoot_projects_cube f hf hk r).2

private theorem central_commutator_cube (x y : E)
    (hz : ⁅x,y⁆ ∈ Subgroup.center E) (hx : x ^ 3 = 1) : ⁅x,y⁆ ^ 3 = 1 := by
  have hc (t : E) : t * ⁅x,y⁆ * t⁻¹ = ⁅x,y⁆ := by
    rw [Subgroup.mem_center_iff.mp hz t, mul_inv_cancel_right]
  have hp (n : ℕ) : ⁅x ^ n,y⁆ = ⁅x,y⁆ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, hc, ih, pow_succ']
  rw [← hp, hx, commutatorElement_one_left]

namespace CubicRootLifts
variable {f : E →* S} (L : CubicRootLifts f)

/-- The commutator inside the first short-root plane. -/
def shortDefect : E := ⁅L.gen 0, L.gen 1⁆
/-- The mixed pair which already commutes in the coordinate unitary group. -/
def mixedDefect : E := ⁅L.gen 0, L.gen 3⁆

theorem shortDefect_mem : L.shortDefect ∈ f.ker := by
  change f ⁅L.gen 0, L.gen 1⁆ = 1
  rw [map_commutatorElement, L.projects, L.projects]
  apply Commute.commutator_eq
  change root 0 * root 1 = root 1 * root 0
  have h := root_swap 0 1 (by decide)
  simpa [swapTail] using h.symm

theorem mixedDefect_mem : L.mixedDefect ∈ f.ker := by
  change f ⁅L.gen 0, L.gen 3⁆ = 1
  rw [map_commutatorElement, L.projects, L.projects]
  apply Commute.commutator_eq
  change root 0 * root 3 = root 3 * root 0
  have h := root_swap 0 3 (by decide)
  simpa [swapTail] using h.symm

theorem shortDefect_cube (hk : f.ker ≤ Subgroup.center E) : L.shortDefect ^ 3 = 1 :=
  central_commutator_cube _ _ (hk L.shortDefect_mem) (L.cubes 0)

theorem mixedDefect_cube (hk : f.ker ≤ Subgroup.center E) : L.mixedDefect ^ 3 = 1 :=
  central_commutator_cube _ _ (hk L.mixedDefect_mem) (L.cubes 0)

end CubicRootLifts
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
