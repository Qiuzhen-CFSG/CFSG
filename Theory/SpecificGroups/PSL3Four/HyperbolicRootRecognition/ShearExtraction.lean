module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.Reflections

/-!
# Extracting the two nonsingular binary shears

For an additive involution, its displacement lies in its fixed space.
If that fixed space is exactly one of the two quotient planes, the other
coordinate is unchanged and the displacement is a nonsingular two-by-two
binary map. Its two columns give the parameters used by the finite criterion.
Source: the natural-module reflections in Aschbacher, 45.3, pp.242–243.
-/

public section
namespace Theory.GroupTheory.HyperbolicRecognition

private theorem map_binary_pair (f : Central →+ Central) (v : Central) :
    f v = planeMap (f cz,f cu) v := by
  rcases v with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · change f 0 = planeMap (f cz,f cu) 0
    rw [map_zero,planeMap_zero]
  · change f cu = planeMap (f cz,f cu) cu
    simp [planeMap,cu]
  · change f cz = planeMap (f cz,f cu) cz
    simp [planeMap,cz]
  · change f (cz+cu) = planeMap (f cz,f cu) (cz+cu)
    rw [map_add]
    apply Prod.ext <;> simp [planeMap,cz,cu]

/-- The first exact fixed plane determines the actual nonsingular shear. -/
theorem exists_first_shear (f : Vector →+ Vector) (hf : Function.Involutive f)
    (hfix : ∀ v : Vector, f v = v ↔ v.2 = 0) :
    ∃ P : Frame, Nonsingular P ∧ ∀ v, f v = reflectA P v := by
  let g : Central →+ Central := {
    toFun := fun v => (f (0,v)).1
    map_zero' := by change (f 0).1 = 0; rw [map_zero]; rfl
    map_add' := fun v w => by
      change (f ((0,v)+(0,w))).1 = _
      rw [map_add]
      rfl }
  let P : Frame := (g cz,g cu)
  have hs (v : Vector) : (f v).2 = v.2 := by
    have hh := (hfix (f v+v)).mp (by rw [map_add,hf]; exact add_comm _ _)
    change (f v).2 + v.2 = 0 at hh
    exact CharTwo.add_eq_zero.mp hh
  have hform (v : Vector) : f v = reflectA P v := by
    have hh : f v = f (v.1,0) + f (0,v.2) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    have hfirst : f (v.1,0) = (v.1,0) := (hfix _).mpr rfl
    apply Prod.ext
    · change (f v).1 = v.1 + planeMap P v.2
      rw [hh,hfirst]
      change v.1 + g v.2 = v.1 + planeMap P v.2
      rw [map_binary_pair g v.2]
    · exact hs v
  refine ⟨P,?_,hform⟩
  intro v hv
  apply (hfix ((0 : Central),v)).mp
  rw [hform]
  change (0 + planeMap P v,v) = (0,v)
  rw [hv,add_zero]

/-- The second exact fixed plane determines the other nonsingular shear. -/
theorem exists_second_shear (f : Vector →+ Vector) (hf : Function.Involutive f)
    (hfix : ∀ v : Vector, f v = v ↔ v.1 = 0) :
    ∃ P : Frame, Nonsingular P ∧ ∀ v, f v = reflectB P v := by
  let g : Central →+ Central := {
    toFun := fun v => (f (v,0)).2
    map_zero' := by change (f 0).2 = 0; rw [map_zero]; rfl
    map_add' := fun v w => by
      change (f ((v,0)+(w,0))).2 = _
      rw [map_add]
      rfl }
  let P : Frame := (g cz,g cu)
  have hs (v : Vector) : (f v).1 = v.1 := by
    have hh := (hfix (f v+v)).mp (by rw [map_add,hf]; exact add_comm _ _)
    change (f v).1 + v.1 = 0 at hh
    exact CharTwo.add_eq_zero.mp hh
  have hform (v : Vector) : f v = reflectB P v := by
    have hh : f v = f (v.1,0) + f (0,v.2) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    have hsecond : f (0,v.2) = (0,v.2) := (hfix _).mpr rfl
    apply Prod.ext
    · exact hs v
    · change (f v).2 = v.2 + planeMap P v.1
      rw [hh,hsecond]
      change g v.1 + v.2 = v.2 + planeMap P v.1
      rw [map_binary_pair g v.1,add_comm]
  refine ⟨P,?_,hform⟩
  intro v hv
  apply (hfix (v,(0 : Central))).mp
  rw [hform]
  change (v,0 + planeMap P v) = (v,0)
  rw [hv,add_zero]

end Theory.GroupTheory.HyperbolicRecognition
