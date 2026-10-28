module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.Model
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Normalized lifts into every perfect central cover of the literal centralizer

Commutators are unchanged when either argument is multiplied by an element
of the central kernel. Thus the two commutator words defining the local
generators give lifts satisfying both normalization identities. Each of the
seven local relations evaluates into the central kernel, so all sixteen
presentation relations hold. The resulting map is surjective when the
extension is perfect, and its composite is the literal local projection.

Source: the free central-extension method of Aschbacher–Smith I.1.1, with
the concrete ATLAS J2G1-p100B0 relations checked in `Model.lean`.
-/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation
open Subgroup PerfectCentralCovering
open scoped commutatorElement

private theorem commutator_mul_center {G : Type*} [Group G] (a b x y : G)
    (ha : a ∈ center G) (hb : b ∈ center G) : ⁅a * x, b * y⁆ = ⁅x, y⁆ := by
  have ca (z : G) : Commute a z := (mem_center_iff.mp ha z).symm
  have cb (z : G) : Commute b z := (mem_center_iff.mp hb z).symm
  rw [commutatorElement_mul_left_eq_conj_mul, (ca (b * y)).commutator_eq]
  simp only [mul_one, (ca ⁅x, b * y⁆).eq, mul_inv_cancel_right]
  rw [commutatorElement_mul_right_eq_mul_conj, (cb x).symm.commutator_eq]
  simp only [one_mul, (cb ⁅x, y⁆).eq, mul_inv_cancel_right]

private theorem commutator_eq_of_map_eq {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hk : f.ker ≤ center G) {a b x y : G}
    (ha : f a = f x) (hb : f b = f y) : ⁅a, b⁆ = ⁅x, y⁆ := by
  have ca : a * x⁻¹ ∈ center G := hk (by simp [MonoidHom.mem_ker, ha])
  have cb : b * y⁻¹ ∈ center G := hk (by simp [MonoidHom.mem_ker, hb])
  simpa only [inv_mul_cancel_right] using
    commutator_mul_center (a * x⁻¹) (b * y⁻¹) x y ca cb

/-- Normalization depends only on the images of the two arguments in a central quotient. -/
theorem normalize_eq_of_map_eq {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hk : f.ker ≤ center G) {a b x y : G}
    (ha : f a = f x) (hb : f b = f y) (i : Bool) :
    normalize a b i = normalize x y i := by
  apply commutator_eq_of_map_eq f hk
  · simp only [map_leftWord, ha, hb]
  · simp only [map_rightWord, ha, hb]

variable {E : Type*} [Group E] (f : E →* Local) (hf : Function.Surjective f)

noncomputable def rawLift (i : Bool) : E := Classical.choose (hf (localGenerator i))

@[simp] theorem map_rawLift (i : Bool) : f (rawLift f hf i) = localGenerator i :=
  Classical.choose_spec (hf (localGenerator i))

noncomputable def liftGenerator (i : Bool) : E :=
  normalize (rawLift f hf false) (rawLift f hf true) i

@[simp] theorem map_liftGenerator (i : Bool) : f (liftGenerator f hf i) = localGenerator i := by
  rw [liftGenerator, map_normalize, map_rawLift, map_rawLift, local_normalize]

theorem liftGenerator_normalize (hk : f.ker ≤ center E) (i : Bool) :
    normalize (liftGenerator f hf false) (liftGenerator f hf true) i = liftGenerator f hf i :=
  normalize_eq_of_map_eq f hk (by simp) (by simp) i

theorem liftGenerator_baseValue_central (hk : f.ker ≤ center E) (i : Fin 7) :
    baseValue (liftGenerator f hf false) (liftGenerator f hf true) i ∈ center E := by
  apply hk
  simp only [MonoidHom.mem_ker, map_baseValue, map_liftGenerator, local_baseValue]

theorem liftGenerator_relations (hk : f.ker ≤ center E) (i : Fin 16) :
    relationValue (liftGenerator f hf false) (liftGenerator f hf true) i = 1 := by
  have hc (j : Fin 7) (x : E) :
      ⁅baseValue (liftGenerator f hf false) (liftGenerator f hf true) j, x⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      ((mem_center_iff.mp (liftGenerator_baseValue_central f hf hk j) x).symm)
  fin_cases i <;> simp [relationValue, hc, liftGenerator_normalize f hf hk]

/-- The explicit presentation maps to every central extension of the literal local group. -/
noncomputable def coverMap (hk : f.ker ≤ center E) : Presentation →* E :=
  evaluate (liftGenerator f hf false) (liftGenerator f hf true) (liftGenerator_relations f hf hk)

@[simp] theorem coverMap_generator (hk : f.ker ≤ center E) (i : Bool) :
    coverMap f hf hk (generator i) = liftGenerator f hf i := by
  cases i <;> exact evaluate_generator _ _ _ _

/-- The comparison preserves the actual quotient map and the original marked generators. -/
theorem coverMap_fac (hk : f.ker ≤ center E) : f.comp (coverMap f hf hk) = localMap := by
  apply PresentedGroup.ext
  intro i
  change f (coverMap f hf hk (generator i)) = localMap (generator i)
  rw [coverMap_generator, map_liftGenerator, localMap_generator]

/-- Perfectness makes the normalized lifts generate the entire extension. -/
theorem coverMap_surjective [Group.IsPerfect E] (hk : f.ker ≤ center E) :
    Function.Surjective (coverMap f hf hk) :=
  surjective_of_comp_surjective_of_ker_le_center_of_isPerfect f (coverMap f hf hk)
    (by rw [coverMap_fac]; exact localMap_surjective) hk

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation
