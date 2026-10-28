module

public import Theory.SpecificGroups.Triality.RootPresentationRecognition.PositiveModel

/-!
# Evaluation of the triality positive presentation

The six positive relations construct a homomorphism from the genuine
unipotent subgroup into an arbitrary target group. Pair the target roots
with the native roots and collect in their direct product. Uniqueness of
native positive coordinates forces the common collected parameters and
hence proves multiplicativity. No target-to-model map is assumed.

The image is precisely the positive root closure, and every original
short or long root parameter is preserved. These are the positive-subgroup
inputs for the subsequent signed-root Bruhat collection.
Source: GLS3 2.3.5 and 2.4.5; the literal D₄ orbit marking is unchanged.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RootPresentationRecognition
open Parabolics PositiveCoordinates RadicalCoordinates.LeviCommutators
open CentralCovers.TwoPrimary
namespace PositiveRoots
variable {n : ℕ} {hn : 0 < n} {Y : Type*} [Group Y]
local notation "P" => binaryParameters n hn

/-- A single short parameter has its original root value in the product. -/
theorem product_single_short (L : PositiveRoots n hn Y) (i : Fin 3) (t : ExtensionField P) :
    L.product (Function.update 0 i t, 0) = L.shortValue i t := by
  fin_cases i <;> simp [product, factor, shortValue, List.ofFn_succ]

/-- A single long parameter uses the actual fixed-field inclusion. -/
theorem product_single_long (L : PositiveRoots n hn Y) (i : Fin 3) (t : fixedField P) :
    L.product (0, Function.update 0 i t) = L.longValue i t := by
  fin_cases i <;> simp [product, factor, longValue, List.ofFn_succ]

/-- Evaluate the native positive normal form in the target roots. -/
def positiveHom (L : PositiveRoots n hn Y) (h : L.Relations) : unipotent P →* Y where
  toFun u := L.product ((positiveEquiv n hn).symm u)
  map_one' := by
    have hz : positiveEquiv n hn 0 = 1 := by
      apply Subtype.ext
      rw [positiveEquiv_val, ← native_product]
      exact (nativePositiveRoots n hn).product_zero
    rw [← hz, Equiv.symm_apply_apply]
    exact L.product_zero
  map_mul' a b := by
    obtain ⟨v, hv, hm⟩ := common_product h (native_relations n hn)
      ((positiveEquiv n hn).symm a) ((positiveEquiv n hn).symm b)
    have he : positiveEquiv n hn v = a * b := by
      apply Subtype.ext
      simp only [native_product, ← positiveEquiv_val,
        Equiv.apply_symm_apply] at hm
      exact hm.symm
    rw [← he, Equiv.symm_apply_apply]
    exact hv.symm

@[simp] theorem positiveHom_coordinates (L : PositiveRoots n hn Y) (h : L.Relations)
    (v : PositiveParameters n hn) :
    L.positiveHom h (positiveEquiv n hn v) = L.product v := by
  change L.product ((positiveEquiv n hn).symm (positiveEquiv n hn v)) = _
  rw [Equiv.symm_apply_apply]

/-- The image retains the full positive closure, without injectivity assumptions. -/
theorem positiveHom_range (L : PositiveRoots n hn Y) (h : L.Relations) :
    (L.positiveHom h).range = L.positiveClosure := by
  ext g
  rw [L.mem_positiveClosure_iff h]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(positiveEquiv n hn).symm u, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨positiveEquiv n hn v, L.positiveHom_coordinates h v⟩

/-- The short root marking holds for every actual unipotent representative. -/
theorem positiveHom_short (L : PositiveRoots n hn Y) (h : L.Relations)
    (i : Fin 3) (t : ExtensionField P) (u : unipotent P)
    (hu : u.val = short P rfl i t) : L.positiveHom h u = L.shortValue i t := by
  have he : positiveEquiv n hn (Function.update 0 i t, 0) = u := by
    apply Subtype.ext
    rw [positiveEquiv_val, ← native_product, product_single_short]
    exact hu.symm
  rw [← he, positiveHom_coordinates, product_single_short]

/-- Long roots retain their original fixed-field parameters. -/
theorem positiveHom_long (L : PositiveRoots n hn Y) (h : L.Relations)
    (i : Fin 3) (t : fixedField P) (u : unipotent P)
    (hu : u.val = long P rfl i t) : L.positiveHom h u = L.longValue i t := by
  have he : positiveEquiv n hn (0, Function.update 0 i t) = u := by
    apply Subtype.ext
    rw [positiveEquiv_val, ← native_product, product_single_long]
    exact hu.symm
  rw [← he, positiveHom_coordinates, product_single_long]

/-- In particular the positive closure is finite in an arbitrary target group. -/
theorem positiveClosure_finite (L : PositiveRoots n hn Y) (h : L.Relations) :
    Finite L.positiveClosure := by
  rw [← L.positiveHom_range h]
  exact Finite.of_surjective _ (L.positiveHom h).rangeRestrict_surjective

/-- The positive presentation gives the required unipotent size bound. -/
theorem card_positiveClosure_le (L : PositiveRoots n hn Y) (h : L.Relations) :
    Nat.card L.positiveClosure ≤ Nat.card (unipotent P) := by
  rw [← L.positiveHom_range h]
  exact Nat.card_le_card_of_surjective _ (L.positiveHom h).rangeRestrict_surjective

end PositiveRoots
end Triality.Standard.RootPresentationRecognition
