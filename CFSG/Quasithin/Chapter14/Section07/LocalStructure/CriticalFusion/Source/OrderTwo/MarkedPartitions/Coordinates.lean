module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover

/-!
# Marked coordinates for the partitions in 14.7.69

On the universal cover the upper fixed plane has coordinates (r,x,0).
The nonzero single displacements are (t²y,ty,0), with t and y nonzero;
their parameters are unique and both coordinates are nonzero. The other
two lines are the central line and the line moved by a split cubic actor.
A proper central quotient removes the latter exception: adding a nonzero
kernel vector gives a lift with both coordinates nonzero.

These calculations retain the actual universal projection. The application
on the original section, including its Sylow and V-line markings, is separate.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Remark 14.7.64 and Lemma 14.7.69, printed pp.1069, 1072–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.MarkedPartitions
open Representation Representation.SL2FourNatural Representation.SL2FourCentralCover
open Matrix Matrix.SpecialLinearGroup

/-- A vector of the universal upper fixed plane, with its two field coordinates. -/
def point (r x : F) : Space := coordinates.symm (r, ![x, 0])

theorem point_coordinates (r x : F) : coordinates (point r x) = (r, ![x, 0]) :=
  coordinates.apply_symm_apply _

theorem point_projection (r x : F) : projection (point r x) = ![x, 0] :=
  congrArg Prod.snd (point_coordinates r x)

theorem point_eq_iff (r x s y : F) : point r x = point s y ↔ r = s ∧ x = y := by
  constructor
  · intro h
    have he := congrArg coordinates h
    rw [point_coordinates, point_coordinates] at he
    exact ⟨congrArg Prod.fst he, congrArg (fun z : F × V => z.2 0) he⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem point_zero : point 0 0 = 0 := by
  apply coordinates.injective
  simp [point_coordinates]

theorem point_add (r x s y : F) : point r x + point s y = point (r + s) (x + y) := by
  apply coordinates.injective
  simp only [map_add, point_coordinates, Prod.mk_add_mk]
  congr 1
  funext i
  fin_cases i <;> simp

theorem fixed_point (w : Space) (hw : (coordinates w).2 1 = 0) :
    w = point (coordinates w).1 ((coordinates w).2 0) := by
  apply coordinates.injective
  rw [point_coordinates]
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp [hw]

theorem displacement_point (t : F) (w : Space) :
    binaryAction (upper t) w - w =
      point (t ^ 2 * (coordinates w).2 1) (t * (coordinates w).2 1) := by
  apply coordinates.injective
  rw [coordinates_upper_displacement, point_coordinates]

theorem point_is_displacement (t y : F) :
    point (t ^ 2 * y) (t * y) =
      binaryAction (upper t) (coordinates.symm (0, ![0, y])) -
        coordinates.symm (0, ![0, y]) := by
  rw [displacement_point]
  simp

/-- The three single-displacement lines exclude both distinguished lines away from zero. -/
theorem displacement_coordinates_ne_zero (t y : F) (ht : t ≠ 0) (hy : y ≠ 0) :
    t ^ 2 * y ≠ 0 ∧ t * y ≠ 0 :=
  ⟨mul_ne_zero (pow_ne_zero _ ht) hy, mul_ne_zero ht hy⟩

/-- The parameter of a nonzero displacement line is unique. -/
theorem displacement_parameters_injective {t y s z : F}
    (ht : t ≠ 0) (hy : y ≠ 0) (hs : s ≠ 0)
    (he : point (t ^ 2 * y) (t * y) = point (s ^ 2 * z) (s * z)) :
    t = s ∧ y = z := by
  obtain ⟨hr, hx⟩ := (point_eq_iff _ _ _ _).mp he
  have hx0 : t * y ≠ 0 := mul_ne_zero ht hy
  have hts : t = s := by
    apply mul_right_cancel₀ hx0
    calc
      t * (t * y) = s * (s * z) := by simpa only [pow_two, mul_assoc] using hr
      _ = s * (t * y) := by rw [hx]
  subst s
  exact ⟨rfl, mul_left_cancel₀ ht hx⟩

/-- Coverage of the five-line partition, with exactly the source's nonzero actors
and vectors outside the fixed plane in the third alternative. -/
theorem point_partition (r x : F) :
    x = 0 ∨ r = 0 ∨ ∃ t y : F, t ≠ 0 ∧ y ≠ 0 ∧
      point r x = point (t ^ 2 * y) (t * y) := by
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hr : r = 0
  · exact Or.inr (Or.inl hr)
  right; right
  let t := r / x
  have ht : t ≠ 0 := div_ne_zero hr hx
  refine ⟨t, x / t, ht, div_ne_zero hx ht, ?_⟩
  apply (point_eq_iff _ _ _ _).mpr
  constructor
  · dsimp only [t]
    field_simp
  · field_simp

theorem coordinates_diagonal (a : F) (ha : a ≠ 0) (w : Space) :
    coordinates (binaryAction (diag2 a ha) w) =
      ((coordinates w).1, ![a * (coordinates w).2 0, a⁻¹ * (coordinates w).2 1]) := by
  change coordinates (fieldAction (diag2 a ha) w) = _
  rw [coordinates_action, diag2_inv]
  have hc : (SL2NaturalH1.sqrtCocycle (K := F)).val
      (diag2 a⁻¹ (inv_ne_zero ha)) = 0 := by
    funext i
    rw [SL2NaturalH1.sqrtCocycle_apply]
    fin_cases i <;> simp [diag2_coe']
  rw [hc]
  apply Prod.ext
  · simp [wedge]
  · change diag2 a ha • (coordinates w).2 = _
    funext i
    fin_cases i <;> simp [SpecialLinearGroup.smul_def, diag2_coe', mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The marked line is identified by the cubic action, rather than by dimension. -/
theorem diagonal_displacement_point (a : F) (ha : a ≠ 0) (r x : F) :
    binaryAction (diag2 a ha) (point r x) - point r x = point 0 ((a - 1) * x) := by
  apply coordinates.injective
  rw [map_sub, coordinates_diagonal, point_coordinates, point_coordinates]
  apply Prod.ext
  · simp
  · funext i
    fin_cases i <;> simp [sub_mul]

/-- The marked line, as an actual binary linear map. -/
def markedPointMap : SL2FourNatural.F →ₗ[ZMod 2] Space :=
  ({ toFun := fun x => point 0 x
     map_add' := by intro x y; simpa only [zero_add] using (point_add 0 x 0 y).symm
     map_smul' := by
       intro a x
       apply coordinates.injective
       rw [point_coordinates, map_smul, point_coordinates]
       apply Prod.ext
       · simp
       · funext i
         fin_cases i <;> simp } : SL2FourNatural.F →ₗ[SL2FourNatural.F] Space).restrictScalars (ZMod 2)

theorem markedPointMap_apply (x : F) : markedPointMap x = point 0 x := rfl

section Quotient
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (q : Space →ₗ[ZMod 2] W) (p : W →ₗ[ZMod 2] V)
  (hp : ∀ w, p (q w) = projection w)
include p hp

theorem point_image_eq_coordinates {r x s y : F}
    (h : q (point r x) = q (point s y)) : x = y := by
  have he := congrArg p h
  rw [hp, hp] at he
  simpa only [point_projection, Matrix.cons_val_zero] using congrFun he 0

/-- Every nonzero kernel vector lies on the actual central line. -/
theorem central_kernel_of_not_injective (hq : ¬ Function.Injective q) :
    ∃ k : F, k ≠ 0 ∧ q (point k 0) = 0 := by
  have hk : q.ker ≠ ⊥ := fun h => hq (LinearMap.ker_eq_bot.mp h)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hproj : projection w = 0 := by rw [← hp, show q w = 0 from hw, map_zero]
  have hcoord : (coordinates w).2 = 0 := hproj
  have he : w = point (coordinates w).1 0 := by
    apply coordinates.injective
    rw [point_coordinates]
    apply Prod.ext
    · rfl
    · rw [hcoord]
      funext i
      fin_cases i <;> rfl
  refine ⟨(coordinates w).1, ?_, ?_⟩
  · intro hz
    rw [hz, point_zero] at he
    exact hw0 he
  · rw [← he]
    exact hw

/-- In a proper central quotient, the central image and single nonzero
upper displacements cover the fixed plane. -/
theorem proper_quotient_partition (hq : ¬ Function.Injective q) (r x : F) :
    x = 0 ∨ ∃ t y : F, t ≠ 0 ∧ y ≠ 0 ∧
      q (point r x) = q (point (t ^ 2 * y) (t * y)) := by
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hr : r = 0
  · obtain ⟨k, hk, hkq⟩ := central_kernel_of_not_injective q p hp hq
    have he : q (point r x) = q (point k x) := by
      subst r
      calc
        q (point 0 x) = q (point k 0) + q (point 0 x) := by rw [hkq, zero_add]
        _ = q (point k x) := by rw [← map_add, point_add, add_zero, zero_add]
    rcases point_partition k x with h | h | ⟨t, y, ht, hy, h⟩
    · exact (hx h).elim
    · exact (hk h).elim
    · exact Or.inr ⟨t, y, ht, hy, he.trans (congrArg q h)⟩
  · rcases point_partition r x with h | h | ⟨t, y, ht, hy, h⟩
    · exact (hx h).elim
    · exact (hr h).elim
    · exact Or.inr ⟨t, y, ht, hy, congrArg q h⟩

/-- No single nonzero displacement can lie in the central image, even after quotienting. -/
theorem displacement_not_central_image (t y : F) (ht : t ≠ 0) (hy : y ≠ 0) (r : F) :
    q (point (t ^ 2 * y) (t * y)) ≠ q (point r 0) := by
  intro h
  exact mul_ne_zero ht hy (point_image_eq_coordinates q p hp h)

/-- The original marked line always has four elements, including in a central quotient. -/
theorem markedPointMap_injective : Function.Injective (q.comp markedPointMap) := by
  intro x y h
  exact point_image_eq_coordinates q p hp h

theorem markedPointMap_finrank : Module.finrank (ZMod 2) (q.comp markedPointMap).range = 2 := by
  rw [LinearMap.finrank_range_of_inj (markedPointMap_injective q p hp)]
  exact SL2NaturalH1.field_finrank 2 (by rw [Nat.card_eq_fintype_card, card_field]; rfl)

/-- The two distinguished images meet only at zero. -/
theorem central_marked_disjoint {r x : F} (he : q (point r 0) = q (point 0 x)) :
    q (point r 0) = 0 := by
  have hx := point_image_eq_coordinates q p hp he
  rw [← hx, point_zero, map_zero] at he
  exact he

omit p hp in
/-- Before a central quotient the three displacement lines also avoid the marked line. -/
theorem displacement_not_marked_image (hq : Function.Injective q)
    (t y : F) (ht : t ≠ 0) (hy : y ≠ 0) (x : F) :
    q (point (t ^ 2 * y) (t * y)) ≠ q (point 0 x) := by
  intro h
  exact mul_ne_zero (pow_ne_zero _ ht) hy ((point_eq_iff _ _ _ _).mp (hq h)).1

/-- A vector outside the fixed plane has four distinct displacements by the
upper four-group, on every quotient compatible with the natural projection. -/
theorem vector_displacements_injective (y : F) (hy : y ≠ 0) :
    Function.Injective (fun t : F => q (point (t ^ 2 * y) (t * y))) := by
  intro t s h
  exact mul_right_cancel₀ hy (point_image_eq_coordinates q p hp h)

end Quotient
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.MarkedPartitions
