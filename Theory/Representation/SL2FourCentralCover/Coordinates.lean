module
public import Theory.Representation.SL2FourCentralCover
public import Theory.Representation.SL2CentralExtensionFixedSpace

/-!
# Coordinates on the universal SL₂(4) central cover

Evaluation on the nonprincipal square-root cocycle, together with the actual
natural projection, identifies the universal cover with F₄ × F₄². Completeness
of the I.1.6 cohomology calculation proves injectivity; dimension three proves
surjectivity. The action of an upper unipotent of parameter t is
(r,x,y) ↦ (r+t²y,x+ty,y). Hence every upper displacement lies in the common
fixed space, and two parameters generate that entire space by displacements.

These are coordinate calculations used in Aschbacher–Smith, Remark 14.7.64
and Lemmas 14.7.69–70, printed pp.1069 and 1072–1074, combined manuscript of
1 March 2004. They concern the universal cover of the natural K*-module,
not the separate O₂(K)/U section in Lemma 14.7.73.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourCentralCover
open Representation.OneCohomology SL2FourNatural Matrix Matrix.SpecialLinearGroup

/-- Evaluation on the distinguished nonprincipal cocycle. -/
def scalarCoordinate : Space →ₗ[F] F where
  toFun w := w SL2NaturalH1.sqrtCocycle
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinates consist of one scalar and the actual natural projection. -/
def coordinateMap : Space →ₗ[F] F × V :=
  scalarCoordinate.prod fieldProjection.toLinearMap

/-- Evaluation on a principal cocycle is the determinant pairing with the projection. -/
theorem principal_evaluation (w : Space) (v : V) :
    w (principal natural v) = wedge (fieldProjection w) v := by
  exact (LinearMap.congr_fun
    (fieldSelfDual.apply_symm_apply (universalDualProjection natural w)) v).symm

/-- These are faithful coordinates: I.1.6 spans the cocycles by the principal
cocycles and the single square-root cocycle. -/
theorem coordinateMap_injective : Function.Injective coordinateMap := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro w hw
  have hr : w SL2NaturalH1.sqrtCocycle = 0 := congrArg Prod.fst hw
  have hp : fieldProjection w = 0 := congrArg Prod.snd hw
  change w = 0
  apply LinearMap.ext
  intro f
  obtain ⟨c, hc, _⟩ := SL2NaturalH1.existsUnique_representative
    (K := F) (by rw [Nat.card_eq_fintype_card, card_field]; decide) (classMap natural f)
  have he : classMap natural (f - c • SL2NaturalH1.sqrtCocycle) = 0 := by
    rw [map_sub, hc, sub_self]
  obtain ⟨v, hv⟩ := (classMap_eq_zero_iff natural _).mp he
  have hz : w (principal natural v) = 0 := by
    rw [principal_evaluation, hp]
    simp [wedge]
  change w f = 0
  calc
    w f = w ((f - c • SL2NaturalH1.sqrtCocycle) + c • SL2NaturalH1.sqrtCocycle) := by
      rw [sub_add_cancel]
    _ = 0 := by rw [← hv, map_add, map_smul, hz, hr, smul_zero, add_zero]

/-- F₄-coordinates on the universal covering space. -/
def coordinates : Space ≃ₗ[F] F × V :=
  LinearEquiv.ofBijective coordinateMap ⟨coordinateMap_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [field_finrank, Module.finrank_prod]
      simp)).mp coordinateMap_injective⟩

theorem coordinates_apply (w : Space) :
    coordinates w = (w SL2NaturalH1.sqrtCocycle, fieldProjection w) := rfl

/-- The full action formula retains the literal natural group element. -/
theorem coordinates_action (g : SL) (w : Space) :
    coordinates (fieldAction g w) =
      ((coordinates w).1 + wedge (coordinates w).2
        ((SL2NaturalH1.sqrtCocycle (K := F)).val g⁻¹),
        natural g (coordinates w).2) := by
  apply Prod.ext
  · change w (SL2NaturalH1.sqrtCocycle +
        principal natural ((SL2NaturalH1.sqrtCocycle (K := F)).val g⁻¹)) = _
    rw [map_add, principal_evaluation]
    rfl
  · exact LinearMap.congr_fun (fieldProjection.isIntertwining' g) w

theorem upper_transvection (t : F) :
    upper t = SpecialLinearGroup.transvection zero_ne_one t := by
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [upper, transvection_coe]

private theorem upper_inv (t : F) : (upper t)⁻¹ = upper t := by
  rw [upper_transvection, transvection_inv, CharTwo.neg_eq]

private theorem root_eq_square (t : F) : (frobeniusEquiv F 2).symm t = t ^ 2 := by
  apply CharTwo.sq_injective
  change (frobeniusEquiv F 2).symm t ^ 2 = (t ^ 2) ^ 2
  rw [frobeniusEquiv_symm_pow_p, ← pow_mul, pow_four]

private theorem sqrtCocycle_upper (t : F) :
    (SL2NaturalH1.sqrtCocycle (K := F)).val (upper t) = ![t ^ 2, 0] := by
  funext i
  calc
    _ = (frobeniusEquiv F 2).symm ((upper t).val i 0 * (upper t).val i 1) :=
      SL2NaturalH1.sqrtCocycle_apply (upper t) i
    _ = _ := by fin_cases i <;> simp [upper, root_eq_square]

/-- Upper unipotents move along the F₄-lines of slopes parametrized by t. -/
theorem coordinates_upper (t : F) (w : Space) :
    coordinates (fieldAction (upper t) w) =
      ((coordinates w).1 + t ^ 2 * (coordinates w).2 1,
        ![(coordinates w).2 0 + t * (coordinates w).2 1, (coordinates w).2 1]) := by
  rw [coordinates_action, upper_inv, sqrtCocycle_upper]
  change (_ + wedge _ ![t ^ 2, 0], action (upper t) _) = _
  rw [upper_action]
  congr 1
  simp only [wedge, Matrix.cons_val_one, Matrix.cons_val_zero,
    mul_zero, zero_sub, CharTwo.neg_eq]
  ring

/-- The displacement formula used in the partitions in 14.7.69. -/
theorem coordinates_upper_displacement (t : F) (w : Space) :
    coordinates (binaryAction (upper t) w - w) =
      (t ^ 2 * (coordinates w).2 1, ![t * (coordinates w).2 1, 0]) := by
  rw [map_sub]
  change coordinates (fieldAction (upper t) w) - coordinates w = _
  rw [coordinates_upper]
  apply Prod.ext
  · simp
  · funext i
    fin_cases i <;> simp

/-- Every nonidentity upper element has the same fixed space. -/
theorem upper_fixed_iff (t : F) (ht : t ≠ 0) (w : Space) :
    binaryAction (upper t) w = w ↔ (coordinates w).2 1 = 0 := by
  rw [← sub_eq_zero, ← coordinates.map_eq_zero_iff,
    coordinates_upper_displacement]
  constructor
  · intro h
    have h1 := congrArg (fun x : F × V => x.2 0) h
    exact (mul_eq_zero.mp h1).resolve_left ht
  · intro h
    simp [h]

/-- All upper displacements lie in their common fixed space. -/
theorem upper_displacement_fixed (s t : F) (w : Space) :
    binaryAction (upper s) (binaryAction (upper t) w - w) =
      binaryAction (upper t) w - w := by
  apply coordinates.injective
  change coordinates (fieldAction (upper s) _) = _
  rw [coordinates_upper, coordinates_upper_displacement]
  simp

/-- Two upper displacements generate the entire common fixed space. -/
theorem fixed_is_sum_of_upper_displacements (w : Space)
    (hw : (coordinates w).2 1 = 0) :
    ∃ (s t : F) (u v : Space),
      w = (binaryAction (upper s) u - u) + (binaryAction (upper t) v - v) := by
  let a : F := ⟨0, 1⟩
  have ha : a + a ^ 2 = 1 := by decide +kernel
  let r := (coordinates w).1
  let x := (coordinates w).2 0
  let z := r + x
  let y := x + a * z
  have hy : y + a * z = x := by
    dsimp only [y]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hr : y + a ^ 2 * z = r := by
    calc
      y + a ^ 2 * z = x + (a + a ^ 2) * z := by dsimp only [y]; ring
      _ = x + (r + x) := by rw [ha, one_mul]
      _ = r := by rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  let u := coordinates.symm (0, ![0, y])
  let v := coordinates.symm (0, ![0, z])
  refine ⟨1, a, u, v, ?_⟩
  apply coordinates.injective
  rw [map_add, coordinates_upper_displacement, coordinates_upper_displacement]
  simp only [u, v, coordinates.apply_symm_apply, one_pow, one_mul,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  apply Prod.ext
  · exact hr.symm
  · funext i
    fin_cases i
    · exact hy.symm
    · exact hw

/-- Apart from the central line and the diagonal-moved line, every vector
of the fixed plane is a single nonzero upper displacement. These are the five
F₄-lines in the partition used in 14.7.69. -/
theorem fixed_plane_partition (w : Space) (hw : (coordinates w).2 1 = 0) :
    (coordinates w).2 = 0 ∨ (coordinates w).1 = 0 ∨
      ∃ t : F, t ≠ 0 ∧ ∃ v : Space, w = binaryAction (upper t) v - v := by
  by_cases hx : (coordinates w).2 0 = 0
  · left
    funext i
    fin_cases i <;> assumption
  by_cases hr : (coordinates w).1 = 0
  · exact Or.inr (Or.inl hr)
  right; right
  let t := (coordinates w).1 / (coordinates w).2 0
  have ht : t ≠ 0 := div_ne_zero hr hx
  let y := (coordinates w).2 0 / t
  let v := coordinates.symm (0, ![0, y])
  refine ⟨t, ht, v, ?_⟩
  apply coordinates.injective
  rw [coordinates_upper_displacement]
  simp only [v, coordinates.apply_symm_apply, Matrix.cons_val_one]
  apply Prod.ext
  · change (coordinates w).1 = t ^ 2 * ((coordinates w).2 0 / t)
    calc
      _ = t * (coordinates w).2 0 := by dsimp only [t]; field_simp
      _ = _ := by field_simp
  · funext i
    fin_cases i
    · change (coordinates w).2 0 = t * ((coordinates w).2 0 / t)
      field_simp
    · exact hw

end Representation.SL2FourCentralCover

