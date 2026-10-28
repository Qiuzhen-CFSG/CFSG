module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus.Control
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# A split torus controlled by diagonal and graph actions

For a nonzero parameter k, the last two coordinates carry the matrix
with diagonal (u + u⁻¹)/2 and off-diagonal entries (u - u⁻¹)/(2k)
and k(u - u⁻¹)/2. These matrices form an actual homomorphism from Fˣ
into SL₃, and the standard involution inverts them. A diagonal element
with ratio ±1 preserves this torus. A diagonal times inverse transpose
preserves it when its ratio is ±k².

Over a field of order p congruent to three modulo four, either δ or -δ
is a nonzero square. This chooses one torus for the whole subgroup in
`DiagonalControl`. An odd prime divisor of (p-1)/2 supplies a unit whose
torus matrix mixes coordinates 1 and 2.

Source: the concrete odd-torus construction for Aschbacher--Smith
E.1.14(7), printed p.214, and Aschbacher (1982), Lemma 4.11. The geometric
existence of `DiagonalControl` is not asserted here.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3.OuterSolvable

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.OddTorus
variable (F : Type*) [Field F]

/-- The concrete matrix on the last two coordinates. -/
@[expose] def planeMatrix (k u : Fˣ) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0;
     0, ((u : F) + (u⁻¹ : Fˣ)) / 2, ((u : F) - (u⁻¹ : Fˣ)) / (2 * k);
     0, k * ((u : F) - (u⁻¹ : Fˣ)) / 2, ((u : F) + (u⁻¹ : Fˣ)) / 2]

private theorem planeMatrix_det (h2 : (2 : F) ≠ 0) (k u : Fˣ) :
    (planeMatrix F k u).det = 1 := by
  simp [planeMatrix, Matrix.det_fin_three]
  field_simp
  ring


/-- The determinant-one split torus, parametrized by the literal unit group. -/
@[expose] def planeTorus (h2 : (2 : F) ≠ 0) (k : Fˣ) : Fˣ →* SL(3,F) where
  toFun u := ⟨planeMatrix F k u, by exact planeMatrix_det F h2 k u⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [planeMatrix, h2]
  map_mul' u v := by
    apply Subtype.ext
    change planeMatrix F k (u * v) = planeMatrix F k u * planeMatrix F k v
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    all_goals field_simp
    all_goals ring

/-- A unit whose square is nonidentity gives the required nonzero off-block entry. -/
theorem planeTorus_mixes (h2 : (2 : F) ≠ 0) (k u : Fˣ) (hu : u ^ 2 ≠ 1) :
    MixesSecondPlane F (planeTorus F h2 k u) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  change ((u : F) - (u⁻¹ : Fˣ)) / (2 * (k : F)) ≠ 0
  apply div_ne_zero _ (mul_ne_zero h2 k.ne_zero)
  intro he
  have he' : u = u⁻¹ := Units.ext (sub_eq_zero.mp he)
  apply hu
  rw [pow_two]
  exact (congrArg (fun v => v * u) he').trans (inv_mul_cancel u)

/-- The distinguished coordinate involution inverts the entire torus. -/
theorem planeTorus_standard (h2 : (2 : F) ≠ 0) (k u : Fˣ) :
    SL3.standardInvolution F * planeTorus F h2 k u * (SL3.standardInvolution F)⁻¹ =
      planeTorus F h2 k u⁻¹ := by
  have hinv : (SL3.standardInvolution F)⁻¹ = SL3.standardInvolution F := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using SL3.standardInvolution_sq F
  rw [hinv]
  apply Subtype.ext
  change (SL3.standardInvolution F).val * planeMatrix F k u *
    (SL3.standardInvolution F).val = planeMatrix F k u⁻¹
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SL3.standardInvolution, planeMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem diagonal_inner_action (h2 : (2 : F) ≠ 0) (k u : Fˣ)
    (d : SL(3,F)) (hd : d.val = Matrix.diagonal (fun i => d.val i i))
    (hr : d.val 2 2 = d.val 1 1 ∨ d.val 2 2 = -d.val 1 1) :
    d * planeTorus F h2 k u * d⁻¹ = planeTorus F h2 k u ∨
      d * planeTorus F h2 k u * d⁻¹ = planeTorus F h2 k u⁻¹ := by
  rcases hr with hr | hr
  · left
    apply mul_inv_eq_iff_eq_mul.mpr
    apply Subtype.ext
    change d.val * planeMatrix F k u = planeMatrix F k u * d.val
    conv_lhs => rw [hd]
    conv_rhs => rw [hd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, planeMatrix, hr]
    all_goals ring
  · right
    apply mul_inv_eq_iff_eq_mul.mpr
    apply Subtype.ext
    change d.val * planeMatrix F k u = planeMatrix F k u⁻¹ * d.val
    conv_lhs => rw [hd]
    conv_rhs => rw [hd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, planeMatrix, hr]
    all_goals ring

private theorem graphSL_plane_val (h2 : (2 : F) ≠ 0) (k u : Fˣ) :
    (graphSL F (planeTorus F h2 k u)).val = (planeMatrix F k u⁻¹).transpose := by
  have ht (x : SL(3,F)) :
      (SpecialLinearGroup.transpose x)⁻¹ = SpecialLinearGroup.transpose x⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change x.val.transpose * (x⁻¹).val.transpose = (1 : Matrix (Fin 3) (Fin 3) F)
    rw [← Matrix.transpose_mul]
    change ((x⁻¹ * x).val).transpose = _
    simp
  change ((SpecialLinearGroup.transpose (planeTorus F h2 k u))⁻¹).val = _
  rw [ht, ← map_inv]
  rfl

private theorem diagonal_graph_action (h2 : (2 : F) ≠ 0) (k u : Fˣ)
    (d : SL(3,F)) (hd : d.val = Matrix.diagonal (fun i => d.val i i))
    (hr : d.val 2 2 = (k : F)^2 * d.val 1 1 ∨
      d.val 2 2 = -((k : F)^2 * d.val 1 1)) :
    d * graphSL F (planeTorus F h2 k u) * d⁻¹ = planeTorus F h2 k u ∨
      d * graphSL F (planeTorus F h2 k u) * d⁻¹ = planeTorus F h2 k u⁻¹ := by
  rcases hr with hr | hr
  · right
    apply mul_inv_eq_iff_eq_mul.mpr
    apply Subtype.ext
    change d.val * (graphSL F (planeTorus F h2 k u)).val = planeMatrix F k u⁻¹ * d.val
    rw [graphSL_plane_val]
    conv_lhs => rw [hd]
    conv_rhs => rw [hd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, planeMatrix, Matrix.transpose_apply, hr]
    all_goals field_simp
  · left
    apply mul_inv_eq_iff_eq_mul.mpr
    apply Subtype.ext
    change d.val * (graphSL F (planeTorus F h2 k u)).val = planeMatrix F k u * d.val
    rw [graphSL_plane_val]
    conv_lhs => rw [hd]
    conv_rhs => rw [hd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, planeMatrix, Matrix.transpose_apply, hr]
    all_goals field_simp
    all_goals ring

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.OddTorus

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.OddTorus
variable (F : Type*) [Field F] [Finite F]

/-- In the residue-three case, one of the two signed ratios has a nonzero square root. -/
theorem exists_square_or_neg {p : ℕ} (hF : Nat.card F = p) (hp4 : p % 4 = 3)
    (δ : Fˣ) : ∃ k : Fˣ, (k : F) ^ 2 = δ ∨ (k : F) ^ 2 = -(δ : F) := by
  classical
  let := Fintype.ofFinite F
  have hneg : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF, hp4]
    simp
  have hsq : IsSquare (δ : F) ∨ IsSquare (-(δ : F)) := by
    by_cases h : IsSquare (δ : F)
    · exact Or.inl h
    right
    apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr δ.ne_zero)).mp
    rw [← neg_one_mul, map_mul,
      quadraticChar_neg_one_iff_not_isSquare.mpr hneg,
      quadraticChar_neg_one_iff_not_isSquare.mpr h]
    norm_num
  rcases hsq with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk0 : k ≠ 0 := by intro h; simp [h] at hk
    exact ⟨Units.mk0 k hk0, Or.inl (by simpa [pow_two] using hk.symm)⟩
  · have hk0 : k ≠ 0 := by intro h; simp [h] at hk
    exact ⟨Units.mk0 k hk0, Or.inr (by simpa [pow_two] using hk.symm)⟩

/-- The odd part of the split multiplicative group has a prime-order element. -/
theorem exists_odd_prime_unit {p : ℕ} (hbig : 3 < p)
    (hF : Nat.card F = p) (hp4 : p % 4 = 3) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ u : Fˣ, orderOf u = r := by
  have hn : (p - 1) / 2 ≠ 1 := by omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hn
  have hodd : Odd ((p - 1) / 2) := by
    rw [Nat.odd_iff]
    omega
  have hor := hodd.of_dvd_nat hrd
  have hrd' : r ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    exact hrd.trans ⟨2, by omega⟩
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' r hrd'
  exact ⟨r, hr, hor, u, hu⟩

omit [Finite F] in
private theorem innerSL_graph_action (x : SL(3,F)) :
    innerSL F (graphSL F x) = graphElement F * innerSL F x * (graphElement F)⁻¹ := by
  apply Subtype.ext
  change MulAut.conj (Matrix.PSL3.projection F (graphSL F x)) =
    graph F * MulAut.conj (Matrix.PSL3.projection F x) * (graph F)⁻¹
  have he : Matrix.PSL3.projection F (graphSL F x) =
      graph F (Matrix.PSL3.projection F x) := rfl
  rw [he]
  ext y
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

omit [Finite F] in
private theorem innerSL_outer_action (d x : SL(3,F)) :
    (innerSL F d * graphElement F) * innerSL F x * (innerSL F d * graphElement F)⁻¹ =
      innerSL F (d * graphSL F x * d⁻¹) := by
  rw [map_mul, map_mul, map_inv, innerSL_graph_action]
  group

/-- One square choice makes every element of the controlled subgroup act on
all elements of the concrete split torus either trivially or by inversion. -/
theorem controlled_planeTorus {p : ℕ}
    (hF : Nat.card F = p) (hp4 : p % 4 = 3) (h2 : (2 : F) ≠ 0)
    (D : Subgroup (graphExtension F)) (hD : DiagonalControl F D) :
    ∃ k : Fˣ, ∀ u : Fˣ, ∀ g ∈ D,
      g * innerSL F (planeTorus F h2 k u) * g⁻¹ = innerSL F (planeTorus F h2 k u) ∨
      g * innerSL F (planeTorus F h2 k u) * g⁻¹ = innerSL F (planeTorus F h2 k u)⁻¹ := by
  obtain ⟨δ, hδ⟩ := hD
  obtain ⟨k, hk⟩ := exists_square_or_neg F hF hp4 δ
  refine ⟨k, ?_⟩
  intro u g hg
  obtain ⟨d, hd, (⟨rfl, hr⟩ | ⟨rfl, hr⟩)⟩ := hδ g hg
  · rcases diagonal_inner_action F h2 k u d hd hr with he | he
    · exact Or.inl (by simpa only [map_mul, map_inv] using congrArg (innerSL F) he)
    · exact Or.inr (by simpa only [map_mul, map_inv] using congrArg (innerSL F) he)
  · have hr' : d.val 2 2 = (k : F)^2 * d.val 1 1 ∨
        d.val 2 2 = -((k : F)^2 * d.val 1 1) := by
      rcases hk with hk | hk
      · simpa only [hk] using hr
      · rcases hr with hr | hr
        · right; rw [hk, neg_mul, neg_neg]; exact hr
        · left; rw [hk, neg_mul]; exact hr
    rw [innerSL_outer_action]
    rcases diagonal_graph_action F h2 k u d hd hr' with he | he
    · exact Or.inl (congrArg (innerSL F) he)
    · exact Or.inr (by simpa only [map_inv] using congrArg (innerSL F) he)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.OddTorus
