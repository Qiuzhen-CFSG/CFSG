module

public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Geometry

/-!
# Flag rigidity for subgroups of the upper unitriangular group

A subgroup of UT₃(F) contained in neither coordinate root plane has common
fixed vector and covector lines equal to the standard ones. Its normalizer
in SL₃(F) therefore preserves the whole standard flag. The proof follows the
vector and covector calculation of `LinearThree.normalizer_unipotentSL_le_borelSL`,
using just two elements with the required nonzero coordinates.

Two nonzero diagonal entries and the three entries above the diagonal
inject the flag stabilizer into (Fˣ)² × F³. This gives the order bound needed
to exclude such a normalizer for a subgroup of order 3000 in PSL₃(5).
Neither calculation assumes characteristic two or commutativity of the
unitriangular subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 1.3.8, printed p.513, the assertion that the marked P* is a
maximal-parabolic unipotent radical. Coordinate definitions and their ATLAS
attribution are inherited from the imports; no new ATLAS source is copied.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.RadicalParabolicTwoSignalizers
variable (F : Type*) [Field F] [Finite F]

/-- Outside both coordinate root planes, the normalizer preserves the standard flag. -/
theorem normalizer_noncoordinate_le_borelSL (A : Subgroup (U F))
    (h₁ : ¬ A ≤ V₁ F) (h₂ : ¬ A ≤ V₂ F) :
    normalizer (A.map (specialLinear F)) ≤ borelSL F := by
  obtain ⟨a, ha, hay⟩ := SetLike.not_le_iff_exists.mp h₁
  obtain ⟨b, hb, hbx⟩ := SetLike.not_le_iff_exists.mp h₂
  have hay : a.y ≠ 0 := by simpa using hay
  have hbx : b.x ≠ 0 := by simpa using hbx
  intro g hg
  have hcol (u : U F) (hu : u ∈ A) (i : Fin 3) :
      (specialLinear F u * g).val i 0 = g.val i 0 := by
    let v := g⁻¹ * specialLinear F u * g
    have hv : v ∈ A.map (specialLinear F) :=
      (Subgroup.mem_normalizer_iff''.mp hg _).mp (Subgroup.mem_map_of_mem _ hu)
    have hvU : v ∈ unipotentSL F := by
      rw [← specialLinear_range]
      exact Subgroup.map_le_range _ _ hv
    have hv' := (mem_pointLocalSL_iff F v).mp hvU.1
    have he : specialLinear F u * g = g * v := by dsimp [v]; group
    rw [he]
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      hv'.1, hv'.2.1, hv'.2.2]
  have hrow (u : U F) (hu : u ∈ A) (j : Fin 3) :
      (g * specialLinear F u).val 2 j = g.val 2 j := by
    let v := g * specialLinear F u * g⁻¹
    have hv : v ∈ A.map (specialLinear F) :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp (Subgroup.mem_map_of_mem _ hu)
    have hvU : v ∈ unipotentSL F := by
      rw [← specialLinear_range]
      exact Subgroup.map_le_range _ _ hv
    have hv' := (mem_lineLocalSL_iff F v).mp hvU.2
    have he : g * specialLinear F u = v * g := by dsimp [v]; group
    rw [he]
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      hv'.1, hv'.2.1, hv'.2.2]
  have h20 := hcol a ha 1
  change (matrix F a * g.val) 1 0 = g.val 1 0 at h20
  have hg20 : g.val 2 0 = 0 := by
    simpa [matrix, Matrix.mul_apply, Fin.sum_univ_three, hay] using h20
  have h10 := hcol b hb 0
  change (matrix F b * g.val) 0 0 = g.val 0 0 at h10
  have hg10 : g.val 1 0 = 0 := by
    simpa [matrix, Matrix.mul_apply, Fin.sum_univ_three, hg20, hbx] using h10
  have h21 := hrow a ha 2
  change (g.val * matrix F a) 2 2 = g.val 2 2 at h21
  have hg21 : g.val 2 1 = 0 := by
    simpa [matrix, Matrix.mul_apply, Fin.sum_univ_three, hg20, hay] using h21
  exact (mem_borelSL_iff F g).mpr ⟨hg10, hg20, hg21⟩

private theorem borel_diagonal_product (g : borelSL F) :
    g.val.val 0 0 * g.val.val 1 1 * g.val.val 2 2 = 1 := by
  obtain ⟨h10, h20, h21⟩ := (mem_borelSL_iff F g.val).mp g.property
  have hd := g.val.property
  rw [Matrix.det_fin_three, h10, h20, h21] at hd
  simpa only [zero_mul, mul_zero, add_zero, sub_zero] using hd

private theorem borel_diagonal_nonzero (g : borelSL F) :
    g.val.val 0 0 ≠ 0 ∧ g.val.val 2 2 ≠ 0 := by
  have h := borel_diagonal_product F g
  constructor <;> intro hz <;> simp [hz] at h

/-- Two nonzero diagonal entries and three upper entries determine the matrix. -/
theorem card_borelSL_le :
    Nat.card (borelSL F) ≤ (Nat.card F - 1) ^ 2 * Nat.card F ^ 3 := by
  let coords : borelSL F → Fˣ × Fˣ × F × F × F := fun g =>
    (Units.mk0 (g.val.val 0 0) (borel_diagonal_nonzero F g).1,
     Units.mk0 (g.val.val 2 2) (borel_diagonal_nonzero F g).2,
     g.val.val 0 1, g.val.val 0 2, g.val.val 1 2)
  have hinj : Function.Injective coords := by
    intro g h he
    have h00 : g.val.val 0 0 = h.val.val 0 0 :=
      congrArg (fun z : Fˣ × Fˣ × F × F × F => (z.1 : F)) he
    have h22 : g.val.val 2 2 = h.val.val 2 2 :=
      congrArg (fun z : Fˣ × Fˣ × F × F × F => (z.2.1 : F)) he
    have h01 : g.val.val 0 1 = h.val.val 0 1 := congrArg (fun z => z.2.2.1) he
    have h02 : g.val.val 0 2 = h.val.val 0 2 := congrArg (fun z => z.2.2.2.1) he
    have h12 : g.val.val 1 2 = h.val.val 1 2 := congrArg (fun z => z.2.2.2.2) he
    have h11 : g.val.val 1 1 = h.val.val 1 1 := by
      apply mul_left_cancel₀ (borel_diagonal_nonzero F g).1
      apply mul_right_cancel₀ (borel_diagonal_nonzero F g).2
      calc
        g.val.val 0 0 * g.val.val 1 1 * g.val.val 2 2 = 1 :=
          borel_diagonal_product F g
        _ = g.val.val 0 0 * h.val.val 1 1 * g.val.val 2 2 := by
          rw [h00, h22]
          exact (borel_diagonal_product F h).symm
    obtain ⟨g10, g20, g21⟩ := (mem_borelSL_iff F g.val).mp g.property
    obtain ⟨h10, h20, h21⟩ := (mem_borelSL_iff F h.val).mp h.property
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h00, h22, h01, h02, h12, h11, g10, g20, g21, h10, h20, h21]
  have hc := Nat.card_le_card_of_injective coords hinj
  simpa only [Nat.card_prod, Nat.card_units, pow_two, pow_succ, pow_zero,
    mul_one, one_mul, mul_assoc] using hc

end Matrix.PSL3.RadicalParabolicTwoSignalizers
