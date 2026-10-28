module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation.Normalizer
public import Mathlib.Algebra.CharP.Reduced
/-!
# Linear two-elements in the degree-three local normalizers

For a parabolic matrix, its distinguished diagonal entry is multiplicative.
If its projective conjugation action has two-power order, that matrix power
is scalar. Determinants and distinguished entries therefore give
`det(g) = distinguished(g)^3`, since Frobenius is injective. Dividing by the
distinguished scalar produces a determinant-one matrix in the actual local
factor, with exactly the same projective conjugation action.

Source: the two-core calculation in Aschbacher–Smith F.1.12, printed p.264.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
variable (F : Type*) [Field F]
private def distinguished (point : Bool) (g : GL (Fin 3) F) : F :=
  if point then g.val 0 0 else g.val 2 2
private theorem shape_mul (point : Bool) (g h : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hh : ParabolicShape F point h) :
    ParabolicShape F point (g * h) := by
  cases point <;> obtain ⟨hg1,hg2⟩ := hg <;> obtain ⟨hh1,hh2⟩ := hh <;>
    simp [ParabolicShape, Matrix.mul_apply, Fin.sum_univ_three, hg1,hg2,hh1,hh2]
private theorem distinguished_mul (point : Bool) (g h : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hh : ParabolicShape F point h) :
    distinguished F point (g * h) = distinguished F point g * distinguished F point h := by
  cases point <;> obtain ⟨hg1,hg2⟩ := hg <;> obtain ⟨hh1,hh2⟩ := hh <;>
    simp [distinguished, Matrix.mul_apply, Fin.sum_univ_three, hg1,hg2,hh1,hh2]
private theorem shape_pow (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (k : ℕ) : ParabolicShape F point (g ^ k) := by
  induction k with
  | zero => cases point <;> simp [ParabolicShape]
  | succ k ih => rw [pow_succ]; exact shape_mul F point _ _ ih hg
private theorem distinguished_pow (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (k : ℕ) :
    distinguished F point (g ^ k) = distinguished F point g ^ k := by
  induction k with
  | zero => cases point <;> simp [distinguished]
  | succ k ih => rw [pow_succ, distinguished_mul F point _ _ (shape_pow F point g hg k) hg,
      ih, pow_succ]
private theorem distinguished_ne_zero (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) : distinguished F point g ≠ 0 := by
  cases point
  · obtain ⟨h20,h21⟩ := hg
    have he := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) g.val_inv
    have hx : g.val 2 2 * g.inv 2 2 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three,h20,h21] using he
    exact (mul_ne_zero_iff.mp (hx ▸ one_ne_zero)).1
  · obtain ⟨h10,h20⟩ := hg
    have he := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) g.inv_val
    have hx : g.inv 0 0 * g.val 0 0 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three,h10,h20] using he
    exact (mul_ne_zero_iff.mp (hx ▸ one_ne_zero)).2

variable [CharP F 2]
/-- A linear two-element preserving either local is already induced by that local. -/
theorem linear_two_element_local (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (k : ℕ) (hp : (linearConj F g) ^ (2 ^ k) = 1) :
    ∃ x : localSL F point, linearConj F g = MulAut.conj (projection F x.val) := by
  have hc : g ^ (2 ^ k) ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [← linearConj_ker]
    change linearConj F (g ^ (2 ^ k)) = 1
    rwa [map_pow]
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨c,hc⟩ := hc
  have ht : distinguished F point g ^ (2 ^ k) = (c : F) := by
    rw [← distinguished_pow F point g hg, ← hc]
    cases point <;> simp [distinguished, Matrix.scalar]
  let u : Fˣ := Units.mk0 (distinguished F point g) (distinguished_ne_zero F point g hg)
  have hu : u ^ (2 ^ k) = c := Units.ext ht
  have hd : GeneralLinearGroup.det g ^ (2 ^ k) = c ^ 3 := by
    simpa only [map_pow, GeneralLinearGroup.det_scalar, Fintype.card_fin] using
      (congrArg GeneralLinearGroup.det hc).symm
  have hd0 : GeneralLinearGroup.det g = u ^ 3 := by
    apply Units.ext
    apply iterateFrobenius_inj F 2 k
    change (↑(GeneralLinearGroup.det g) : F) ^ (2 ^ k) = (↑(u ^ 3) : F) ^ (2 ^ k)
    have he : GeneralLinearGroup.det g ^ (2 ^ k) = (u ^ 3) ^ (2 ^ k) := by
      rw [hd, ← pow_mul, Nat.mul_comm 3 (2 ^ k), pow_mul, hu]
    exact congrArg Units.val he
  let y : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g
  have hy : GeneralLinearGroup.det y = 1 := by
    dsimp only [y]
    rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hd0]
    group
  let x : SL(3,F) := ⟨y.val, congrArg Units.val hy⟩
  have hx : x ∈ localSL F point := by
    cases point
    · apply (mem_lineLocalSL_iff F x).mpr
      obtain ⟨h20,h21⟩ := hg
      have hn := distinguished_ne_zero F false g ⟨h20,h21⟩
      change g.val 2 2 ≠ 0 at hn
      simp [-Matrix.coe_units_inv, -map_inv, x, y, u, distinguished, GeneralLinearGroup.coe_scalar, Matrix.scalar,
        Matrix.diagonal_mul,h20,h21,hn]
    · apply (mem_pointLocalSL_iff F x).mpr
      obtain ⟨h10,h20⟩ := hg
      have hn := distinguished_ne_zero F true g ⟨h10,h20⟩
      change g.val 0 0 ≠ 0 at hn
      simp [-Matrix.coe_units_inv, -map_inv, x, y, u, distinguished, GeneralLinearGroup.coe_scalar, Matrix.scalar,
        Matrix.diagonal_mul,h10,h20,hn]
  refine ⟨⟨x,hx⟩, ?_⟩
  have hxy : SpecialLinearGroup.toGL x = y := Units.ext rfl
  rw [show MulAut.conj (projection F (⟨x,hx⟩ : localSL F point).val) =
    linearConj F (SpecialLinearGroup.toGL x) from (linearConj_toGL F x).symm, hxy]
  have hz : linearConj F (GeneralLinearGroup.scalar (Fin 3) u⁻¹) = 1 := by
    change GeneralLinearGroup.scalar (Fin 3) u⁻¹ ∈ (linearConj F).ker
    rw [linearConj_ker, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u⁻¹,rfl⟩
  change linearConj F g = linearConj F (GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g)
  rw [map_mul,hz,one_mul]
end Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
