module

public import Theory.SpecificGroups.PSL3Even.TauGeometry.Actors
public import Theory.SpecificGroups.PSL3Even.TauGeometry.Pair
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner
public import Theory.GroupTheory.SylowKernelCore
public import Theory.FieldTheory.ScalarTwistedFixedPoints.Triangular
import Mathlib.Tactic.LinearCombination

/-!
# Large elementary pointwise fixers in Aut(PSL₃(F))

An elementary subgroup of the standard unitriangular group lies in one of
its two root planes. A graph actor would send it into the opposite plane;
pointwise fixation would therefore put it in the highest-root intersection,
which has only |F| elements. After excluding this possibility, standard
automorphism coverage and Sylow preservation give an upper triangular
linear–field action. Its literal projective matrix equations form a
triangular semilinear system on either plane. A nontrivial field coefficient
has at most |F| fixed points, so fixation of a larger subgroup eliminates it.
Finally the existing coprime determinant argument makes the remaining
linear two-element inner.

This proves the exact `LargeActorFixersAreInner` input of the Chapter E tau
adapter, with the actual projective UT₃ embedding. The proof includes q=2
and q=4 and does not pass to a power of the field coefficient.
Source: Aschbacher–Smith, E.1.1–6 and E.1.14(1), printed pp.209–214;
standard automorphism coordinates are GLS3 §2.5 and §2.7.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3.OuterSolvable Matrix.PSL3.CartanActions Matrix.PSL3.ExtensionBorel
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.TauGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private theorem not_swap_of_large_fixed (A : Subgroup (U F))
    (he : ∀ a ∈ A, a^2 = 1) (hc : Nat.card F < Nat.card A)
    (α : MulAut PSL(3,F)) (hfix : ∀ a ∈ A, α (projective F a) = projective F a) :
    ¬ (∀ b, (localFactor F b).map α.toMonoidHom = localFactor F (!b)) := by
  intro hswap
  obtain ⟨b,hb⟩ : ∃ b : Bool, A ≤ if b then V₁ F else V₂ F := by
    rcases le_plane_of_exponent_two F A he with h | h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  have ho : A ≤ if !b then V₁ F else V₂ F := by
    intro u hu
    rw [← core_comap_projective]
    change projective F u ∈ (localFactor F (!b)).pCoreIn 2
    rw [← hswap b, ← map_pCoreIn_of_injective 2 _ _ α.injective]
    refine ⟨projective F u, ?_, hfix u hu⟩
    have hh := hb hu
    rw [← core_comap_projective] at hh
    exact hh
  have hz : A ≤ Z F := by
    rw [← root_planes_inter]
    cases b
    · exact le_inf ho hb
    · exact le_inf hb ho
  have hcard := Subgroup.card_le_of_le hz
  rw [card_Z] at hcard
  exact (not_le_of_gt hc) hcard

omit [Finite F] [CharP F 2] in
private theorem triangular_diag_ne_zero (m : GL (Fin 3) F) (hm : m ∈ glBorel F)
    (i : Fin 3) : m.val i i ≠ 0 := by
  have hn : Matrix.det m.val ≠ 0 := (GeneralLinearGroup.det m).ne_zero
  rw [Matrix.det_fin_three] at hn
  simp only [hm.1,hm.2.1,hm.2.2,mul_zero,zero_mul,sub_zero,add_zero] at hn
  fin_cases i
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  · exact (mul_ne_zero_iff.mp hn).2

omit [Finite F] [CharP F 2] in
private theorem scalar_of_projection_eq (x y : SL(3,F))
    (h : projection F x = projection F y) : ∃ r : F, x.val = r • y.val := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

omit [Finite F] [CharP F 2] in
private theorem field_projective (σ : F ≃+* F) (u : U F) :
    fieldAction F σ (projective F u) = projective F ⟨σ u.x, σ u.y, σ u.c⟩ := by
  change fieldAction F σ (QuotientGroup.mk (specialLinear F u)) =
    QuotientGroup.mk (specialLinear F ⟨σ u.x, σ u.y, σ u.c⟩)
  rw [fieldAction_mk]
  congr 1
  apply Subtype.ext
  ext i j
  change σ (matrix F u i j) = matrix F ⟨σ u.x, σ u.y, σ u.c⟩ i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

omit [Finite F] [CharP F 2] in
private theorem fixed_matrix (m : GL (Fin 3) F) (hm : m ∈ glBorel F)
    (σ : F ≃+* F) (u : U F)
    (hfix : (linearConj F m * fieldAction F σ) (projective F u) = projective F u) :
    m.val * matrix F ⟨σ u.x, σ u.y, σ u.c⟩ = matrix F u * m.val := by
  rw [MulAut.mul_apply, field_projective] at hfix
  have hp : projection F (linearConjSL F m (specialLinear F ⟨σ u.x, σ u.y, σ u.c⟩)) =
      projection F (specialLinear F u) := hfix
  obtain ⟨r,hr⟩ := scalar_of_projection_eq F _ _ hp
  have hv : (linearConjSL F m (specialLinear F ⟨σ u.x, σ u.y, σ u.c⟩)).val =
      m.val * matrix F ⟨σ u.x, σ u.y, σ u.c⟩ * m.inv :=
    congrArg Units.val (linearConjSL_toGL F m _)
  have he : m.val * matrix F ⟨σ u.x, σ u.y, σ u.c⟩ =
      (r • matrix F u) * m.val := by
    rw [← show (specialLinear F u).val = matrix F u from rfl, ← hr, hv,
      Matrix.mul_assoc, m.inv_val, mul_one]
  have h00 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 0) he
  have h00 : m.val 0 0 = r * m.val 0 0 := by
    simpa [matrix, Matrix.mul_apply, Fin.sum_univ_three, hm.1, hm.2.1] using h00
  have hr1 : r = 1 := (mul_eq_right₀ (triangular_diag_ne_zero F m hm 0)).mp h00.symm
  simpa only [hr1, one_smul] using he

omit [Finite F] [CharP F 2] in
private theorem fixed_coordinates (m : GL (Fin 3) F) (hm : m ∈ glBorel F)
    (σ : F ≃+* F) (u : U F)
    (hfix : (linearConj F m * fieldAction F σ) (projective F u) = projective F u) :
    m.val 0 0 * σ u.x = u.x * m.val 1 1 ∧
    m.val 1 1 * σ u.y = u.y * m.val 2 2 ∧
    m.val 0 0 * σ u.c + m.val 0 1 * σ u.y = u.x * m.val 1 2 + u.c * m.val 2 2 := by
  have h := fixed_matrix F m hm σ u hfix
  have h01 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 1) h
  have h12 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 1 2) h
  have h02 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 2) h
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, hm.1, hm.2.2] at h01 h12 h02
  constructor
  · linear_combination h01
  constructor
  · linear_combination h12
  · linear_combination h02

omit [CharP F 2] in
private theorem card_le_of_fixed_coordinates {X : Type*} [Finite X]
    (σ : F ≃+* F) (hne : σ ≠ 1) (a b : F) (t : F → F) (v : X → F × F)
    (hv : Function.Injective v)
    (hfix : ∀ u, a * σ (v u).1 = (v u).1 ∧ b * σ (v u).2 + t (v u).1 = (v u).2) :
    Nat.card X ≤ Nat.card F := by
  let j : X → {p : F × F // a * σ p.1 = p.1 ∧ b * σ p.2 + t p.1 = p.2} :=
    fun u => ⟨v u,hfix u⟩
  exact (Nat.card_le_card_of_injective j (fun _ _ h => hv (congrArg Subtype.val h))).trans
    (FiniteField.card_triangular_fixed_le σ hne a b t)

omit [CharP F 2] in
private theorem field_eq_one_of_large_fixed (A : Subgroup (U F)) (b : Bool)
    (hA : A ≤ if b then V₁ F else V₂ F) (hc : Nat.card F < Nat.card A)
    (m : GL (Fin 3) F) (hm : m ∈ glBorel F) (σ : F ≃+* F)
    (hfix : ∀ u ∈ A, (linearConj F m * fieldAction F σ) (projective F u) = projective F u) :
    σ = 1 := by
  by_contra hne
  have h11 := triangular_diag_ne_zero F m hm 1
  have h22 := triangular_diag_ne_zero F m hm 2
  apply (not_le_of_gt hc)
  cases b
  · apply card_le_of_fixed_coordinates F σ hne (m.val 1 1 / m.val 2 2)
      (m.val 0 0 / m.val 2 2) (fun y => (m.val 0 1 / m.val 2 2) * σ y)
      (fun u : A => (u.val.y,u.val.c))
    · intro u v h
      apply Subtype.ext
      apply U.ext
      · exact ((mem_V₂ F _).mp (hA u.property)).trans ((mem_V₂ F _).mp (hA v.property)).symm
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · intro u
      obtain ⟨_,hy,hz⟩ := fixed_coordinates F m hm σ u.val (hfix u.val u.property)
      have hx : u.val.x = 0 := (mem_V₂ F _).mp (hA u.property)
      simp only [hx, zero_mul, zero_add] at hz
      dsimp only
      constructor
      · field_simp
        linear_combination hy
      · field_simp
        linear_combination hz
  · apply card_le_of_fixed_coordinates F σ hne (m.val 0 0 / m.val 1 1)
      (m.val 0 0 / m.val 2 2) (fun x => -(m.val 1 2 / m.val 2 2) * x)
      (fun u : A => (u.val.x,u.val.c))
    · intro u v h
      apply Subtype.ext
      apply U.ext
      · exact congrArg Prod.fst h
      · exact ((mem_V₁ F _).mp (hA u.property)).trans ((mem_V₁ F _).mp (hA v.property)).symm
      · exact congrArg Prod.snd h
    · intro u
      obtain ⟨hx,_,hz⟩ := fixed_coordinates F m hm σ u.val (hfix u.val u.property)
      have hy : u.val.y = 0 := (mem_V₁ F _).mp (hA u.property)
      simp only [hy, map_zero, mul_zero, add_zero] at hz
      dsimp only
      constructor
      · field_simp
        linear_combination hx
      · field_simp
        linear_combination hz

omit [CharP F 2] in
/-- Every Sylow-preserving two-element fixing a large elementary plane subgroup
pointwise is inner, for every positive binary field degree. -/
theorem largeActorFixersAreInner {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f) :
    LargeActorFixersAreInner F := by
  let := Fintype.ofFinite F
  have hchar : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hf])
  let : CharP F 2 := ringChar.of_eq hchar
  intro A he hc α hstable hpow hfix
  have hstd : α ∈ standard F := by rw [standard_eq_top_of_two_power_card F hf hF]; trivial
  obtain ⟨m,σ,ha | ha⟩ := ResidualLinear.standard_opposition_factorization α hstd
  · have hm := ResidualLinear.linear_field_upperTriangular m σ (by rwa [← ha])
    obtain ⟨b,hb⟩ : ∃ b : Bool, A ≤ if b then V₁ F else V₂ F := by
      rcases le_plane_of_exponent_two F A he with h | h
      · exact ⟨true,h⟩
      · exact ⟨false,h⟩
    have hs := field_eq_one_of_large_fixed F A b hb hc m hm σ (by rwa [← ha])
    have hα : α = linearConj F m := by simpa only [hs,map_one,mul_one] using ha
    obtain ⟨k,hk⟩ := hpow
    rw [hα] at hk ⊢
    exact ResidualInner.linearConj_twoPower_inner m hk
  · exfalso
    apply not_swap_of_large_fixed F A he hc α hfix
    have hu : (unipotent F).map (linearConj F m * fieldAction F σ).toMonoidHom = unipotent F := by
      rw [ha] at hstable
      change (unipotent F).map (((linearConj F m * fieldAction F σ).toMonoidHom).comp
        (OddPrimeCoverage.oppositionGraph F).toMonoidHom) = _ at hstable
      rwa [← Subgroup.map_map, oppositionGraph_unipotent] at hstable
    have hm := ResidualLinear.linear_field_upperTriangular m σ hu
    intro b
    rw [ha]
    change (localFactor F b).map ((linearConj F m).toMonoidHom.comp
      ((fieldAction F σ).toMonoidHom.comp
        (OddPrimeCoverage.oppositionGraph F).toMonoidHom)) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, opposition_map_local,
      CoreCalculation.field_preserves, triangular_map_local F m hm]
end Matrix.PSL3Even.TauGeometry
