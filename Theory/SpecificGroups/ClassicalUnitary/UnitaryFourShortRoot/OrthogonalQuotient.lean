module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.Stabilizer

/-!
# Long-root representatives in the binary orthogonal quotient

The eight fixed-field symmetric matrices are exhausted explicitly. Modulo
the off-diagonal short-root line, their three nonzero cosets are represented
by the long root and its two cubic conjugates. The statement is transported
through any actual homomorphism of the short-root centralizer killing that
line; no injectivity or model-placement premise is required.

This supplies the marked-vector input to I.8.5 in the binary unitary
case of Aschbacher–Smith F.4.42, printed p.295.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

omit [CharP F 2] in
private theorem binary_fixed_cases (hc : Nat.card (FixedBy.subfield F σ) = 2)
    (a : F) (ha : σ a = a) : a = 0 ∨ a = 1 := by
  let b : FixedBy.subfield F σ := ⟨a,ha⟩
  by_cases h : b = 0
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val (((Nat.card_eq_two_iff' (0 : FixedBy.subfield F σ)).mp hc).unique h one_ne_zero))

theorem cubic_mem_fixedSL : cubic F ∈ fixedSL F σ := by
  rw [mem_fixedSL]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cubic]

omit [CharP F 2] in
private theorem long_congruence_val (A : SpecialLinearGroup (Fin 2) F) :
    (hermitianCongruence F σ hσ A (longParameter F σ)).val =
      !![A.val 0 0 * σ (A.val 0 0), A.val 0 0 * σ (A.val 1 0);
         A.val 1 0 * σ (A.val 0 0), A.val 1 0 * σ (A.val 1 0)] := by
  change A.val * !![1,0;0,0] * adjoint σ A.val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjoint, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cubic_sq_val : (cubic F ^ 2).val = !![1,1;1,0] := by
  change ( !![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 2 = _
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

/-- Modulo the short-root line every nonzero vector of the binary orthogonal
three-space is represented by a long root in the orbit of the marked cubic. -/
theorem binary_orthogonal_cases (hc : Nat.card (FixedBy.subfield F σ) = 2)
    (X : hermitianMatrices F σ) (hX : X ∈ fixedHermitian F σ) :
    X = 0 ∨ X = shortParameter F σ ∨
      ∃ A : SpecialLinearGroup (Fin 2) F, A ∈ fixedSL F σ ∧
        (X = hermitianCongruence F σ hσ A (longParameter F σ) ∨
         X = hermitianCongruence F σ hσ A (longParameter F σ) + shortParameter F σ) := by
  have h10 : X.val 1 0 = X.val 0 1 :=
    (congrFun (congrFun X.property 1) 0).symm.trans (hX 0 1)
  rcases binary_fixed_cases F σ hc (X.val 0 0) (hX 0 0) with ha | ha <;>
    rcases binary_fixed_cases F σ hc (X.val 0 1) (hX 0 1) with hb | hb <;>
    rcases binary_fixed_cases F σ hc (X.val 1 1) (hX 1 1) with hd | hd
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha,hb,hd,h10]
  · right; right
    refine ⟨cubic F,cubic_mem_fixedSL F σ,Or.inl ?_⟩
    apply Subtype.ext
    simp only [ long_congruence_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubic,ha,hb,hd,h10]
  · right; left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [shortParameter,ha,hb,hd,h10]
  · right; right
    refine ⟨cubic F,cubic_mem_fixedSL F σ,Or.inr ?_⟩
    apply Subtype.ext
    simp only [AddSubgroup.coe_add, long_congruence_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubic,shortParameter,ha,hb,hd,h10,CharTwo.add_self_eq_zero]
  · right; right
    refine ⟨1,(fixedSL F σ).one_mem,Or.inl ?_⟩
    apply Subtype.ext
    simp only [ long_congruence_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha,hb,hd,h10]
  · right; right
    refine ⟨cubic F ^ 2,(fixedSL F σ).pow_mem (cubic_mem_fixedSL F σ) 2,Or.inr ?_⟩
    apply Subtype.ext
    simp only [AddSubgroup.coe_add, long_congruence_val, cubic_sq_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shortParameter,ha,hb,hd,h10,CharTwo.add_self_eq_zero]
  · right; right
    refine ⟨1,(fixedSL F σ).one_mem,Or.inr ?_⟩
    apply Subtype.ext
    simp only [AddSubgroup.coe_add, long_congruence_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shortParameter,ha,hb,hd,h10,CharTwo.add_self_eq_zero]
  · right; right
    refine ⟨cubic F ^ 2,(fixedSL F σ).pow_mem (cubic_mem_fixedSL F σ) 2,Or.inl ?_⟩
    apply Subtype.ext
    simp only [ long_congruence_val, cubic_sq_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha,hb,hd,h10]


variable [Finite F]
local notation "C" => shortCentralizer F σ hσ

/-- The whole abelian plane radical lies in the short-root centralizer. -/
def radicalIntoCentralizer : Multiplicative (hermitianMatrices F σ) →* C :=
  (inclusion (radical_le_shortCentralizer F σ hσ)).comp (radicalEquiv F σ hσ).toMonoidHom

theorem radicalIntoCentralizer_conj (a : C) (X : Multiplicative (hermitianMatrices F σ)) :
    a * radicalIntoCentralizer F σ hσ X * a⁻¹ =
      radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd
        (hermitianCongruence F σ hσ (factorRestriction F (form F σ hσ) a.val) X.toAdd)) := by
  apply Subtype.ext
  exact congrArg (fun q : radical F σ hσ => q.val) (radicalEquiv_conj F σ hσ a.val X)

/-- A fixed-field Levi matrix gives a literal element of the short-root centralizer. -/
def fixedLevi (A : fixedSL F σ) : C :=
  ⟨levi F σ hσ A.val, (mem_shortCentralizer F σ hσ _).mpr
    (by simpa only [factorRestriction_levi] using A.property)⟩

theorem radicalIntoCentralizer_map :
    (fixedHermitian F σ).toSubgroup.map (radicalIntoCentralizer F σ hσ) =
      (orthogonalRadical F σ hσ).subgroupOf C := by
  ext x
  constructor
  · rintro ⟨X,hX,rfl⟩
    exact ⟨X,hX,rfl⟩
  · rintro ⟨X,hX,he⟩
    exact ⟨X,hX,Subtype.ext he⟩

/-- Killing the original short-root line makes every nonzero vector of the
orthogonal quotient a conjugate of the actual marked long root. -/
theorem binary_orthogonal_image_fusion
    (hc : Nat.card (FixedBy.subfield F σ) = 2)
    {H : Type*} [Group H] (f : C →* H)
    (ht : f (radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (shortParameter F σ))) = 1)
    {v : H} (hv : v ∈ ((orthogonalRadical F σ hσ).subgroupOf C).map f)
    (hv1 : v ≠ 1) :
    IsConj (f (radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (longParameter F σ)))) v := by
  rw [← radicalIntoCentralizer_map, Subgroup.map_map] at hv
  obtain ⟨X,hX,rfl⟩ := hv
  obtain hzero | hshort | ⟨A,hA,hAeq | hAeq⟩ := binary_orthogonal_cases F σ hσ hc X.toAdd hX
  · have hx : X = 1 := congrArg Multiplicative.ofAdd hzero
    simp only [hx,map_one] at hv1
    exact False.elim (hv1 rfl)
  · have hx : X = Multiplicative.ofAdd (shortParameter F σ) := congrArg Multiplicative.ofAdd hshort
    exact False.elim (hv1 (by simpa only [MonoidHom.comp_apply,hx] using ht))
  · apply isConj_iff.mpr
    refine ⟨f (fixedLevi F σ hσ ⟨A,hA⟩), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, radicalIntoCentralizer_conj]
    change f (radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd
      (hermitianCongruence F σ hσ (factorRestriction F (form F σ hσ) (levi F σ hσ A)) (longParameter F σ)))) = _
    rw [factorRestriction_levi, ← hAeq]
    rfl
  · apply isConj_iff.mpr
    refine ⟨f (fixedLevi F σ hσ ⟨A,hA⟩), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, radicalIntoCentralizer_conj]
    have hx : X = Multiplicative.ofAdd (hermitianCongruence F σ hσ A (longParameter F σ)) *
        Multiplicative.ofAdd (shortParameter F σ) := congrArg Multiplicative.ofAdd hAeq
    change _ = f (radicalIntoCentralizer F σ hσ X)
    rw [hx,map_mul,map_mul,ht,mul_one]
    simp only [toAdd_ofAdd,fixedLevi,factorRestriction_levi]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
