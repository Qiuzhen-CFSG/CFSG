module
public import Theory.SpecificGroups.SymplecticFour.WeylFrame
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
import Mathlib.Tactic.FinCases

/-!
# The two Cartan-fixed neighbors of a symplectic flag

In the plane parabolic, a Cartan-fixed flag has a first column which is an
eigenvector for diag(a,1) on the plane. In the point parabolic, the second
column modulo the fixed point is an eigenvector for diag(a,a⁻¹). For q > 2
in characteristic two the two eigenvalues are distinct, including for q = 4.
Thus each fixed flag lies in the Borel coset or its specified Weyl-reflection
coset. No Hall conjugacy or polygon identification is required.

These native coset calculations feed the literal extended completion's
fixed-neighbor theorem. Source: the Cartan/apartment argument discussed in
Aschbacher–Smith F.4.10 and F.4.16, printed pp.279,282 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.WeylFrame
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private theorem separating_unit (hq : 2 < Nat.card F) :
    ∃ a : Fˣ, (a : F) ≠ 1 ∧ (a : F) ≠ (a⁻¹ : Fˣ) := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨a,ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  refine ⟨a,ha1,?_⟩
  intro h
  apply ha1
  apply CharTwo.sq_injective
  calc
    (a : F)^2 = (a : F)*(a⁻¹ : Fˣ) := by rw [pow_two,h]
    _ = (1 : F)^2 := by simp

omit [CharP F 2] [Finite F] in
private theorem conjugate_equation (g t : Sp F) :
    t.val * g.val = g.val * (g⁻¹*t*g).val := by
  have h : t*g=g*(g⁻¹*t*g) := by group
  exact congrArg Subtype.val h

/-- On the plane endpoint, a coset fixed by the full Cartan is one of the two
coordinate-line cosets. This proves the local apartment markings. -/
theorem plane_fixed_coset (hq : 2 < Nat.card F) (g : Sp F) (hg : g ∈ planeParabolic)
    (hfix : ∀ a b : Fˣ, g⁻¹*diagonalTorus a b*g ∈ borel) :
    g ∈ borel ∨ planeReflection*g ∈ borel := by
  obtain ⟨a,ha,_⟩ := separating_unit hq
  let t := diagonalTorus a 1
  let z := g⁻¹*t*g
  have hz : z ∈ borel := hfix a 1
  have hc := (mem_pointParabolic_iff z).mp hz.1
  have hm := conjugate_equation g t
  change t.val*g.val=g.val*z.val at hm
  have h0 : (a : F)*g.val (.inl 0) (.inl 0) =
      g.val (.inl 0) (.inl 0)*z.val (.inl 0) (.inl 0) := by
    have h := congrArg (fun A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => A (.inl 0) (.inl 0)) hm
    simpa [t,diagonalTorus,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,hc.1,hc.2] using h
  have h1 : g.val (.inl 1) (.inl 0) =
      g.val (.inl 1) (.inl 0)*z.val (.inl 0) (.inl 0) := by
    have h := congrArg (fun A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => A (.inl 1) (.inl 0)) hm
    simpa [t,diagonalTorus,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,hc.1,hc.2] using h
  by_cases h10 : g.val (.inl 1) (.inl 0)=0
  · left
    exact ⟨(mem_pointParabolic_iff g).mpr ⟨h10,fun i => (mem_planeParabolic_iff g).mp hg i 0⟩,hg⟩
  · have hz1 : z.val (.inl 0) (.inl 0)=1 := by
      apply (mul_left_cancel₀ h10)
      simpa using h1.symm
    have h00 : g.val (.inl 0) (.inl 0)=0 := by
      rw [hz1,mul_one] at h0
      exact (mul_eq_mul_right_iff.mp (h0.trans (one_mul _).symm)).resolve_left ha
    right
    have hp := planeParabolic.mul_mem planeReflection_mem hg
    refine ⟨(mem_pointParabolic_iff _).mpr ⟨?_,fun i => (mem_planeParabolic_iff _).mp hp i 0⟩,hp⟩
    simpa [planeReflection,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two] using h00

omit [CharP F 2] [Finite F] in
private theorem point_row_zero (g : pointParabolic (F := F))
    (j : Fin 2 ⊕ Fin 2) (hj : j ≠ .inr 0) : g.val.val (.inr 0) j = 0 := by
  have h := preserves_form g.val (e (F := F) 0) (Pi.single j 1)
  rw [pointParabolic_smul_e_zero g] at h
  have ha : g.val.val (.inl 0) (.inl 0) ≠ 0 := by
    rw [← determinantCharacter_point_coe g]
    exact Units.ne_zero _
  simpa [map_smul, form_apply, e, Fin.sum_univ_two, smul_eq_mulVec,
    Matrix.mulVec_single, Pi.single_apply, Ne.symm hj, ha] using h

/-- On the point endpoint, the induced diagonal action on the perpendicular
quotient fixes exactly the two coordinate-line cosets, including over F₄. -/
theorem point_fixed_coset (hq : 2 < Nat.card F) (g : Sp F) (hg : g ∈ pointParabolic)
    (hfix : ∀ a b : Fˣ, g⁻¹*diagonalTorus a b*g ∈ borel) :
    g ∈ borel ∨ pointReflection*g ∈ borel := by
  obtain ⟨a,_,ha⟩ := separating_unit hq
  let t := diagonalTorus 1 a
  let z := g⁻¹*t*g
  have hz : z ∈ borel := hfix 1 a
  have hc := (mem_planeParabolic_iff z).mp hz.2
  have hgc := (mem_pointParabolic_iff g).mp hg
  have hm := conjugate_equation g t
  change t.val*g.val=g.val*z.val at hm
  have h1 : (a : F)*g.val (.inl 1) (.inl 1) =
      g.val (.inl 1) (.inl 1)*z.val (.inl 1) (.inl 1) := by
    have h := congrArg (fun A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => A (.inl 1) (.inl 1)) hm
    simpa [t,diagonalTorus,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,hc,hgc.1] using h
  have h3 : (a⁻¹ : Fˣ)*g.val (.inr 1) (.inl 1) =
      g.val (.inr 1) (.inl 1)*z.val (.inl 1) (.inl 1) := by
    have h := congrArg (fun A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => A (.inr 1) (.inl 1)) hm
    simpa [t,diagonalTorus,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,hc,hgc.2] using h
  have hr : g.val (.inr 0) (.inl 1)=0 := point_row_zero (⟨g,hg⟩ : pointParabolic (F := F)) (.inl 1) (by decide)
  by_cases h31 : g.val (.inr 1) (.inl 1)=0
  · left
    refine ⟨hg,(mem_planeParabolic_iff _).mpr ?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · exact hgc.2 0
    · exact hr
    · exact hgc.2 1
    · exact h31
  · have hza : z.val (.inl 1) (.inl 1)=(a⁻¹ : Fˣ) := by
      apply (mul_right_cancel₀ h31)
      simpa only [mul_comm _ (g.val (.inr 1) (.inl 1))] using h3.symm
    have h11 : g.val (.inl 1) (.inl 1)=0 := by
      rw [hza,mul_comm (g.val (.inl 1) (.inl 1))] at h1
      exact (mul_eq_mul_right_iff.mp h1).resolve_left ha
    right
    have hp := pointParabolic.mul_mem pointReflection_mem hg
    refine ⟨hp,(mem_planeParabolic_iff _).mpr ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pointReflection,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,hgc.1,hgc.2,hr,h11]
end Theory.SpecificGroups.SymplecticFour.WeylFrame
