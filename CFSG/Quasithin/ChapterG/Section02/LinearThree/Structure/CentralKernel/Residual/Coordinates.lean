module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Source
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A cubic actor at the marked point of G.2.5

In coordinates sending the marked point to the first coordinate line,
use diag(1, [[0,1],[1,1]]). Its cube is one in characteristic two. A
matrix fixing that line pointwise and moving every vector into the line
is a shear; commuting with the cubic forces both shear entries to vanish.
Conjugating back preserves the actual SL₃ model, including its scalar
center. The calculation also holds over F₂.

Source: Aschbacher–Smith G.2.5(3), printed pp.335–336, using the
point-stabilizer action argument of G.2.3, printed pp.333–334.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel.ResidualCoordinates

section Matrices
variable {F : Type*} [Field F] [CharP F 2]
private def cubic : SL(3, F) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by simp [det_fin_three, CharTwo.neg_eq]⟩
private theorem cubic_cube : (cubic (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
private theorem cubic_fixed : (cubic (F := F)) • (![1, 0, 0] : Fin 3 → F) = ![1, 0, 0] := by
  change (cubic (F := F)).val *ᵥ _ = _
  ext i
  fin_cases i <;> simp [cubic, mulVec, dotProduct, Fin.sum_univ_three]
private theorem shear_centralizer (u : SL(3, F))
    (hfix : u • (![1, 0, 0] : Fin 3 → F) = ![1, 0, 0])
    (hmove : ∀ v : Fin 3 → F, u • v - v ∈ Submodule.span F {(![1, 0, 0] : Fin 3 → F)})
    (hc : Commute u (cubic (F := F))) : u = 1 := by
  have hcol : u.val 0 0 = 1 := by
    have hh := congrFun hfix 0
    change (u.val *ᵥ ![1, 0, 0]) 0 = 1 at hh
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using hh
  have hrow (i j : Fin 3) (hi : i ≠ 0) : u.val i j = (1 : Matrix (Fin 3) (Fin 3) F) i j := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hmove (Pi.single j 1))
    have hh := congrFun ha i
    have hi' : (![1, 0, 0] : Fin 3 → F) i = 0 := by fin_cases i <;> simp_all
    change a * (![1, 0, 0] : Fin 3 → F) i = (u.val *ᵥ Pi.single j 1) i - (Pi.single j (1 : F) : Fin 3 → F) i at hh
    simp only [hi', mul_zero, Matrix.mulVec_single, MulOpposite.op_one, one_smul] at hh
    have he := (sub_eq_zero.mp hh.symm)
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using he
  have hc01 := congrArg (fun x : SL(3, F) => x.val 0 1) hc.eq
  have hc02 := congrArg (fun x : SL(3, F) => x.val 0 2) hc.eq
  change (u.val * (cubic (F := F)).val) 0 1 = ((cubic (F := F)).val * u.val) 0 1 at hc01
  change (u.val * (cubic (F := F)).val) 0 2 = ((cubic (F := F)).val * u.val) 0 2 at hc02
  simp [cubic, Matrix.mul_apply, Fin.sum_univ_three] at hc01 hc02
  have h01 : u.val 0 1 = 0 := by linear_combination hc02
  have h02 : u.val 0 2 = 0 := hc01.trans h01
  apply Subtype.ext
  ext i j
  by_cases hi : i = 0
  · subst i
    fin_cases j <;> simp_all
  · exact hrow i j hi

private theorem exists_cubic_at_point (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) :
    ∃ c : SL(3, F), c ^ 3 = 1 ∧ (∀ v ∈ P, c • v = v) ∧
      ∀ u : SL(3, F), (∀ v ∈ P, u • v = v) →
        (∀ v : Fin 3 → F, u • v - v ∈ P) → Commute u c → u = 1 := by
  have hPne : P ≠ ⊥ := by
    intro he
    rw [he] at hP
    have hz : Module.finrank F (⊥ : Submodule F (Fin 3 → F)) = 0 := finrank_bot F (Fin 3 → F)
    omega
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff P).mp hPne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hP hw hw0
  obtain ⟨s, hs⟩ := SpecialLinearGroup.exists_mulVec_eq_three
    (![1, 0, 0] : Fin 3 → F) w (by simp) hw0
  change s • (![1, 0, 0] : Fin 3 → F) = w at hs
  let c := s * cubic (F := F) * s⁻¹
  have hc (v : Fin 3 → F) : c • v = s • (cubic (F := F) • (s⁻¹ • v)) := by
    simp only [c, mul_smul]
  refine ⟨c, ?_, ?_, ?_⟩
  · change (MulAut.conj s) (cubic (F := F)) ^ 3 = 1
    rw [← map_pow, cubic_cube, map_one]
  · intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hv)
    rw [hc, smul_comm (s⁻¹) a, ← hs, inv_smul_smul,
      smul_comm (cubic (F := F)) a, cubic_fixed, smul_comm s a]
  · intro u huf hum huc
    let u' := s⁻¹ * u * s
    have hu' (v : Fin 3 → F) : u' • v = s⁻¹ • (u • (s • v)) := by
      simp only [u', mul_smul]
    have hu1 : u' = 1 := by
      apply shear_centralizer
      · rw [hu', hs, huf w hw, ← hs, inv_smul_smul]
      · intro v
        have hv := hum (s • v)
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hv)
        apply Submodule.mem_span_singleton.mpr
        refine ⟨a, ?_⟩
        have ha' := congrArg (fun z : Fin 3 → F => s⁻¹ • z) ha
        rw [smul_comm, ← hs, inv_smul_smul, smul_sub, inv_smul_smul] at ha'
        simpa only [hu'] using ha'
      · have hh := huc.map (MulAut.conj s⁻¹).toMonoidHom
        simpa [c, MulAut.conj_apply, mul_assoc, u'] using hh
    have hh := congrArg (fun z : SL(3, F) => s * z * s⁻¹) hu1
    simpa [u', mul_assoc] using hh
end Matrices

/-- The cubic in the source's actual SL₃ model fixes the marked point and
has no nonidentity fixed shear along it. -/
theorem exists_point_cubic {G : Type*} [Group G] [Finite G]
    {D : Setup G} {F : Type*} [Field F] [Finite F]
    {n : ℕ} {g h : G} (d : Hypothesis D F n g h) :
    ∃ c : SL(3, F), c ^ 3 = 1 ∧ (∀ v ∈ d.point, c • v = v) ∧
      ∀ u : SL(3, F), (∀ v ∈ d.point, u • v = v) →
        (∀ v : Fin 3 → F, u • v - v ∈ d.point) → Commute u c → u = 1 := by
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    apply ringChar.of_eq
    apply FiniteField.even_card_iff_char_two.mpr
    rw [← Nat.card_eq_fintype_card, d.field_card]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt d.exponent_pos))
  exact exists_cubic_at_point d.point d.point_dimension

end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel.ResidualCoordinates
