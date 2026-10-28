module
public import Theory.SpecificGroups.SymplecticFour.TorusFixedUnipotent
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
import Mathlib.Tactic.FinCases

/-!
# A marked Weyl frame and Cartan centralizer for Sp₄

The two permutation reflections lie in the actual point and plane parabolics,
escape the other parabolic, and have product of order dividing four. Their
conjugation actions on both diagonal parameters are computed directly.
The native Borel centralizer of the whole diagonal torus is the torus: remove
the torus section of the two determinant characters and use the trivial
unipotent fixed subgroup. This includes the field of order four.

These are the native calculations for the Cartan/apartment recognition route
of Aschbacher–Smith F.4.10 and F.4.16, printed pp.279,282 of
`refs/quasithin.pdf`. The extension-completion consumer transports these exact
reflections and eliminates outer factors in the marked Borel centralizer.
-/

@[expose] public noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.WeylFrame
variable {F : Type*} [Field F] [CharP F 2]

/-- Reflection fixing the standard point and interchanging the second hyperbolic pair. -/
def pointReflection : Sp F := ⟨fromBlocks !![1,0;0,0] !![0,0;0,1]
    !![0,0;0,1] !![1,0;0,0], by
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [CharTwo.neg_eq, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]⟩

/-- Reflection fixing the standard plane and interchanging its two coordinate lines. -/
def planeReflection : Sp F := ⟨fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0], by
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [CharTwo.neg_eq, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]⟩

theorem pointReflection_mem : pointReflection (F := F) ∈ pointParabolic := by
  rw [mem_pointParabolic_iff]
  exact ⟨rfl,fun i => by fin_cases i <;> rfl⟩

theorem planeReflection_mem : planeReflection (F := F) ∈ planeParabolic := by
  rw [mem_planeParabolic_iff]
  exact fun _ _ => rfl

theorem pointReflection_not_mem : pointReflection (F := F) ∉ planeParabolic := by
  intro h
  exact one_ne_zero ((mem_planeParabolic_iff _).mp h 1 1)

theorem planeReflection_not_mem : planeReflection (F := F) ∉ pointParabolic := by
  intro h
  exact one_ne_zero ((mem_pointParabolic_iff _).mp h).1

theorem pointReflection_sq : pointReflection (F := F)^2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change (pointReflection (F := F)).val * pointReflection.val = (1 : Matrix _ _ F)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pointReflection, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem planeReflection_sq : planeReflection (F := F)^2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change (planeReflection (F := F)).val * planeReflection.val = (1 : Matrix _ _ F)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeReflection, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem pointReflection_torus (a b : Fˣ) :
    pointReflection * diagonalTorus a b * pointReflection = diagonalTorus a b⁻¹ := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pointReflection, diagonalTorus, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem planeReflection_torus (a b : Fˣ) :
    planeReflection * diagonalTorus a b * planeReflection = diagonalTorus b a := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeReflection, diagonalTorus, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem rotation_four : (pointReflection (F := F) * planeReflection)^4=1 := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pow_succ, pointReflection, planeReflection, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

variable [Finite F]
/-- The full Borel centralizer of the diagonal torus is the diagonal torus. -/
theorem borel_inf_centralizer_torus (hq : 2 < Nat.card F) :
    borel (F := F) ⊓ centralizer ((CentralRootGeometry.diagonalTorusHom (F := F)).range : Set (Sp F)) =
      (CentralRootGeometry.diagonalTorusHom (F := F)).range := by
  let D := (CentralRootGeometry.diagonalTorusHom (F := F)).range
  have hc : D ≤ centralizer (D : Set (Sp F)) := by
    rintro x ⟨p,rfl⟩ y ⟨q,rfl⟩
    rw [←map_mul,←map_mul,mul_comm]
  have hB : D ≤ borel := by
    rintro x ⟨⟨a,b⟩,rfl⟩
    exact diagonalTorus_mem_borel a b
  apply le_antisymm
  · rintro g ⟨hg,hgc⟩
    let b : borel (F := F) := ⟨g,hg⟩
    let t := EvenBorelTorus.torusSection (borelCharacters b)
    have ht : t.val ∈ D := ⟨((borelCharacters b).1,(borelCharacters b).1⁻¹ * (borelCharacters b).2),rfl⟩
    have hu : (b*t⁻¹).val ∈ unipotent := by
      apply (borelCharacters_eq_one _).mp
      rw [map_mul,map_inv,EvenBorelTorus.characters_torusSection,mul_inv_cancel]
    have huc : (b*t⁻¹).val ∈ centralizer (D : Set (Sp F)) :=
      (centralizer (D : Set (Sp F))).mul_mem hgc ((centralizer _).inv_mem (hc ht))
    have he : (b*t⁻¹).val = 1 := mem_bot.mp
      ((CentralRootGeometry.unipotent_torus_fixed_eq_bot hq).le ⟨hu,huc⟩)
    have hbt : b=t := mul_inv_eq_one.mp (Subtype.ext he)
    change b.val ∈ D
    rw [hbt]
    exact ht
  · exact le_inf hB hc
end Theory.SpecificGroups.SymplecticFour.WeylFrame
