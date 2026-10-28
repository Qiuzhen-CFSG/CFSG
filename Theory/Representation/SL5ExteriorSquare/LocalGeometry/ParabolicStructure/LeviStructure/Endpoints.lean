module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.Shears

/-!
# Perfect endpoint parabolics and the source hyperplane radical

Every allowed transvection of a line or hyperplane parabolic is a commutator
[tᵢₛ,tₛⱼ] inside that same parabolic. Their block-generation theorem therefore
proves perfection, so each endpoint equals its terminal derived subgroup and
its join with the flag group. In the hyperplane case, the identity-block kernel
is exactly the previously defined last-column shear subgroup.

This proves the group equalities in clauses (3) and (4) of Aschbacher–Smith,
Lemma 12.5.2, printed p.817/PDF p.834, including R₆ = O₂(L₆T).
The natural and orthogonal module identifications are separate assertions.
-/

@[expose] public section



namespace Representation.SL5ExteriorSquare
open SL5TenDimensional Subgroup
open scoped commutatorElement

private theorem elementary_commutator (i s j : Fin 5)
    (his : i ≠ s) (hsj : s ≠ j) (hij : i ≠ j) :
    ⁅elementary i s, elementary s j⁆ = elementary i j := by
  rw [commutatorElement_def,
    inv_eq_of_mul_eq_one_left (elementary_square i s),
    inv_eq_of_mul_eq_one_left (elementary_square s j)]
  calc
    elementary i s * elementary s j * elementary i s * elementary s j =
        (elementary i s * (elementary s j * elementary i s)) * elementary s j := by
      simp only [mul_assoc]
    _ = (elementary s j * elementary i j) * elementary s j := by
      rw [elementary_steinberg i s j his hsj hij]
    _ = elementary i j := by
      rw [elementary_commute s j i j hsj hij.symm, mul_assoc,
        elementary_square, mul_one]

private theorem endpoint_intermediate (k : ℕ) (hk : k = 1 ∨ k = 4)
    (i j : Fin 5) (hij : i ≠ j) (hp : j.val < k → i.val < k) :
    ∃ s : Fin 5, i ≠ s ∧ s ≠ j ∧ (s.val < k → i.val < k) ∧
      (j.val < k → s.val < k) := by
  rcases hk with rfl | rfl
  · exact (by decide : ∀ i j : Fin 5, i ≠ j → (j.val < 1 → i.val < 1) →
      ∃ s : Fin 5, i ≠ s ∧ s ≠ j ∧ (s.val < 1 → i.val < 1) ∧
        (j.val < 1 → s.val < 1)) i j hij hp
  · exact (by decide : ∀ i j : Fin 5, i ≠ j → (j.val < 4 → i.val < 4) →
      ∃ s : Fin 5, i ≠ s ∧ s ≠ j ∧ (s.val < 4 → i.val < 4) ∧
        (j.val < 4 → s.val < 4)) i j hij hp

private theorem endpoint_isPerfect (k : ℕ) (hk : k = 1 ∨ k = 4) :
    Group.IsPerfect (parabolic k) := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm (parabolic k).commutator_le_self
  conv_lhs => rw [parabolic_eq_closure_transvections]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, j, hij, c, hp, rfl⟩
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp
  have hm (a b : Fin 5) (hab : a ≠ b) (hp : b.val < k → a.val < k) :
      elementary a b ∈ parabolic k := by
    rw [parabolic_eq_closure_transvections]
    apply Subgroup.subset_closure
    exact ⟨a, b, hab, 1, hp, by simp [elementary, hab]⟩
  obtain ⟨s, his, hsj, hpi, hpj⟩ := endpoint_intermediate k hk i j hij hp
  have hc := commutator_mem_commutator (hm i s his hpi) (hm s j hsj hpj)
  rw [elementary_commutator i s j his hsj hij] at hc
  simpa [elementary, hij] using hc

instance parabolic_one_isPerfect : Group.IsPerfect (parabolic 1) :=
  endpoint_isPerfect 1 (Or.inl rfl)

instance parabolic_four_isPerfect : Group.IsPerfect (parabolic 4) :=
  endpoint_isPerfect 4 (Or.inr rfl)

@[simp] theorem parabolicResidual_one : parabolicResidual 1 = parabolic 1 := by
  rw [parabolicResidual, Subgroup.solvableResidual_eq_top,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

@[simp] theorem parabolicResidual_four : parabolicResidual 4 = parabolic 4 := by
  rw [parabolicResidual, Subgroup.solvableResidual_eq_top,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

@[simp] theorem parabolicResidualFlag_one : parabolicResidualFlag 1 = parabolic 1 := by
  rw [parabolicResidualFlag, parabolicResidual_one,
    sup_eq_left.mpr (flagGroup_le_parabolic 1 (by decide))]

@[simp] theorem parabolicResidualFlag_four : parabolicResidualFlag 4 = parabolic 4 := by
  rw [parabolicResidualFlag, parabolicResidual_four,
    sup_eq_left.mpr (flagGroup_le_parabolic 4 (by decide))]
end Representation.SL5ExteriorSquare

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private theorem shear_upperLeft (u : ShearParameter) (i j : Fin 4) :
    (shear u).val i.castSucc j.castSucc = (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j := by
  rw [matrix_shear]
  fin_cases i <;> fin_cases j <;> rfl

private theorem shear_lowerLeft (u : ShearParameter) (j : Fin 4) :
    (shear u).val 4 j.castSucc = 0 := by
  rw [matrix_shear]
  fin_cases j <;> rfl

private theorem shear_upperRight (u : ShearParameter) (i : Fin 4) :
    (shear u).val i.castSucc 4 = u i := by
  rw [matrix_shear]
  fin_cases i <;> rfl

private theorem shear_lowerRight (u : ShearParameter) : (shear u).val 4 4 = 1 := by
  rw [matrix_shear]
  rfl

theorem parabolicUnipotent_four_eq_shearSubgroup : parabolicUnipotent 4 = shearSubgroup := by
  rw [← parabolic_twoCore_eq_unipotent]
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨ha, hd⟩ := (mem_parabolic_twoCore_iff 4 (by decide) x).mp hx
    have hz := (mem_parabolic_iff_lowerLeft_zero 4 x.val).mp x.property
    apply (mem_shearSubgroup _).mpr
    refine ⟨fun i => x.val.val i.castSucc 4, ?_⟩
    apply Subtype.ext
    ext i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · exact (shear_lowerRight _).trans (hd 0 0).symm
      · exact shear_upperRight _ i
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · exact (shear_lowerLeft _ j).trans (hz 4 j.castSucc (by decide) j.isLt).symm
      · rw [shear_upperLeft]
        exact (ha i j).symm
  · intro hg
    obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp hg
    have hp : shear u ∈ parabolic 4 := by
      apply (mem_parabolic_iff_lowerLeft_zero 4 _).mpr
      intro i j hi hj
      have hi4 : i = 4 := Fin.ext (by change i.val = 4; omega)
      subst i
      exact shear_lowerLeft u ⟨j.val, hj⟩
    refine ⟨⟨shear u, hp⟩, ?_, rfl⟩
    apply (mem_parabolic_twoCore_iff 4 (by decide) _).mpr
    constructor
    · intro i j
      exact shear_upperLeft u i j
    · intro i j
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
      subst i
      subst j
      exact shear_lowerRight u

@[simp] theorem parabolicResidualTwoCore_one :
    parabolicResidualTwoCore 1 = parabolicUnipotent 1 := by
  rw [parabolicResidualTwoCore, parabolicResidualFlag_one,
    parabolic_twoCore_eq_unipotent]

@[simp] theorem parabolicResidualTwoCore_four :
    parabolicResidualTwoCore 4 = shearSubgroup := by
  rw [parabolicResidualTwoCore, parabolicResidualFlag_four,
    parabolic_twoCore_eq_unipotent, parabolicUnipotent_four_eq_shearSubgroup]
end Representation.SL5ExteriorSquare
