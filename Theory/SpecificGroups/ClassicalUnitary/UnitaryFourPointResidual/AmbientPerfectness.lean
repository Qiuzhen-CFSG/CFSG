module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Levi
import all Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual

/-!
# Ambient perfectness of antidiagonal SU₄ in characteristic two

The plane Levi SL₂ over the quadratic extension is perfect, including when
its field has order four. Its upper root and a coordinate conjugate supply
both point-radical root groups. The radical center consists of commutators;
coordinate conjugation carries these central transvections to the two middle
SL₂ root groups. Thus the actual vector stabilizer lies in the ambient
derived subgroup, even when that stabilizer itself is solvable. The existing
point-parabolic and adjacent-swap generation proves ambient perfectness.

This internal extension reuses the private radical coordinates of
UnitaryFourPointResidual without changing that module’s public boundary.
It removes the binary fixed-field restriction in the exterior-square
SU₄/Ω₆⁻ comparison used by Aschbacher–Smith A.2.18 and Theorem D.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
open UnitaryFourGeneration UnitaryFourPointResidual
open scoped commutatorElement
noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual.AmbientPerfectness
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "G" => SU F (form F σ hσ)
local notation "L" => localSU F (form F σ hσ)
local notation "R" => radical F σ hσ
local notation "D" => commutator G

omit [Finite F] in
private theorem rootY_eq_levi (y : F) :
    (rootY F σ hσ y).val.val = UnitaryFourPlaneRadical.leviSU F σ hσ
      (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (σ y)) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootY,radicalOfCoordinates,radicalElement,radicalMatrix,
      UnitaryFourPlaneRadical.leviSU,UnitaryFourPlaneRadical.leviMatrix,
      SpecialLinearGroup.transvection_coe]
  exact (hσ y).symm

private theorem rootX_conjugate (x : F) :
    middleSwap F σ hσ * (rootY F σ hσ x).val.val * (middleSwap F σ hσ)⁻¹ =
      (rootX F σ hσ x).val.val := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  change middleSwapMatrix F * radicalMatrix F σ ⟨0,x,0,by simp⟩ =
    radicalMatrix F σ ⟨x,0,0,by simp⟩ * middleSwapMatrix F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleSwapMatrix,radicalMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

omit [Finite F] in
private theorem center_mem_ambient_commutator (hnt : ∃ x, σ x ≠ x)
    (t : FixedBy.subfield F σ) : (centralElement F σ hσ t).val.val ∈ D := by
  have hc : centralElement F σ hσ t ∈ Subgroup.center R := by
    rw [mem_center_radical_iff F σ hσ hnt]
    exact ⟨rfl,rfl⟩
  obtain ⟨b,c,hbc⟩ := center_radical_exists_commutator F σ hσ hnt _ hc
  let f : R →* G := (L).subtype.comp (R).subtype
  change f (centralElement F σ hσ t) ∈ D
  rw [← hbc,map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem planeLevi_mem_ambient_commutator (hnt : ∃ x, σ x ≠ x)
    (A : SpecialLinearGroup (Fin 2) F) :
    UnitaryFourPlaneRadical.leviSU F σ hσ A ∈ D := by
  obtain ⟨a,ha⟩ := hnt
  have ha0 : a ≠ 0 := by intro h; subst a; exact ha (map_zero σ)
  have ha1 : a ≠ 1 := by intro h; subst a; exact ha (map_one σ)
  have ha2 : a^2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact ha1 h
    · exact ha1 (by simpa only [CharTwo.neg_eq] using h)
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) := ⟨Matrix.SL2.commutator_eq_top ha0 ha2⟩
  let f : SpecialLinearGroup (Fin 2) F →* G :=
    (UnitaryFourPlaneLocal.localFactor F (form F σ hσ)).subtype.comp
      (UnitaryFourPlaneRadical.levi F σ hσ)
  have hm := map_derivedSeries_le_derivedSeries f 1
  rw [derivedSeries_one,derivedSeries_one,Group.IsPerfect.commutator_eq_top] at hm
  exact hm ⟨A,Subgroup.mem_top _,rfl⟩

private theorem radical_mem_ambient_commutator (hnt : ∃ x, σ x ≠ x) (r : R) : r.val.val ∈ D := by
  have hy (y : F) : (rootY F σ hσ y).val.val ∈ D := by
    rw [rootY_eq_levi]
    exact planeLevi_mem_ambient_commutator F σ hσ hnt _
  have hx (x : F) : (rootX F σ hσ x).val.val ∈ D := by
    rw [← rootX_conjugate]
    exact (inferInstance : (D).Normal).conj_mem _ (hy x) _
  let c := coordinatesOfRadical F σ hσ r
  let t := (radicalParametersEquiv F σ hσ c).2.2
  have he : rootY F σ hσ c.y * rootX F σ hσ c.x * centralElement F σ hσ t = r := by
    apply coord_ext F σ hσ
    · simp only [(coord_mul F σ hσ _ _).1]
      change 0+c.x+0 = c.x
      simp
    · simp only [(coord_mul F σ hσ _ _).2.1]
      change c.y+0+0 = c.y
      simp
    · simp only [(coord_mul F σ hσ _ _).2.2,
        (coord_mul F σ hσ _ _).1,(coord_mul F σ hσ _ _).2.1]
      change (0+0+σ c.y*c.x+σ 0*0)+(c.z+c.x*σ c.y)+σ (c.y+0)*0+σ (0+c.x)*0 = c.z
      simp [mul_comm,add_left_comm,CharTwo.add_self_eq_zero]
  have hh := congrArg (fun a : R => a.val.val) he
  change (rootY F σ hσ c.y).val.val * (rootX F σ hσ c.x).val.val *
    (centralElement F σ hσ t).val.val = r.val.val at hh
  rw [← hh]
  exact (D).mul_mem ((D).mul_mem (hy c.y) (hx c.x)) (center_mem_ambient_commutator F σ hσ hnt t)

private theorem central_conjugate_upper (t : FixedBy.subfield F σ) :
    pairSwap F σ hσ * (centralElement F σ hσ t).val.val * (pairSwap F σ hσ)⁻¹ =
      (leviSL F σ hσ (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t)).val := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  change pairSwapMatrix F * radicalMatrix F σ ⟨0,0,t,_⟩ =
    (leviSL F σ hσ _).val.val.val * pairSwapMatrix F
  rw [leviSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSwapMatrix,radicalMatrix,UnitaryFourPointQuotient.leviMatrix,
      SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem middle_upper_conjugate_lower (t : FixedBy.subfield F σ) :
    middleSwap F σ hσ *
      (leviSL F σ hσ (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t)).val *
      (middleSwap F σ hσ)⁻¹ =
      (leviSL F σ hσ (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t)).val := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  change middleSwapMatrix F * (leviSL F σ hσ _).val.val.val =
    (leviSL F σ hσ _).val.val.val * middleSwapMatrix F
  rw [leviSL_val,leviSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleSwapMatrix,UnitaryFourPointQuotient.leviMatrix,
      SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem middleLevi_mem_ambient_commutator (hnt : ∃ x, σ x ≠ x)
    (A : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) : (leviSL F σ hσ A).val ∈ D := by
  apply Matrix.SL2.transvection_induction (fun A => (leviSL F σ hσ A).val ∈ D) ?_ ?_ A
  · intro i j hij t
    have hu : (leviSL F σ hσ (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t)).val ∈ D := by
      rw [← central_conjugate_upper]
      exact (inferInstance : (D).Normal).conj_mem _ (center_mem_ambient_commutator F σ hσ hnt t) _
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hu
    · rw [← middle_upper_conjugate_lower]
      exact (inferInstance : (D).Normal).conj_mem _ hu _
    · exact False.elim (hij rfl)
  · intro A B hA hB
    simpa only [map_mul,Subgroup.coe_mul] using (D).mul_mem hA hB

private theorem local_mem_ambient_commutator (hnt : ∃ x, σ x ≠ x) (g : L) : g.val ∈ D := by
  let l := leviSL F σ hσ (middleSL F σ hσ g)
  have hr : g*l⁻¹ ∈ R := by
    rw [← middleSU_ker]
    apply (middleEquivSL F σ hσ).injective
    rw [map_one]
    change middleSL F σ hσ (g*l⁻¹) = 1
    simp [l]
  have hd := radical_mem_ambient_commutator F σ hσ hnt ⟨g*l⁻¹,hr⟩
  have hl := middleLevi_mem_ambient_commutator F σ hσ hnt (middleSL F σ hσ g)
  have hh := (D).mul_mem hd hl
  change (g.val*l.val⁻¹)*l.val ∈ D at hh
  simpa only [inv_mul_cancel_right] using hh

/-- The actual antidiagonal special unitary group is perfect, including SU₄(2). -/
public theorem antidiagonal_isPerfect (hnt : ∃ x, σ x ≠ x) : Group.IsPerfect G := by
  have hP : pointParabolicSU F (form F σ hσ) ≤ D := by
    intro g hg
    obtain ⟨h1,h2,h3⟩ := (mem_pointParabolicSU F _ g).mp hg
    have ht : g.val.val 0 0 ≠ 0 := by
      intro ht
      apply GeneralLinearGroup.det_ne_zero g.val
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro i
      fin_cases i <;> assumption
    let A := SpecialLinearGroup.diag2 (g.val.val 0 0)⁻¹ (inv_ne_zero ht)
    let l := UnitaryFourPlaneRadical.leviSU F σ hσ A
    have hl : g*l ∈ L := by
      rw [mem_localSU]
      change (g.val.val * UnitaryFourPlaneRadical.leviMatrix F σ A) 0 0 = 1 ∧
        (g.val.val * UnitaryFourPlaneRadical.leviMatrix F σ A) 1 0 = 0 ∧
        (g.val.val * UnitaryFourPlaneRadical.leviMatrix F σ A) 2 0 = 0 ∧
        (g.val.val * UnitaryFourPlaneRadical.leviMatrix F σ A) 3 0 = 0
      simp [UnitaryFourPlaneRadical.leviMatrix,A,SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply,Fin.sum_univ_succ,h1,h2,h3,mul_inv_cancel₀ ht]
    exact ((D).mul_mem_cancel_right (planeLevi_mem_ambient_commutator F σ hσ hnt A)).mp
      (local_mem_ambient_commutator F σ hσ hnt ⟨g*l,hl⟩)
  have hs : pairSwap F σ hσ ∈ D := by
    let A : SpecialLinearGroup (Fin 2) F := ⟨!![0,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
    have he : UnitaryFourPlaneRadical.leviSU F σ hσ A = pairSwap F σ hσ := by
      apply Subtype.ext
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [UnitaryFourPlaneRadical.leviSU,UnitaryFourPlaneRadical.leviMatrix,
          A,pairSwap,involutionElement,pairSwapMatrix]
    exact he ▸ planeLevi_mem_ambient_commutator F σ hσ hnt A
  exact ⟨eq_top_of_point_and_pairSwap F σ hσ D hP hs⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual.AmbientPerfectness
