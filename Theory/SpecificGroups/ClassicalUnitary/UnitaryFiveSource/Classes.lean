module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.HermitianAction
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOrbits
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortConjugacy

/-!
# The two native involution classes of PSU₅(4)

The full GL₂ Levi acts on central plane parameters by Hermitian congruence.
The existing SL₂ normalization sends every nonzero block to diag(1,det),
and a fixed-field square root normalizes every nonzero determinant to one.
Thus the plane-core center has two parabolic types. Their displacement
spaces are respectively the standard line and plane, so they do not fuse
in the full projective group. Conjugacy of involutory SU lifts is reflected
by the projective map using its actual scalar kernel of order five.

The model and marked-source companions combine these calculations with the
proved placement of all native involutions in the plane-core center.
Source: Aschbacher–Smith F.4.27(3), F.4.29 and F.4.35, printed pp.288–292.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem block_central_conjugation (A : GL (Fin 2) F)
    (u v : Parameters J) (hu : u.x = 0) (hv : v.x = 0)
    (hz : v.z = A.val * u.z * planeAdjoint J A.val) :
    planeBlockMatrix J A * matrix u * planeBlockInvMatrix J A = matrix v := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) (planeBlock_mul_inv J A)
  fin_cases i <;> fin_cases j <;>
    simp [matrix,planeBlockMatrix,planeBlockInvMatrix,planeAdjoint,
      Matrix.mul_apply,Fin.sum_univ_succ,hu,hv,hz] at h ⊢ <;>
    exact h

theorem central_planeLevi_conjugation (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (A : GL (Fin 2) F)
    (u v : Parameters J) (hu : u.x = 0) (hv : v.x = 0)
    (hz : v.z = A.val * u.z * planeAdjoint J A.val) :
    planeLeviParabolic J c hc hJ A * toParabolic hJ u *
      (planeLeviParabolic J c hc hJ A)⁻¹ = toParabolic hJ v := by
  have hb : planeBlockGL J A * toGL u * (planeBlockGL J A)⁻¹ = toGL v :=
    Units.ext (block_central_conjugation J A u v hu hv hz)
  have he := congrArg (MulAut.conj (planeBasisGL c)) hb
  simp only [map_mul,map_inv] at he
  change planeLeviGL J c A * (planeBasisGL c * toGL u * (planeBasisGL c)⁻¹) *
    (planeLeviGL J c A)⁻¹ = planeBasisGL c * toGL v * (planeBasisGL c)⁻¹ at he
  rw [←ambientGL_eq_planeBasis c,←ambientGL_eq_planeBasis c] at he
  have hs : planeLeviStabilizer J c hc hJ A * toStabilizer hJ u *
      (planeLeviStabilizer J c hc hJ A)⁻¹ = toStabilizer hJ v :=
    Subtype.ext (Subtype.ext he)
  exact congrArg ((project J).subgroupMap (specialStabilizer J (plane F))) hs



/-- The diagonal central parameter with leading entry one. -/
def diagonalParameter (b : F) (hb : J.conj b = b) : Parameters J where
  x := 0
  z := !![1,0;0,b]
  relation i j := by
    fin_cases i <;> fin_cases j <;> simp [hb,CharTwo.add_self_eq_zero]

open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel

theorem central_normalize [Finite F] (c : F) (hc : c + J.conj c = 1)
    (hconj : ∀ a, J.conj a = a ^ 4) (e : F ≃+* Field 2)
    (u : Parameters J) (hu : u.x = 0) (hne : u ≠ 1) :
    ∃ (A : SpecialLinearGroup (Fin 2) F) (b : F) (hb : J.conj b = b),
      planeAction A u = diagonalParameter J b hb := by
  let ec := centerHermitianEquiv J c hc hconj e
  let z : center (Parameters J) := ⟨u,mem_center_of_x_eq_zero J u hu⟩
  let X := (ec z).toAdd
  have hX : X ≠ 0 := by
    intro hz
    have he : ec z = 1 := Multiplicative.toAdd.injective hz
    exact hne (congrArg Subtype.val (ec.injective (he.trans ec.map_one.symm)))
  obtain ⟨A,hA⟩ := ClassicalUnitary.SourceNormalizer.FourOrbits.normalize 2 X hX
  let B := SpecialLinearGroup.map e.symm.toRingHom A
  have hB : SpecialLinearGroup.map e.toRingHom B = A := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply _
  let b := e.symm (form 2 X).val
  have hb : J.conj b = b := by
    apply e.injective
    rw [field_conjugation J hconj e,e.apply_symm_apply]
    exact (form 2 X).property
  refine ⟨B,b,hb,ext ?_ ?_⟩
  · simp only [planeAction_x,hu,Matrix.mulVec_zero,diagonalParameter]
  · have he := centerHermitianEquiv_planeAction J c hc hconj e B z
    rw [hB] at he
    have hm := congrArg (fun v : Multiplicative (Space 2) => v.toAdd.val) he
    change ((planeAction B u).z).map e = (action 2 A X).val at hm
    rw [hA] at hm
    ext i j
    apply e.injective
    have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Field 2) => M i j) hm
    fin_cases i <;> fin_cases j <;>
      simpa [ClassicalUnitary.SourceNormalizer.FourOrbits.representative,
        coordinates_symm_val,diagonalParameter,b] using hij

private def diagonalGL (s : F) (hs : s ≠ 0) : GL (Fin 2) F :=
  ⟨!![1,0;0,s],!![1,0;0,s⁻¹],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,hs],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,hs]⟩

/-- The full plane Levi merges all nonzero determinant fibers. -/
theorem diagonal_conjugate [Finite F] (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (b : F) (hb : J.conj b = b) (hbn : b ≠ 0) :
    IsConj (toParabolic hJ (diagonalParameter J b hb))
      (toParabolic hJ (diagonalParameter J 1 (map_one _))) := by
  obtain ⟨s,hs⟩ := (Finite.surjective_of_injective
    (fun a b (h : a^2 = b^2) => CharTwo.sq_injective h)) b⁻¹
  change s ^ 2 = b⁻¹ at hs
  have hs0 : s ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide)] at hs
    exact inv_ne_zero hbn hs.symm
  have hsf : J.conj s = s := by
    apply CharTwo.sq_injective
    change (J.conj s)^2 = s^2
    rw [←map_pow,hs,map_inv₀,hb]
  refine isConj_iff.mpr ⟨planeLeviParabolic J c hc hJ (diagonalGL s hs0),?_⟩
  apply central_planeLevi_conjugation J c hc hJ _ _ _ rfl rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalParameter,diagonalGL,planeAdjoint,Matrix.mul_apply,Fin.sum_univ_two,hsf]
  rw [mul_right_comm,←pow_two,hs,inv_mul_cancel₀ hbn]

/-- Nonidentity elements of the plane-core center have just two plane-parabolic types. -/
theorem central_two_types [Finite F] (c : F) (hc : c + J.conj c = 1)
    (hconj : ∀ a, J.conj a = a ^ 4) (e : F ≃+* Field 2) (hJ : J.form = 1)
    (u : Parameters J) (hu : u.x = 0) (hne : u ≠ 1) :
    IsConj (toParabolic hJ u) (toParabolic hJ (diagonalParameter J 0 (map_zero _))) ∨
      IsConj (toParabolic hJ u) (toParabolic hJ (diagonalParameter J 1 (map_one _))) := by
  obtain ⟨A,b,hb,he⟩ := central_normalize J c hc hconj e u hu hne
  have hh : IsConj (toParabolic hJ u) (toParabolic hJ (diagonalParameter J b hb)) :=
    isConj_iff.mpr ⟨planeSLParabolic J c hc hJ A,he ▸ planeSLParabolic_conjugation c hc hJ A u⟩
  by_cases hz : b = 0
  · subst b
    exact Or.inl hh
  · exact Or.inr (hh.trans (diagonal_conjugate J c hc hJ b hb hz))

end Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters

namespace Theory.SpecificGroups.UnitaryFive.InvolutionGeometry
open PlaneCore PlaneCore.Parameters
variable {F : Type*} [Field F] [CharP F 2] [Finite F] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem project_injective_on_involutions (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (A B : J.specialSubgroup) (hA : A^2 = 1) (hB : B^2 = 1)
    (he : project J A = project J B) : A = B := by
  have hfour : B^4=1 := by rw [show 4=2*2 by decide,pow_mul,hB,one_pow]
  have hc : Commute A B := RadicalCentralizers.commute_of_project_commute_fourth_power J hconj hcard
    (by rw [he]) hfour
  let C := A * B⁻¹
  have hker : C ∈ (project J).ker := by simp [C,MonoidHom.mem_ker,he]
  have htwo : C^2=1 := by rw [hc.inv_right.mul_pow,hA,inv_pow,hB]; simp
  have hfive : C^5=1 := by
    have hh := pow_card_eq_one' (x := (⟨C,hker⟩ : (project J).ker))
    rw [card_project_kernel J hconj hcard] at hh
    exact congrArg Subtype.val hh
  have hC : C=1 := calc
    C = (C^2)^2*C := by rw [htwo]; simp
    _ = C^5 := by group
    _ = 1 := hfive
  exact mul_inv_eq_one.mp hC

omit [CharP F 2] in
/-- Conjugacy of involutory SU lifts is reflected by the actual projective map. -/
theorem project_isConj_involutions (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (A B : J.specialSubgroup) (hA : A^2 = 1) (hB : B^2 = 1) :
    IsConj (project J A) (project J B) ↔ IsConj A B := by
  constructor
  · intro h
    obtain ⟨g,hg⟩ := isConj_iff.mp h
    obtain ⟨a,rfl⟩ := project_surjective J g
    exact isConj_iff.mpr ⟨a,project_injective_on_involutions J hcard hconj _ B
      (by rw [conj_pow,hA]; simp) hB (by simpa only [map_mul,map_inv] using hg)⟩
  · exact (project J).map_isConj

omit [CharP F 2] [Finite F] in
private theorem displacement_conjugate_le (a b g : J.specialSubgroup)
    (h : g*a*g⁻¹=b) :
    (displacement J a).map (linearAction J g).toLinearMap ≤ displacement J b := by
  rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
  refine ⟨linearAction J g v,?_⟩
  change linearAction J b (linearAction J g v) - linearAction J g v =
    linearAction J g (linearAction J a v-v)
  rw [map_sub]
  have he : b*g=g*a := by rw [←h]; group
  have hh := congrArg (fun x => linearAction J x v) he
  simpa only [map_mul,LinearEquiv.mul_apply] using
    congrArg (fun w => w-linearAction J g v) hh

omit [CharP F 2] [Finite F] in
/-- The displacement rank is an invariant of actual SU conjugacy. -/
theorem displacement_finrank_isConj (a b : J.specialSubgroup) (h : IsConj a b) :
    Module.finrank F (displacement J a) = Module.finrank F (displacement J b) := by
  have hle (a b : J.specialSubgroup) (h : IsConj a b) :
      Module.finrank F (displacement J a) ≤ Module.finrank F (displacement J b) := by
    obtain ⟨g,hg⟩ := isConj_iff.mp h
    have hh := Submodule.finrank_mono (displacement_conjugate_le J a b g hg)
    rwa [LinearEquiv.finrank_map_eq] at hh
  exact Nat.le_antisymm (hle a b h) (hle b a h.symm)

omit [Finite F] in
theorem longParameter_displacement (hJ : J.form = 1) :
    displacement J (toSU hJ (diagonalParameter J 0 (map_zero _))) = line F := by
  have he (v : Fin 5 → F) :
      linearAction J (toSU hJ (diagonalParameter J 0 (map_zero _))) v - v =
        ![v 0+v 1,v 0+v 1,0,0,0] := by
    change (ambientGL (diagonalParameter J 0 (map_zero _))).val *ᵥ v-v = _
    rw [ambientGL_val]
    ext i
    fin_cases i <;>
      simp [ambientMatrix,diagonalParameter,dotProduct,Fin.sum_univ_succ] <;> ring
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    change linearAction J (toSU hJ (diagonalParameter J 0 (map_zero _))) v-v ∈ line F
    rw [he]
    exact ⟨rfl,rfl,rfl,rfl⟩
  · intro v hv
    refine ⟨![v 0,0,0,0,0],?_⟩
    change linearAction J (toSU hJ (diagonalParameter J 0 (map_zero _)))
      ![v 0,0,0,0,0] - ![v 0,0,0,0,0] = v
    rw [he]
    change v 1=v 0 ∧ v 2=0 ∧ v 3=0 ∧ v 4=0 at hv
    ext i
    fin_cases i <;> simp [hv.1,hv.2.1,hv.2.2.1,hv.2.2.2]

/-- The two diagonal types cannot fuse in the full projective carrier. -/
theorem long_short_not_isConj (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    ¬ IsConj (toParabolic hJ (diagonalParameter J 0 (map_zero _))).val
      (toParabolic hJ (diagonalParameter J 1 (map_one _))).val := by
  intro h
  have hs (b : F) (hb : J.conj b = b) : (toSU hJ (diagonalParameter J b hb))^2=1 := by
    rw [←map_pow,(square_eq_one_iff J _).mpr rfl,map_one]
  have hh := displacement_finrank_isConj J _ _
    ((project_isConj_involutions J hcard hconj _ _ (hs 0 (map_zero _))
      (hs 1 (map_one _))).mp h)
  rw [longParameter_displacement J hJ,
    nonsingular_displacement_eq_plane J hJ _ rfl (by simp [diagonalParameter,Matrix.det_fin_two]),
    finrank_line,finrank_plane] at hh
  contradiction

end Theory.SpecificGroups.UnitaryFive.InvolutionGeometry
