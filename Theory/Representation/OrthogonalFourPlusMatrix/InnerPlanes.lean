module
public import Theory.Representation.OrthogonalFourPlusMatrix.SingularPlaneCentralizer
public import Mathlib.GroupTheory.Index

/-!
# Singular planes for inner tensor two-groups

Conjugate a containing Sylow subgroup of SL₂(4) × SL₂(4) to the two
upper-unipotent factors. On matrices with zero first column, only the
first factor acts; on matrices with zero second row, only the second
factor acts. Each action is detected by a quotient of order at most four,
and both displacement spaces lie in the same singular field line.
Conjugation transports this literal geometry to every inner two-group.

Source: Aschbacher–Smith 9.4.4–5, printed pp.736–737.
-/

@[expose] public noncomputable section
open Matrix Subgroup Representation Representation.BinaryOffender
open scoped Pointwise
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

def rowPlaneMap : (Fin 2 → F) →ₗ[ZMod 2] V where
  toFun v := !![v 0,v 1;0,0]
  map_add' a b := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a b := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp

def rowPlane : Submodule (ZMod 2) V := rowPlaneMap.range

private theorem upper_plane_displacement (g : G) (hg : g ∈ upperPairSylow)
    (v : V) (hv : v ∈ plane) : action g v - v ∈ point := by
  obtain ⟨x,rfl⟩ := hv
  obtain ⟨a,ha⟩ := hg.1
  obtain ⟨b,hb⟩ := hg.2
  refine ⟨a.toAdd * x 1,?_⟩
  rw [action_apply,←ha,←hb]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pointMap,planeMap,SpecialLinearGroup.upperUnipotentHom,
      SpecialLinearGroup.transvection_coe,SpecialLinearGroup.transvection_inv,
      Matrix.mul_apply,Fin.sum_univ_two]

private theorem upper_rowPlane_displacement (g : G) (hg : g ∈ upperPairSylow)
    (v : V) (hv : v ∈ rowPlane) : action g v - v ∈ point := by
  obtain ⟨x,rfl⟩ := hv
  obtain ⟨a,ha⟩ := hg.1
  obtain ⟨b,hb⟩ := hg.2
  refine ⟨-(x 0 * b.toAdd),?_⟩
  rw [action_apply,←ha,←hb]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pointMap,rowPlaneMap,SpecialLinearGroup.upperUnipotentHom,
      SpecialLinearGroup.transvection_coe,SpecialLinearGroup.transvection_inv,
      Matrix.mul_apply,Fin.sum_univ_two]

private theorem upper_plane_fixed_of_fst_eq_one (g : G) (hg : g ∈ upperPairSylow)
    (hfirst : g.1 = 1) (v : V) (hv : v ∈ plane) : action g v = v := by
  obtain ⟨x,rfl⟩ := hv
  obtain ⟨b,hb⟩ := hg.2
  rw [action_apply,hfirst,SpecialLinearGroup.coe_one,one_mul,←hb]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [planeMap,SpecialLinearGroup.upperUnipotentHom,
      SpecialLinearGroup.transvection_coe,SpecialLinearGroup.transvection_inv,
      Matrix.mul_apply,Fin.sum_univ_two]

private theorem upper_rowPlane_fixed_of_snd_eq_one (g : G) (hg : g ∈ upperPairSylow)
    (hsecond : g.2 = 1) (v : V) (hv : v ∈ rowPlane) : action g v = v := by
  obtain ⟨x,rfl⟩ := hv
  obtain ⟨a,ha⟩ := hg.1
  rw [action_apply,hsecond,inv_one,SpecialLinearGroup.coe_one,mul_one,←ha]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rowPlaneMap,SpecialLinearGroup.upperUnipotentHom,
      SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two]

private theorem upper_eq_one_of_planes_fixed (g : G) (hg : g ∈ upperPairSylow)
    (hplane : ∀ v ∈ plane, action g v = v)
    (hrow : ∀ v ∈ rowPlane, action g v = v) : g = 1 := by
  have hfirst := first_eq_one_of_plane_fixed g hplane
  obtain ⟨b,hb⟩ := hg.2
  have h := hrow (rowPlaneMap ![1,0]) ⟨![1,0],rfl⟩
  rw [action_apply,hfirst,SpecialLinearGroup.coe_one,one_mul,←hb] at h
  have he := congrArg (fun M : V => M 0 1) h
  have hb0 : b.toAdd = 0 := by
    simpa [rowPlaneMap,SpecialLinearGroup.upperUnipotentHom,
      SpecialLinearGroup.transvection_coe,SpecialLinearGroup.transvection_inv,
      Matrix.mul_apply,Fin.sum_univ_two] using he
  apply Prod.ext hfirst
  rw [←hb]
  simp [SpecialLinearGroup.upperUnipotentHom,hb0]

/-- Two singular planes whose inner two-group actions are detected by
quotients of order at most four. -/
structure InnerPlaneData {H : Type*} [Group H] (f : H →* G) where
  firstPlane : Submodule (ZMod 2) V
  secondPlane : Submodule (ZMod 2) V
  line : Submodule (ZMod 2) V
  line_card : Nat.card line = 4
  line_singular : ∀ v ∈ line, v.det = 0
  firstKernel : Subgroup H
  secondKernel : Subgroup H
  first_index : firstKernel.index ≤ 4
  second_index : secondKernel.index ≤ 4
  first_fixed : ∀ h ∈ firstKernel, ∀ v ∈ firstPlane, action (f h) v = v
  second_fixed : ∀ h ∈ secondKernel, ∀ v ∈ secondPlane, action (f h) v = v
  first_moved : ∀ h : H, ∀ v ∈ firstPlane, action (f h) v - v ∈ line
  second_moved : ∀ h : H, ∀ v ∈ secondPlane, action (f h) v - v ∈ line
  separate : ∀ h : H,
    (∀ v ∈ firstPlane, action (f h) v = v) →
    (∀ v ∈ secondPlane, action (f h) v = v) → f h = 1

private theorem action_mul_apply (g h : G) (v : V) :
    action (g*h) v = action g (action h v) :=
  congrArg (fun e : Module.End (ZMod 2) V => e v) (action.map_mul g h)

private theorem fixed_of_conjugated_fixed (x g : G) (v : V)
    (hf : action (x*g*x⁻¹) v = v) :
    action g (action x⁻¹ v) = action x⁻¹ v := by
  have hh := congrArg (action x⁻¹) hf
  rw [←action_mul_apply] at hh
  have he : x⁻¹*(x*g*x⁻¹) = g*x⁻¹ := by group
  rw [he,action_mul_apply] at hh
  exact hh

private theorem conjugated_fixed_of_fixed (x g : G) (v : V)
    (hf : action g (action x⁻¹ v) = action x⁻¹ v) :
    action (x*g*x⁻¹) v = v := by
  calc
    action (x*g*x⁻¹) v = action x (action g (action x⁻¹ v)) := by
      rw [action_mul_apply,action_mul_apply]
    _ = action x (action x⁻¹ v) := congrArg (action x) hf
    _ = v := by rw [←action_mul_apply,mul_inv_cancel,action.map_one]; rfl

private theorem conjugated_displacement (x g : G) (v : V) :
    action x⁻¹ (action (x*g*x⁻¹) v - v) =
      action g (action x⁻¹ v) - action x⁻¹ v := by
  rw [map_sub,←action_mul_apply]
  have he : x⁻¹*(x*g*x⁻¹) = g*x⁻¹ := by group
  rw [he,action_mul_apply]

/-- Every inner two-group has the actual pair of singular planes. -/
theorem exists_innerPlaneData {H : Type*} [Group H] [Finite H] (f : H →* G)
    (hH : IsPGroup 2 H) : Nonempty (InnerPlaneData f) := by
  have hrange : IsPGroup 2 f.range := hH.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨Q,hQ⟩ := hrange.exists_le_sylow
  obtain ⟨x,hx⟩ := MulAction.exists_smul_eq G Q upperPairSylow
  let q := (MulAut.conj x).toMonoidHom.comp f
  have hq (h : H) : q h ∈ upperPairSylow := by
    rw [←hx]
    change x * f h * x⁻¹ ∈ MulAut.conj x • (Q : Set G)
    exact ⟨f h,hQ ⟨h,rfl⟩,rfl⟩
  let f₁ := (MonoidHom.fst _ _).comp q
  let f₂ := (MonoidHom.snd _ _).comp q
  have hF : Nat.card F = 4 := by
    simpa only [Nat.card_eq_fintype_card] using Representation.SL2FourNatural.card_field
  have hindex₁ : f₁.ker.index ≤ 4 := by
    rw [index_ker]
    have hle : f₁.range ≤ SpecialLinearGroup.upperUnipotent F := by
      rintro _ ⟨h,rfl⟩
      exact (hq h).1
    have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    rw [SpecialLinearGroup.card_upperUnipotent,hF] at hc
    exact hc
  have hindex₂ : f₂.ker.index ≤ 4 := by
    rw [index_ker]
    have hle : f₂.range ≤ SpecialLinearGroup.upperUnipotent F := by
      rintro _ ⟨h,rfl⟩
      exact (hq h).2
    have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    rw [SpecialLinearGroup.card_upperUnipotent,hF] at hc
    exact hc
  refine ⟨{
    firstPlane := plane.map (action x⁻¹)
    secondPlane := rowPlane.map (action x⁻¹)
    line := point.map (action x⁻¹)
    line_card := ?_
    line_singular := ?_
    firstKernel := f₁.ker
    secondKernel := f₂.ker
    first_index := hindex₁
    second_index := hindex₂
    first_fixed := ?_
    second_fixed := ?_
    first_moved := ?_
    second_moved := ?_
    separate := ?_ }⟩
  · change Nat.card (point.map (linearAction x⁻¹).toLinearMap) = 4
    rw [Nat.card_congr ((linearAction x⁻¹).submoduleMap point).toEquiv.symm]
    exact card_point
  · rintro _ ⟨v,hv,rfl⟩
    rw [show (action x⁻¹ v).det = v.det from matrixAction_det x⁻¹ v]
    obtain ⟨c,rfl⟩ := hv
    simp [pointMap,Matrix.det_fin_two]
  · intro h hh
    rintro _ ⟨v,hv,rfl⟩
    have hfix := upper_plane_fixed_of_fst_eq_one (q h) (hq h) hh v hv
    exact fixed_of_conjugated_fixed x (f h) v hfix
  · intro h hh
    rintro _ ⟨v,hv,rfl⟩
    have hfix := upper_rowPlane_fixed_of_snd_eq_one (q h) (hq h) hh v hv
    exact fixed_of_conjugated_fixed x (f h) v hfix
  · intro h
    rintro _ ⟨v,hv,rfl⟩
    refine ⟨action (q h) v - v,upper_plane_displacement (q h) (hq h) v hv,?_⟩
    exact conjugated_displacement x (f h) v
  · intro h
    rintro _ ⟨v,hv,rfl⟩
    refine ⟨action (q h) v - v,upper_rowPlane_displacement (q h) (hq h) v hv,?_⟩
    exact conjugated_displacement x (f h) v
  · intro h hp hr
    have he : q h = 1 := upper_eq_one_of_planes_fixed (q h) (hq h)
      (fun v hv => conjugated_fixed_of_fixed x (f h) v (hp _ ⟨v,hv,rfl⟩))
      (fun v hv => conjugated_fixed_of_fixed x (f h) v (hr _ ⟨v,hv,rfl⟩))
    apply (MulAut.conj x).injective
    change q h = (MulAut.conj x) 1
    rw [map_one]
    exact he

/-- Choose the proved singular-plane geometry for an inner two-group. -/
def innerPlaneData {H : Type*} [Group H] [Finite H] (f : H →* G)
    (hH : IsPGroup 2 H) : InnerPlaneData f :=
  (exists_innerPlaneData f hH).some

end ClassicalOrthogonal.FourPlusMatrix.Binary
