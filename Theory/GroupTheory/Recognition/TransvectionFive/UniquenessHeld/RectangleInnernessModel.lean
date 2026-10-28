module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessHeld.IntersectionRigidity
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangles
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Cubic rigidity of the actual 2+1+2 matrix radical. -/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld.RectangleInnernessModel
open UniquenessLinear

private abbrev B := ZMod 2
private abbrev Vec := Fin 2 → B
private abbrev Mat := Matrix (Fin 2) (Fin 2) B

private structure R where
  u : Vec
  v : Vec
  e : Mat

private theorem R.ext {a b : R} (hu : a.u = b.u) (hv : a.v = b.v) (he : a.e = b.e) :
    a = b := by cases a; cases b; cases hu; cases hv; cases he; rfl

private instance : Mul R := ⟨fun a b =>
  ⟨a.u+b.u,a.v+b.v,fun i j => a.e i j+b.e i j+a.u i*b.v j⟩⟩
private instance : One R := ⟨⟨0,0,0⟩⟩
private instance : Inv R := ⟨fun a =>
  ⟨-a.u,-a.v,fun i j => -a.e i j+a.u i*a.v j⟩⟩
private instance : Group R where
  mul_assoc a b c := by
    apply R.ext
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · funext i j
      change (a.e i j+b.e i j+a.u i*b.v j)+c.e i j+(a.u i+b.u i)*c.v j =
        a.e i j+(b.e i j+c.e i j+b.u i*c.v j)+a.u i*(b.v j+c.v j)
      ring
  one_mul a := by
    apply R.ext
    · exact zero_add _
    · exact zero_add _
    · funext i j; change 0+a.e i j+0*a.v j=a.e i j; ring
  mul_one a := by
    apply R.ext
    · exact add_zero _
    · exact add_zero _
    · funext i j; change a.e i j+0+a.u i*0=a.e i j; ring
  inv_mul_cancel a := by
    apply R.ext
    · exact neg_add_cancel _
    · exact neg_add_cancel _
    · funext i j; change (-a.e i j+a.u i*a.v j)+a.e i j+(-a.u i)*a.v j=0; ring

private def U (u : Vec) : R := ⟨u,0,0⟩
private def V (v : Vec) : R := ⟨0,v,0⟩
private def E (e : Mat) : R := ⟨0,0,e⟩
private def α (a : R) : R :=
  ⟨![a.u 1,a.u 0+a.u 1],a.v,fun i j => ![a.e 1 j,a.e 0 j+a.e 1 j] i⟩
private def β (a : R) : R :=
  ⟨a.u,![a.v 0+a.v 1,a.v 0],fun i j => ![a.e i 0+a.e i 1,a.e i 0] j⟩

private theorem α_fixed (a : R) (h : α a = a) : a = V a.v := by
  have hu := congrArg R.u h
  have he := congrArg R.e h
  have hz (x y : B) (h₁ : y=x) (h₂ : x+y=y) : x=0 ∧ y=0 := by
    have h0 : x=0 := add_eq_right.mp h₂
    exact ⟨h0,h₁.trans h0⟩
  have hzu := hz (a.u 0) (a.u 1) (congrFun hu 0) (congrFun hu 1)
  apply R.ext
  · funext i; fin_cases i <;> first | exact hzu.1 | exact hzu.2
  · rfl
  · funext i j
    have hze := hz (a.e 0 j) (a.e 1 j) (congrFun (congrFun he 0) j)
      (congrFun (congrFun he 1) j)
    fin_cases i <;> first | exact hze.1 | exact hze.2

private theorem β_fixed (a : R) (h : β a = a) : a = U a.u := by
  have hv := congrArg R.v h
  have he := congrArg R.e h
  have hz (x y : B) (h₁ : x+y=x) (h₂ : x=y) : x=0 ∧ y=0 := by
    have h0 : y=0 := add_eq_left.mp h₁
    exact ⟨h₂.trans h0,h0⟩
  have hzv := hz (a.v 0) (a.v 1) (congrFun hv 0) (congrFun hv 1)
  apply R.ext
  · rfl
  · funext i; fin_cases i <;> first | exact hzv.1 | exact hzv.2
  · funext i j
    have hze := hz (a.e i 0) (a.e i 1) (congrFun (congrFun he i) 0)
      (congrFun (congrFun he i) 1)
    fin_cases j <;> first | exact hze.1 | exact hze.2

private theorem α_V (v : Vec) : α (V v) = V v := by
  apply R.ext
  · funext i; fin_cases i <;> simp [α,V]
  · rfl
  · funext i j; fin_cases i <;> simp [α,V]

private theorem β_U (u : Vec) : β (U u) = U u := by
  apply R.ext
  · rfl
  · funext i; fin_cases i <;> simp [β,U]
  · funext i j; fin_cases j <;> simp [β,U]

private theorem axis_commutator (u v : Vec) :
    U u * V v * (U u)⁻¹ * (V v)⁻¹ = E (fun i j => u i*v j) := by
  apply R.ext
  · funext i; change u i+0+-u i+ -0=0; ring
  · funext i; change 0+v i+ -0+ -v i=0; ring
  · funext i j
    change ((0+0+u i*v j)+(-0+u i*0)+(u i+0)*(-0))+
      (-0+0*v j)+(u i+0+-u i)*(-v j)=u i*v j
    ring

private theorem R_decompose (a : R) : a = V a.v * U a.u * E a.e := by
  apply R.ext
  · funext i; change a.u i=0+a.u i+0; ring
  · funext i; change a.v i=a.v i+0+0; ring
  · funext i j; change a.e i j=(0+0+0*0)+a.e i j+(0+a.u i)*0; ring

private theorem coordinate_rigidity (f : R →* R)
    (hE : ∀ e, f (E e) = E e)
    (hα : ∀ a, f (α a) = α (f a))
    (hβ : ∀ a, f (β a) = β (f a)) : f = MonoidHom.id R := by
  have hU (u : Vec) : f (U u) = U (f (U u)).u := β_fixed _ (by rw [←hβ,β_U])
  have hV (v : Vec) : f (V v) = V (f (V v)).v := α_fixed _ (by rw [←hα,α_V])
  have ht (u v : Vec) (i j : Fin 2) :
      (f (U u)).u i * (f (V v)).v j = u i*v j := by
    have hh := congrArg f (axis_commutator u v)
    simp only [map_mul,map_inv] at hh
    rw [hU,hV,axis_commutator] at hh
    have hh' := hh.trans (hE (fun i j => u i*v j))
    exact congrFun (congrFun (congrArg R.e hh') i) j
  let w : Vec := ![1,0]
  have hw := ht w w 0 0
  have hwU : (f (U w)).u 0=1 := by
    exact (by decide : ∀ x y : B, x*y=1 → x=1) _ _ hw
  have hwV : (f (V w)).v 0=1 := by
    exact (by decide : ∀ x y : B, x*y=1 → y=1) _ _ hw
  have hUf (u : Vec) : f (U u) = U u := by
    rw [hU]
    congr 1
    funext i
    simpa only [hwV,mul_one,show w 0=1 from rfl] using ht u w i 0
  have hVf (v : Vec) : f (V v) = V v := by
    rw [hV]
    congr 1
    funext j
    simpa only [hwU,one_mul,show w 0=1 from rfl] using ht w v 0 j
  ext a
  conv_lhs => rw [R_decompose a]
  rw [map_mul,map_mul,hVf,hUf,hE]
  exact (R_decompose a).symm

private def embedFun (a : R) : SL :=
  RectangleCoordinates.word3 ![0,0,0,0,a.v 0,a.v 1] *
    RectangleCoordinates.word2 ![a.u 0,a.e 0 0,a.e 0 1,a.u 1,a.e 1 0,a.e 1 1]

private theorem embed_matrix (a : R) : (embedFun a).val =
    1 + Matrix.single 0 2 (a.u 0) + Matrix.single 1 2 (a.u 1) +
      Matrix.single 2 3 (a.v 0) + Matrix.single 2 4 (a.v 1) +
      Matrix.single 0 3 (a.e 0 0) + Matrix.single 0 4 (a.e 0 1) +
      Matrix.single 1 3 (a.e 1 0) + Matrix.single 1 4 (a.e 1 1) := by
  simp only [embedFun,Matrix.SpecialLinearGroup.coe_mul,
    RectangleCoordinates.word2_val,RectangleCoordinates.word3_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single,Matrix.one_apply]

private def embed : R →* SL where
  toFun := embedFun
  map_one' := by apply Subtype.ext; rw [embed_matrix]; simp; rfl
  map_mul' a b := by
    apply Subtype.ext
    change (embedFun (a*b)).val=(embedFun a).val*(embedFun b).val
    rw [embed_matrix,embed_matrix,embed_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single,Matrix.one_apply]
    all_goals rfl

private theorem embed_injective : Function.Injective embed := by
  intro a b h
  have he : (embedFun a).val=(embedFun b).val := congrArg Subtype.val h
  rw [embed_matrix,embed_matrix] at he
  apply R.ext
  · funext i
    have hh := congrFun (congrFun he (if i=0 then 0 else 1)) 2
    fin_cases i <;> simpa [Matrix.single,Matrix.one_apply] using hh
  · funext i
    have hh := congrFun (congrFun he 2 (if i=0 then 3 else 4))
    fin_cases i <;> simpa [Matrix.single,Matrix.one_apply] using hh
  · funext i j
    have hh := congrFun (congrFun he (if i=0 then 0 else 1)) (if j=0 then 3 else 4)
    fin_cases i <;> fin_cases j <;> simpa [Matrix.single,Matrix.one_apply] using hh

/-- The original 2+1+2 matrix radical. -/
abbrev radical : Subgroup SL := Model.plane ⊔ Model.threeSpace

private theorem embed_range : embed.range = radical := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact radical.mul_mem (mem_sup_right (RectangleCoordinates.word3_mem _))
      (mem_sup_left (RectangleCoordinates.word2_mem _))
  · apply sup_le
    · rw [show Model.plane=rectangle 2 from rfl,←RectangleCoordinates.hom2_range]
      rintro _ ⟨v,rfl⟩
      refine ⟨⟨![v.toAdd 0,v.toAdd 3],0,!![v.toAdd 1,v.toAdd 2;v.toAdd 4,v.toAdd 5]⟩,?_⟩
      apply Subtype.ext
      change (embedFun _).val=(RectangleCoordinates.word2 v.toAdd).val
      rw [embed_matrix,RectangleCoordinates.word2_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.single,Matrix.one_apply]
    · rw [show Model.threeSpace=rectangle 3 from rfl,←RectangleCoordinates.hom3_range]
      rintro _ ⟨v,rfl⟩
      refine ⟨⟨0,![v.toAdd 4,v.toAdd 5],!![v.toAdd 0,v.toAdd 1;v.toAdd 2,v.toAdd 3]⟩,?_⟩
      apply Subtype.ext
      change (embedFun _).val=(RectangleCoordinates.word3 v.toAdd).val
      rw [embed_matrix,RectangleCoordinates.word3_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.single,Matrix.one_apply]

private def coordinates : R ≃* radical :=
  (MonoidHom.ofInjective embed_injective).trans (MulEquiv.subgroupCongr embed_range)

/-- The cubic on coordinates zero and one. -/
def leftCubic : SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 1) 1 *
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 5) ≠ 0) 1

/-- The cubic on coordinates three and four. -/
def rightCubic : SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 4) 1 *
    Matrix.SpecialLinearGroup.transvection (by decide : (4 : Fin 5) ≠ 3) 1

private theorem cubic_conjugation_left (a : R) :
    leftCubic * embed a * leftCubic⁻¹ = embed (α a) := by
  apply Subtype.ext
  change (leftCubic.val*(embedFun a).val)*(leftCubic⁻¹).val=(embedFun (α a)).val
  rw [embed_matrix,embed_matrix]
  simp only [leftCubic,mul_inv_rev,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_inv,Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single,Matrix.one_apply,α]
  all_goals ring_nf
  all_goals simp [show (2:B)=0 from rfl]

private theorem cubic_conjugation_right (a : R) :
    rightCubic * embed a * rightCubic⁻¹ = embed (β a) := by
  apply Subtype.ext
  change (rightCubic.val*(embedFun a).val)*(rightCubic⁻¹).val=(embedFun (β a)).val
  rw [embed_matrix,embed_matrix]
  simp only [rightCubic,mul_inv_rev,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_inv,Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single,Matrix.one_apply,β]
  all_goals ring_nf
  all_goals simp [show (2:B)=0 from rfl]

end Theory.GroupTheory.TransvectionFive.UniquenessHeld.RectangleInnernessModel
