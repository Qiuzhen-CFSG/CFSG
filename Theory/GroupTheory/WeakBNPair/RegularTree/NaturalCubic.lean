module
public import Theory.SpecificGroups.SL2.Affine
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group

/-!
# Cubic pairs above the natural SL₂-module in characteristic two

An upper transvection with nonzero parameter a and the lower transvection
with parameter a⁻¹ have cubic product, acting without nonzero fixed vectors
on the natural plane. In any extension with that actual kernel module, the
cube of a lift lies in the kernel and centralizes the lift, hence is trivial.
Root injectivity lifts the two involution relations. This constructs a cubic
pair in the original group and proves its kernel centralizer trivial.

The braid matrix is anti-diagonal. Comparing it with an independently marked
anti-diagonal reflection gives a diagonal ratio, so their discrepancy belongs
to the original kernel times Cartan. Neither splitting of the extension nor
an abstract recognition of the group is assumed.

Source: DGS, *Groups and Graphs* (1985), (14.12)--(14.13), pp.217--218.
-/

@[expose] public noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {F : Type*} [Field F] [CharP F 2]
/-- The upper root transvection in the standard natural coordinates. -/
abbrev upper (a : F) : SL(2,F) := transvection zero_ne_one a
/-- The opposite lower root transvection in the same coordinates. -/
abbrev lower (a : F) : SL(2,F) := transvection one_ne_zero a

/-- Upper root elements square to one in characteristic two. -/
theorem upper_square (a : F) : upper a * upper a = 1 := by
  rw [upper, ← transvection_add, CharTwo.add_self_eq_zero, transvection_coeff_zero]

/-- Lower root elements square to one in characteristic two. -/
theorem lower_square (a : F) : lower a * lower a = 1 := by
  rw [lower, ← transvection_add, CharTwo.add_self_eq_zero, transvection_coeff_zero]

/-- The product with reciprocal parameters has its literal cubic matrix. -/
theorem cubic_matrix (a : F) (ha : a ≠ 0) :
    (upper a * lower a⁻¹).val = !![0,a;a⁻¹,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper,lower,transvection_coe,coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      mul_inv_cancel₀ ha,CharTwo.add_self_eq_zero]

/-- The reciprocal-parameter product has cube one. -/
theorem cubic_cube (a : F) (ha : a ≠ 0) : (upper a * lower a⁻¹)^3=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ,coe_mul,cubic_matrix a ha,Matrix.mul_apply,Fin.sum_univ_two,
      mul_inv_cancel₀ ha,inv_mul_cancel₀ ha,CharTwo.add_self_eq_zero]

/-- The cubic product fixes no nonzero vector of the natural plane. -/
theorem cubic_fixed (a : F) (ha : a ≠ 0) (v : Fin 2 → F)
    (hv : (upper a * lower a⁻¹).val *ᵥ v=v) : v=0 := by
  have h0 : a * v 1 = v 0 := by
    simpa [cubic_matrix a ha,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun hv 0
  have h1 : a⁻¹ * v 0 = 0 := by
    simpa [cubic_matrix a ha,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun hv 1
  have hv0 : v 0=0 := (mul_eq_zero.mp h1).resolve_left (inv_ne_zero ha)
  have hv1 : v 1=0 := (mul_eq_zero.mp (h0.trans hv0)).resolve_left ha
  ext i
  fin_cases i <;> assumption

/-- The braid word has anti-diagonal entries a and a⁻¹. -/
theorem braid_matrix (a : F) (ha : a ≠ 0) :
    (upper a * lower a⁻¹ * upper a).val=!![0,a;a⁻¹,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mul,cubic_matrix a ha,upper,transvection_coe,Matrix.mul_apply,
      Fin.sum_univ_two,inv_mul_cancel₀ ha,CharTwo.add_self_eq_zero]

/-- The anti-diagonal braid word squares to one. -/
theorem braid_square (a : F) (ha : a ≠ 0) :
    (upper a * lower a⁻¹ * upper a)*(upper a * lower a⁻¹ * upper a)=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mul,braid_matrix a ha,Matrix.mul_apply,Fin.sum_univ_two,
      mul_inv_cancel₀ ha,inv_mul_cancel₀ ha]

/-- Comparing the two marked braid words gives their diagonal ratio. -/
theorem braid_ratio (a c : F) (ha : a ≠ 0) (hc : c ≠ 0) :
    (upper a * lower a⁻¹ * upper a) * (upper c * lower c⁻¹ * upper c)⁻¹ =
      diag2 (a*c⁻¹) (mul_ne_zero ha (inv_ne_zero hc)) := by
  rw [inv_eq_of_mul_eq_one_right (braid_square c hc)]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mul,braid_matrix a ha,braid_matrix c hc,diag2_coe',Matrix.mul_apply,
      Fin.sum_univ_two,mul_comm]

/-- A matrix interchanging two nonidentity opposite root elements is a
marked anti-diagonal braid word. -/
theorem braid_of_intertwines (g : SL(2,F)) (a b c d : F)
    (ha : a≠0) (hc : c≠0)
    (hupper : g*upper a=lower b*g) (hlower : g*lower c=upper d*g) :
    ∃ e : F, e≠0 ∧ g=upper e*lower e⁻¹*upper e := by
  have h00 : g.val 0 0=0 := by
    have he := congrArg (fun z : SL(2,F) => z.val 0 1) hupper
    have hz : g.val 0 0*a=0 := by
      simpa [upper,lower,coe_mul,transvection_coe,Matrix.mul_apply,Fin.sum_univ_two] using he
    exact (mul_eq_zero.mp hz).resolve_right ha
  have h11 : g.val 1 1=0 := by
    have he := congrArg (fun z : SL(2,F) => z.val 1 0) hlower
    have hz : g.val 1 1*c=0 := by
      simpa [upper,lower,coe_mul,transvection_coe,Matrix.mul_apply,Fin.sum_univ_two] using he
    exact (mul_eq_zero.mp hz).resolve_right hc
  have hdet : g.val 0 1*g.val 1 0=1 := by
    simpa only [Matrix.det_fin_two,h00,h11,zero_mul,zero_sub,CharTwo.neg_eq] using g.property
  have he : g.val 0 1≠0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨g.val 0 1,he,?_⟩
  apply Subtype.ext
  rw [braid_matrix _ he]
  have h10 : g.val 1 0=(g.val 0 1)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00,h11,h10]

variable {P : Type*} [Group P] (π : P →* SL(2,F))

/-- Actual vector coordinates on the kernel, intertwining conjugation with the natural action. -/
structure NaturalKernel where
  coords : π.ker ≃* Multiplicative (Fin 2 → F)
  equivariant : ∀ (g : P) (z : π.ker),
    coords ⟨g*z*g⁻¹, (inferInstance : π.ker.Normal).conj_mem z z.property g⟩ =
      Matrix.SL2.naturalAction F (π g) (coords z)

namespace NaturalKernel
variable {π}
variable (d : NaturalKernel π)

include d in
/-- A lift of the cubic matrix centralizes no nonidentity kernel element. -/
theorem cubic_centralizer (g : P) (a : F) (ha : a≠0)
    (hg : π g=upper a * lower a⁻¹) (z : π.ker) (hz : Commute g (z:P)) : z=1 := by
  have hconj : (⟨g*z*g⁻¹, (inferInstance : π.ker.Normal).conj_mem z z.property g⟩ : π.ker)=z := by
    apply Subtype.ext
    change g*z*g⁻¹=z
    rw [hz.eq,mul_assoc,mul_inv_cancel,mul_one]
  have he := d.equivariant g z
  rw [hconj,hg] at he
  have hv : Multiplicative.toAdd (d.coords z)=0 := by
    apply cubic_fixed a ha
    exact (congrArg Multiplicative.toAdd he).symm
  apply d.coords.injective
  rw [map_one]
  exact Multiplicative.toAdd.injective hv

include d in
/-- The natural kernel action forces the cubic relation to lift exactly. -/
theorem cubic_order (g : P) (a : F) (ha : a≠0)
    (hg : π g=upper a * lower a⁻¹) : orderOf g=3 := by
  have hcube : g^3∈π.ker := by
    rw [MonoidHom.mem_ker,map_pow,hg,cubic_cube a ha]
  have hc : g^3=1 := congrArg Subtype.val
    (d.cubic_centralizer g a ha hg ⟨g^3,hcube⟩ (Commute.self_pow g 3))
  have hne : g≠1 := by
    intro he
    have hh := congrArg (fun z : SL(2,F) => z.val 0 0) hg
    rw [he,map_one,cubic_matrix a ha] at hh
    exact one_ne_zero hh
  exact orderOf_eq_prime hc hne

end NaturalKernel

omit [CharP F 2] in
/-- An element of an embedded root with trivial quotient image is trivial. -/
theorem eq_one_of_root_kernel (R : Subgroup P) (hR : R ⊓ π.ker=⊥)
    (x : P) (hx : x∈R) (hπ : π x=1) : x=1 := by
  have hm : x∈R ⊓ π.ker := ⟨hx,hπ⟩
  rwa [hR] at hm

/-- Injectivity on the actual root lifts the upper involution relation. -/
theorem square_of_image_upper (R : Subgroup P) (hR : R ⊓ π.ker=⊥)
    (x : P) (hx : x∈R) (a : F) (hπ : π x=upper a) : x*x=1 := by
  apply eq_one_of_root_kernel π R hR (x*x) (R.mul_mem hx hx)
  rw [map_mul,hπ,upper_square]

/-- Injectivity on the opposite root lifts its involution relation. -/
theorem square_of_image_lower (R : Subgroup P) (hR : R ⊓ π.ker=⊥)
    (x : P) (hx : x∈R) (a : F) (hπ : π x=lower a) : x*x=1 := by
  apply eq_one_of_root_kernel π R hR (x*x) (R.mul_mem hx hx)
  rw [map_mul,hπ,lower_square]

/-- The chosen opposite root element produces an actual cubic pair upstairs. -/
theorem pair_of_opposite_images (d : NaturalKernel π) (R S : Subgroup P)
    (hR : R ⊓ π.ker=⊥) (hS : S ⊓ π.ker=⊥)
    (hRimage : ∀ x∈R, ∃ a : F, π x=upper a)
    (hSimage : ∀ a : F, ∃ y∈S, π y=lower a)
    (x : P) (hx : x∈R) (hne : x≠1) :
    ∃ a : F, a≠0 ∧ π x=upper a ∧ ∃ y∈S, π y=lower a⁻¹ ∧
      x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
      ∀ z∈π.ker, Commute x z → Commute y z → z=1 := by
  obtain ⟨a,ha⟩ := hRimage x hx
  have ha0 : a≠0 := by
    intro he
    apply hne
    apply eq_one_of_root_kernel π R hR x hx
    simpa [he,upper,transvection_coeff_zero] using ha
  obtain ⟨y,hy,hπy⟩ := hSimage a⁻¹
  have hπxy : π (x*y)=upper a * lower a⁻¹ := by rw [map_mul,ha,hπy]
  refine ⟨a,ha0,ha,y,hy,hπy,square_of_image_upper π R hR x hx a ha,
    square_of_image_lower π S hS y hy a⁻¹ hπy,d.cubic_order (x*y) a ha0 hπxy,?_⟩
  intro z hz hxz hyz
  exact congrArg Subtype.val (d.cubic_centralizer (x*y) a ha0 hπxy ⟨z,hz⟩ (hxz.mul_left hyz))

/-- The braid/reflection discrepancy belongs to the genuine kernel times the Cartan. -/
theorem correction_mem (K : Subgroup P) (a c : F) (ha : a≠0) (hc : c≠0)
    (x y t : P) (hx : π x=upper a) (hy : π y=lower a⁻¹)
    (ht : π t=upper c*lower c⁻¹*upper c)
    (hK : ∀ b : F, ∀ hb : b≠0, diag2 b hb∈K.map π) :
    (x*y*x)*t⁻¹∈π.ker ⊔ K := by
  have he : π ((x*y*x)*t⁻¹)=diag2 (a*c⁻¹) (mul_ne_zero ha (inv_ne_zero hc)) := by
    rw [map_mul,map_mul,map_mul,map_inv,hx,hy,ht,braid_ratio a c ha hc]
  have hm : (x*y*x)*t⁻¹∈(K.map π).comap π := by
    change π ((x*y*x)*t⁻¹)∈K.map π
    rw [he]
    exact hK _ _
  rwa [Subgroup.comap_map_eq,sup_comm] at hm

end Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
