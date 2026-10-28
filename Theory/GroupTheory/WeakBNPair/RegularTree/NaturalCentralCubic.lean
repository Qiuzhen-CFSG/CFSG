module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCentralReflection
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalKernelMarking

/-!
# Cubic pairs with the central natural-kernel defect retained

In an extension of SL₂ in characteristic two whose two-kernel maps onto
its natural plane with central kernel, a cubic matrix lift has central cube.
If the full kernel has exponent two, that lift has sixth power one.
For an upper involution x and a parameter-matched involution t, the reflected
root y = txt⁻¹ therefore satisfies (xy)³ = 1. The braid xyx differs from t
by an actual central kernel element. Its common kernel centralizer with x
is precisely the actor center, rather than the trivial subgroup.

A full diagonal Cartan adjusts the parameter inside the original Cartan
coset of t. The source application uses these formulas for the literal
path radicals in both b=1 branches, retaining the r=4 center and its defect.

Source: DGS, Groups and Graphs (1985), the local algebra of (14.12),
pp.217--218. The separate central exchange argument (14.15) is not asserted.
-/

@[expose] public noncomputable section
open Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {F X : Type*} [Field F] [CharP F 2] [Group X]
namespace NaturalCentralKernel
variable {π : X →* SL(2,F)} (d : NaturalCentralKernel π)
include d

/-- The kernel centralizer of a cubic lift is central in the whole actor. -/
theorem cubic_centralizer (g : X) (a : F) (ha : a≠0)
    (hg : π g=upper a*lower a⁻¹) (z : π.ker) (hz : Commute g (z:X)) :
    (z:X)∈center X := by
  have hc : (⟨g*z*g⁻¹,(inferInstance : π.ker.Normal).conj_mem z z.property g⟩ : π.ker)=z := by
    apply Subtype.ext
    change g*z*g⁻¹=z
    rw [hz.eq,mul_assoc,mul_inv_cancel,mul_one]
  apply d.central
  have he := d.equivariant g z
  rw [hc,hg] at he
  exact Multiplicative.toAdd.injective
    (cubic_fixed a ha _ (congrArg Multiplicative.toAdd he).symm)

/-- The cube of a cubic lift lies in the actual central kernel. -/
theorem cubic_cube_central (g : X) (a : F) (ha : a≠0)
    (hg : π g=upper a*lower a⁻¹) : g^3∈π.ker ⊓ center X := by
  have hk : g^3∈π.ker := by
    rw [MonoidHom.mem_ker,map_pow,hg,cubic_cube a ha]
  exact ⟨hk,d.cubic_centralizer g a ha hg ⟨g^3,hk⟩ (Commute.self_pow g 3)⟩

/-- A cubic lift in an elementary central extension has sixth power one. -/
theorem cubic_six (hsq : ∀ z : π.ker, z*z=1)
    (g : X) (a : F) (ha : a≠0) (hg : π g=upper a*lower a⁻¹) : g^6=1 := by
  have hk := (d.cubic_cube_central g a ha hg).1
  have hh := congrArg (fun z : π.ker => (z:X)) (hsq ⟨g^3,hk⟩)
  change g^3*g^3=1 at hh
  simpa only [←pow_add] using hh

/-- Match an upper involution to a reflected copy. The pair is genuinely
cubic, while its braid differs from the chosen reflection by a central involution. -/
theorem reflected_pair (hsq : ∀ z : π.ker, z*z=1)
    (x t : X) (hxx : x*x=1) (htt : t*t=1)
    (a : F) (ha : a≠0) (hx : π x=upper a)
    (ht : π t=upper a*lower a⁻¹*upper a) :
    let y := t*x*t⁻¹
    y*y=1 ∧ π y=lower a⁻¹ ∧ orderOf (x*y)=3 ∧
      (x*y*x)*t⁻¹∈π.ker ⊓ center X ∧
      ∀ z∈π.ker, (Commute x z ∧ Commute y z ↔ z∈center X) := by
  let y := t*x*t⁻¹
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right htt
  have hπy : π y=lower a⁻¹ := by
    dsimp [y]
    rw [map_mul,map_mul,map_inv,ht,hx,braid_conjugates_upper _ ha]
    congr 1
    field_simp
  have hπtx : π (t*x)=upper a*lower a⁻¹ := by
    rw [map_mul,ht,hx,mul_assoc,upper_square,mul_one]
  have hsix := d.cubic_six hsq (t*x) a ha hπtx
  have hxy : (x*y)^3=1 := by
    have hh : (x*y)^3=x*(t*x)^6*x⁻¹ := by
      dsimp [y]
      rw [hti]
      simp only [pow_succ,pow_zero]
      simp only [←mul_assoc,one_mul,mul_inv_cancel_right]
    rw [hh,hsix,mul_one,mul_inv_cancel]
  have hπxy : π (x*y)=upper a*lower a⁻¹ := by rw [map_mul,hx,hπy]
  have hne : x*y≠1 := by
    intro he
    have hh := congrArg (fun z : SL(2,F) => z.val 0 0) hπxy
    rw [he,map_one,cubic_matrix a ha] at hh
    exact one_ne_zero hh
  have hcentral := d.cubic_cube_central (t*x) a ha hπtx
  have hdef : (x*y*x)*t⁻¹=x*(t*x)^3*x⁻¹ := by
    dsimp [y]
    rw [hti]
    simp only [pow_succ,pow_zero]
    group
  have hdef' : (x*y*x)*t⁻¹=(t*x)^3 := by
    rw [hdef,Subgroup.mem_center_iff.mp hcentral.2 x,mul_inv_cancel_right]
  refine ⟨?_,hπy,orderOf_eq_prime hxy hne,hdef' ▸ hcentral,?_⟩
  · calc
      _ = t*(x*x)*t⁻¹ := by group
      _ = 1 := by rw [hxx,mul_one,mul_inv_cancel]
  · intro z hz
    constructor
    · rintro ⟨hxz,hyz⟩
      exact d.cubic_centralizer (x*y) a ha hπxy ⟨z,hz⟩ (hxz.mul_left hyz)
    · intro hc
      exact ⟨Subgroup.mem_center_iff.mp hc x,Subgroup.mem_center_iff.mp hc y⟩

end NaturalCentralKernel

/-- The full diagonal Cartan adjusts a chosen involution to any nonzero
upper-root parameter, inside its original Cartan coset. -/
theorem reflection_with_parameter (π : X →* SL(2,F)) (K : Subgroup X)
    (hdis : K ⊓ π.ker=⊥) (t : X) (htN : t∈normalizer (K : Set X))
    (htt : t*t=1) (b : F) (hb : b≠0)
    (ht : π t=upper b*lower b⁻¹*upper b)
    (hfull : ∀ a : F, ∀ ha : a≠0, diag2 a ha∈K.map π)
    (a : F) (ha : a≠0) :
    ∃ k∈K, (k*t)*(k*t)=1 ∧ π (k*t)=upper a*lower a⁻¹*upper a := by
  obtain ⟨k,hk,hπk⟩ := hfull (a*b⁻¹) (mul_ne_zero ha (inv_ne_zero hb))
  have hπu : π (k*t)=upper a*lower a⁻¹*upper a := by
    rw [map_mul,hπk,←braid_ratio a b ha hb,ht,mul_assoc,inv_mul_cancel,mul_one]
  refine ⟨k,hk,?_,hπu⟩
  apply eq_one_of_root_kernel π K hdis
  · have hh := K.mul_mem hk ((mem_normalizer_iff.mp htN k).mp hk)
    simpa only [inv_eq_of_mul_eq_one_right htt,mul_assoc] using hh
  · rw [map_mul,hπu,braid_square a ha]

end Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
