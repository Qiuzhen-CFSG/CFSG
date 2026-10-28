module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FactorSign
public import Mathlib.GroupTheory.Sylow
/-!
# The odd factor-sign involutions of the binary orthogonal square

An involution outside the factor-sign kernel in S₃ wr C₂ fixes both
anisotropic planes and reflects exactly one of them. All such involutions
are conjugate to the literal right-axis reflection. The two finite tables
use only the seventy-two wreath elements.

Every Sylow two-subgroup contains an involution in this coset. The quotient
consumers retain an arbitrary surjective homomorphism, its actual kernel,
and its Sylow subgroup; their lifted conjugator changes the quotient image
without asserting an involutory lift in the original group.

Source: Aschbacher–Smith (2.4.29), printed p.546, the transvection-coset step.
-/
@[expose] public section
open Subgroup
namespace BinaryFourPlus.TransvectionCoset
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm

def reflection : Equiv.Perm (Fin 3) := Equiv.swap 1 2

def rightReflection : Wreath := ⟨fun i=>if i=1 then 1 else reflection,1⟩

theorem rightReflection_square : rightReflection^2=1 := by decide +kernel

theorem rightReflection_factorSign : factorSign rightReflection≠1 := by decide +kernel

theorem factorSign_conj (a w:Wreath) : factorSign (a*w*a⁻¹)=factorSign w := by
  simp only [map_mul,map_inv]
  exact by rw [mul_comm (factorSign a),mul_assoc,mul_inv_cancel,mul_one]

private theorem coordinates_table : ∀w:Wreath,w^2=1→factorSign w≠1→
    w.right=1 ∧ ((w.left 1=1 ∧ (w.left swapIndex)^2=1 ∧ w.left swapIndex≠1) ∨
    (w.left swapIndex=1 ∧ (w.left 1)^2=1 ∧ w.left 1≠1)) := by decide +kernel

theorem involution_coordinates (w:Wreath) (hw:w^2=1) (hs:factorSign w≠1) :
    w.right=1 ∧ ((w.left 1=1 ∧ (w.left swapIndex)^2=1 ∧ w.left swapIndex≠1) ∨
    (w.left swapIndex=1 ∧ (w.left 1)^2=1 ∧ w.left 1≠1)) :=
  coordinates_table w hw hs

private theorem conjugacy_table : ∀w:Wreath,w^2=1→factorSign w≠1→
    ∃a:Wreath,a*w*a⁻¹=rightReflection := by decide +kernel

theorem conjugate_rightReflection (w:Wreath) (hw:w^2=1) (hs:factorSign w≠1) :
    ∃a:Wreath,a*w*a⁻¹=rightReflection := conjugacy_table w hw hs

theorem conjugate_odd_involutions (w v:Wreath) (hw:w^2=1) (hv:v^2=1)
    (hsw:factorSign w≠1) (hsv:factorSign v≠1) : ∃a:Wreath,a*w*a⁻¹=v := by
  obtain ⟨a,ha⟩ := conjugate_rightReflection w hw hsw
  obtain ⟨b,hb⟩ := conjugate_rightReflection v hv hsv
  refine ⟨b⁻¹*a,?_⟩
  calc
    (b⁻¹*a)*w*(b⁻¹*a)⁻¹=b⁻¹*(a*w*a⁻¹)*b := by group
    _=b⁻¹*(b*v*b⁻¹)*b := by rw [ha,←hb]
    _=v := by group

theorem exists_in_sylow (P:Sylow 2 Wreath) :
    ∃w∈(P:Subgroup Wreath),w^2=1 ∧ factorSign w≠1 := by
  have hp : IsPGroup 2 (zpowers rightReflection) :=
    IsPGroup.of_card_dvd_pow (n:=1) (by
      simpa only [Nat.card_zpowers,pow_one] using
        orderOf_dvd_of_pow_eq_one rightReflection_square)
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq Wreath Q P
  refine ⟨a*rightReflection*a⁻¹,?_,?_,?_⟩
  · have hh := congrArg Sylow.toSubgroup ha
    change (Q:Subgroup Wreath).map (MulAut.conj a).toMonoidHom=(P:Subgroup Wreath) at hh
    rw [←hh]
    exact mem_map_of_mem _ (hQ (mem_zpowers rightReflection))
  · have hh := congrArg (MulAut.conj a) rightReflection_square
    simpa only [map_pow,map_one,MulAut.conj_apply] using hh
  · rw [factorSign_conj]
    exact rightReflection_factorSign

/-- An actual Sylow subgroup has an element outside the pulled-back sign kernel
whose square lies in the literal quotient kernel. -/
theorem exists_sylow_outside_kernel {G:Type*} [Group G] [Finite G]
    (f:G→*Wreath) (hf:Function.Surjective f) (T:Sylow 2 G) :
    ∃t∈(T:Subgroup G),t^2∈f.ker ∧ t∉(T:Subgroup G) ⊓ (factorSign.comp f).ker := by
  let P := T.mapSurjective (f:=f) hf
  obtain ⟨w,hw,h2,hs⟩ := exists_in_sylow P
  change w∈(T:Subgroup G).map f at hw
  obtain ⟨t,ht,rfl⟩ := hw
  refine ⟨t,ht,?_,?_⟩
  · change f (t^2)=1
    rwa [map_pow]
  · intro hh
    exact hs hh.2

/-- Quotient consumer retaining the actual kernel and outside-coset element. -/
theorem conjugate_image_of_outside_kernel {G:Type*} [Group G]
    (f:G→*Wreath) (hf:Function.Surjective f) (T:Subgroup G) (t:G)
    (ht:t∈T) (hout:t∉T ⊓ (factorSign.comp f).ker) (h2:t^2∈f.ker) :
    ∃a:G,f (a*t*a⁻¹)=rightReflection := by
  have hw : (f t)^2=1 := by
    change f (t^2)=1 at h2
    rwa [map_pow] at h2
  have hs : factorSign (f t)≠1 := by
    intro hh
    exact hout ⟨ht,hh⟩
  obtain ⟨b,hb⟩ := conjugate_rightReflection (f t) hw hs
  obtain ⟨a,rfl⟩ := hf b
  refine ⟨a,?_⟩
  simpa only [map_mul,map_inv] using hb

/-- The same literal quotient transport may target any marked odd involution. -/
theorem conjugate_image_to_odd_involution {G:Type*} [Group G]
    (f:G→*Wreath) (hf:Function.Surjective f) (T:Subgroup G) (t:G)
    (ht:t∈T) (hout:t∉T ⊓ (factorSign.comp f).ker) (h2:t^2∈f.ker)
    (v:Wreath) (hv:v^2=1) (hsv:factorSign v≠1) :
    ∃a:G,f (a*t*a⁻¹)=v := by
  have hw : (f t)^2=1 := by
    change f (t^2)=1 at h2
    rwa [map_pow] at h2
  have hs : factorSign (f t)≠1 := by
    intro hh
    exact hout ⟨ht,hh⟩
  obtain ⟨b,hb⟩ := conjugate_odd_involutions (f t) v hw hv hs hsv
  obtain ⟨a,rfl⟩ := hf b
  refine ⟨a,?_⟩
  simpa only [map_mul,map_inv] using hb

end BinaryFourPlus.TransvectionCoset
