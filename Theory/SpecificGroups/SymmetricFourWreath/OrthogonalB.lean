module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.BModel
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The literal plus form on B

The two marked four-planes give coordinates in the orthogonal sum of two anisotropic binary planes. The six nonsingular vectors are the two axis classes; the nine nonzero singular vectors are the three diagonal classes.

Source: Aschbacher–Smith 13.9.4–5, printed p.970.
-/

@[expose] public section
namespace SymmetricFourWreath.OrthogonalB
open Subgroup InvolutionClasses
open scoped IsMulCommutative

def planeWord (v : BinaryFourPlus.Plane) : plane false :=
  if v 0=0 then
    if v 1=0 then ⟨DihedralGroup.r 0,by decide⟩ else ⟨DihedralGroup.sr 2,by decide⟩
  else
    if v 1=0 then ⟨DihedralGroup.sr 0,by decide⟩ else ⟨DihedralGroup.r 2,by decide⟩

def planeHom : Multiplicative BinaryFourPlus.Plane →* plane false where
  toFun v := planeWord v.toAdd
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem planeHom_bijective : Function.Bijective planeHom := by decide +kernel

def parameters : Multiplicative BinaryFourPlus.V →* Parameters where
  toFun v := (planeHom (Multiplicative.ofAdd v.toAdd.1),planeHom (Multiplicative.ofAdd v.toAdd.2))
  map_one' := by exact Prod.ext planeHom.map_one planeHom.map_one
  map_mul' x y := Prod.ext (planeHom.map_mul _ _) (planeHom.map_mul _ _)

theorem parameters_bijective : Function.Bijective parameters := by decide +kernel

noncomputable def coordinates : B ≃* Multiplicative BinaryFourPlus.V :=
  parametersEquivB.symm.trans (MulEquiv.ofBijective parameters parameters_bijective).symm

noncomputable def additiveCoordinates : Additive B ≃+ BinaryFourPlus.V :=
  coordinates.toAdditive.trans (AddEquiv.additiveMultiplicative _)

noncomputable def linearCoordinates : Additive B ≃ₗ[ZMod 2] BinaryFourPlus.V :=
  { additiveCoordinates with map_smul' := ZMod.map_smul additiveCoordinates }

theorem linearCoordinates_symm_apply (v : BinaryFourPlus.V) :
    ((linearCoordinates.symm v).toMul : W)=parametersToW (parameters (Multiplicative.ofAdd v)) := rfl

private theorem nonzero_index : ∀v:BinaryFourPlus.V,
    BinaryFourPlus.q v=1 ↔
      (parameters (Multiplicative.ofAdd v)≠1 ∧
        (parameterIndex (parameters (Multiplicative.ofAdd v))=1 ∨
         parameterIndex (parameters (Multiplicative.ofAdd v))=2)) := by decide +kernel

private theorem parameters_order (a:Parameters) : orderOf (parametersToW a)=2 ↔ a≠1 := by
  have hs : ∀a:Parameters,a^2=1 := by decide +kernel
  rw [orderOf_eq_prime_iff,←map_pow,hs,map_one,eq_self_iff_true,true_and]
  constructor
  · intro hn he
    exact hn (he ▸ parametersToW.map_one)
  · intro hn he
    exact hn (parametersToW_injective (he.trans parametersToW.map_one.symm))

theorem nonsingular_iff (x : B) : BinaryFourPlus.q (linearCoordinates (Additive.ofMul x))=1 ↔
    IsConj (representative 1) (x:W) ∨ IsConj (representative 2) (x:W) := by
  obtain ⟨v,hv⟩ := linearCoordinates.symm.surjective (Additive.ofMul x)
  have hx : (x:W)=parametersToW (parameters (Multiplicative.ofAdd v)) := by
    rw [←linearCoordinates_symm_apply v,hv]
    rfl
  have hl : linearCoordinates (Additive.ofMul x)=v := by rw [←hv,linearCoordinates.apply_symm_apply]
  rw [hl,nonzero_index,hx,isConj_representative_iff,isConj_representative_iff,parametersToW_index]
  rw [parameters_order]
  tauto

private theorem zero_index : ∀v:BinaryFourPlus.V,
    BinaryFourPlus.q v=0 ↔
      parameters (Multiplicative.ofAdd v)=1 ∨
      (parameters (Multiplicative.ofAdd v)≠1 ∧
        (parameterIndex (parameters (Multiplicative.ofAdd v))=0 ∨
         parameterIndex (parameters (Multiplicative.ofAdd v))=3 ∨
         parameterIndex (parameters (Multiplicative.ofAdd v))=4)) := by decide +kernel

theorem singular_iff (x:B) : BinaryFourPlus.q (linearCoordinates (Additive.ofMul x))=0 ↔
    x=1 ∨ IsConj (representative 0) (x:W) ∨
      IsConj (representative 3) (x:W) ∨ IsConj (representative 4) (x:W) := by
  obtain ⟨v,hv⟩ := linearCoordinates.symm.surjective (Additive.ofMul x)
  have hx : (x:W)=parametersToW (parameters (Multiplicative.ofAdd v)) := by
    rw [←linearCoordinates_symm_apply v,hv]
    rfl
  have hl : linearCoordinates (Additive.ofMul x)=v := by rw [←hv,linearCoordinates.apply_symm_apply]
  have h1 : x=1 ↔ parameters (Multiplicative.ofAdd v)=1 := by
    rw [Subtype.ext_iff,hx]
    exact ⟨fun h=>parametersToW_injective (h.trans parametersToW.map_one.symm),
      fun h=>h ▸ parametersToW.map_one⟩
  rw [hl,zero_index,h1,hx,isConj_representative_iff,isConj_representative_iff,
    isConj_representative_iff,parametersToW_index,parameters_order]
  tauto
end SymmetricFourWreath.OrthogonalB
