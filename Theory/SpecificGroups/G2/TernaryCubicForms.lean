module
public import Theory.SpecificGroups.G2.TernaryRootCoordinates
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic

/-!
# Alternating forms on the literal ternary cubic coordinates

Expanding in the four coordinate vectors shows that an alternating form
preserved by the Atlas short-root cubic has only the (0,3) and (2,3)
coefficients. This calculation keeps the scalar map fixed, so it does not
silently discard a sign when comparing the original commutator form.
The original-group application is G2Recognition.MaximalCubicForms, part
of the endpoint construction for Aschbacher–Smith I.4.5, printed p.417.
The root convention comes from the licensed Atlas port; see
LICENSES/ATLAS-CITATION.cff and LICENSES/ATLAS.txt.
-/

public section

open Atlas.G2.TernaryCore
open LinearMap
namespace Atlas.G2.TernaryCore
private abbrev W := Fin 4 → ZMod 3
private def basisVector (i : Fin 4) : W := Pi.single i 1
private theorem expansion (B : LinearMap.BilinForm (ZMod 3) W) (x y : W) :
    B x y = ∑ i : Fin 4, ∑ j : Fin 4, x i * B (basisVector i) (basisVector j) * y j := by
  conv_lhs => rw [←Matrix.toBilin'_toMatrix' B]
  simp only [Matrix.toBilin'_apply, LinearMap.BilinForm.toMatrix'_apply,
    basisVector, mul_assoc]

private theorem formula (B : LinearMap.BilinForm (ZMod 3) W) (hB : B.IsAlt) (x y : W) :
    B x y =
      B (basisVector 0) (basisVector 1)*(x 0*y 1-y 0*x 1)+
      B (basisVector 0) (basisVector 2)*(x 0*y 2-y 0*x 2)+
      B (basisVector 0) (basisVector 3)*(x 0*y 3-y 0*x 3)+
      B (basisVector 1) (basisVector 2)*(x 1*y 2-y 1*x 2)+
      B (basisVector 1) (basisVector 3)*(x 1*y 3-y 1*x 3)+
      B (basisVector 2) (basisVector 3)*(x 2*y 3-y 2*x 3) := by
  rw [expansion]
  have hji (i j : Fin 4) : B (basisVector j) (basisVector i) = - B (basisVector i) (basisVector j) := (hB.neg_eq _ _).symm
  simp only [Fin.sum_univ_four,hB.self_eq_zero,mul_zero,zero_mul,zero_add,add_zero]
  rw [hji 0 1,hji 0 2,hji 0 3,hji 1 2,hji 1 3,hji 2 3]
  ring

private theorem invariant_formula (B : LinearMap.BilinForm (ZMod 3) W) (hB : B.IsAlt)
    (hinv : ∀ x y,B (shortRoot (Multiplicative.ofAdd x)).toAdd
      (shortRoot (Multiplicative.ofAdd y)).toAdd=B x y) :
    ∀ x y,B x y =
      B (basisVector 0) (basisVector 3)*(x 0*y 3-y 0*x 3)+
      B (basisVector 2) (basisVector 3)*(x 2*y 3-y 2*x 3) := by
  have h02 := hinv (basisVector 0) (basisVector 2)
  have h03 := hinv (basisVector 0) (basisVector 3)
  have h13 := hinv (basisVector 1) (basisVector 3)
  have h23 := hinv (basisVector 2) (basisVector 3)
  conv at h02 => lhs; rw [formula B hB]
  conv at h02 => rhs; rw [formula B hB]
  conv at h03 => lhs; rw [formula B hB]
  conv at h03 => rhs; rw [formula B hB]
  conv at h13 => lhs; rw [formula B hB]
  conv at h13 => rhs; rw [formula B hB]
  conv at h23 => lhs; rw [formula B hB]
  conv at h23 => rhs; rw [formula B hB]
  simp [shortRoot,basisVector] at h02 h03 h13 h23
  have h01 : B (basisVector 0) (basisVector 1)=0 := by
    dsimp only [basisVector]
    linear_combination h02
  have h02' : B (basisVector 0) (basisVector 2)=0 := by
    dsimp only [basisVector]
    linear_combination h02 - h03
  have h12 : B (basisVector 1) (basisVector 2)=0 := by
    dsimp only [basisVector]
    linear_combination h02 - h13
  have h13' : B (basisVector 1) (basisVector 3)=0 := by
    dsimp only [basisVector] at h02' h12 ⊢
    linear_combination h23 - h02 - h02' + 2*h12
  intro x y
  rw [formula B hB,h01,h02',h12,h13']
  ring


private def pairingAdd (b : V →* (V →* Multiplicative (ZMod 3))) :
    W →+ (W →+ ZMod 3) where
  toFun x := (b (Multiplicative.ofAdd x)).toAdditive
  map_zero' := by apply AddMonoidHom.ext; intro y; change (b 1 (Multiplicative.ofAdd y)).toAdd=0; simp
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    change (b (Multiplicative.ofAdd x*Multiplicative.ofAdd y) (Multiplicative.ofAdd z)).toAdd =
      (b (Multiplicative.ofAdd x) (Multiplicative.ofAdd z)).toAdd+
      (b (Multiplicative.ofAdd y) (Multiplicative.ofAdd z)).toAdd
    rw [map_mul,MonoidHom.mul_apply]
    rfl

private def pairingForm (b : V →* (V →* Multiplicative (ZMod 3))) :
    LinearMap.BilinForm (ZMod 3) W :=
  ((AddMonoidHom.toZModLinearMapEquiv 3).toAddMonoidHom.comp (pairingAdd b)).toZModLinearMap 3

/-- On the same literal cubic coordinates, the invariant alternating form has
only two coefficients. The scalar-value map is kept fixed. -/
theorem shortRoot_invariant_pairing
    (b : V →* (V →* Multiplicative (ZMod 3))) (halt : ∀ v,b v v=1)
    (hinv : ∀ v w,b (shortRoot v) (shortRoot w)=b v w) :
    ∃ c f : ZMod 3, ∀ v w,b v w=Multiplicative.ofAdd
      (c*shortForm v w+f*(v.toAdd 2*w.toAdd 3-w.toAdd 2*v.toAdd 3)) := by
  let B := pairingForm b
  have hB : B.IsAlt := by
    intro v
    exact congrArg Multiplicative.toAdd (halt (Multiplicative.ofAdd v))
  have hi : ∀ x y,B (shortRoot (Multiplicative.ofAdd x)).toAdd
      (shortRoot (Multiplicative.ofAdd y)).toAdd=B x y := by
    intro x y
    exact congrArg Multiplicative.toAdd (hinv (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))
  refine ⟨B (basisVector 0) (basisVector 3),B (basisVector 2) (basisVector 3),?_⟩
  intro v w
  exact congrArg Multiplicative.ofAdd (invariant_formula B hB hi v.toAdd w.toAdd)

end Atlas.G2.TernaryCore
