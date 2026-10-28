module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Generators
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Coordinate actions for the ternary quaternion core

The four quaternion generators and the five root/torus generators act by the
explicit linear formulas below. Each formula is checked on the octonion basis
against the actual automorphism. This keeps subsequent finite calculations
small while retaining their connection to the concrete G₂ model.

Source application: Aschbacher–Smith, I.4(G1), printed p.417, and Main Theorem
0.1.2(4), pp.3–4 (also pp.481–482). The coordinate conventions are those of the
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.Involution.CoreCalculation
open Atlas.SplitOctonion
set_option maxRecDepth 100000
def marks : Fin 3 → Carrier K := ![u,v,w]
theorem local_ext (g h : P)
    (he : ∀ i j, g.val.val (marks i) j = h.val.val (marks i) j) : g = h := by
  apply Subtype.ext
  exact ext_generators _ _ (funext (he 0)) (funext (he 1)) (funext (he 2))
def qiApply (s : Bool) (x : Carrier K) : Carrier K :=
  if s then ![-x 0 + x 2, x 1 - x 3 + x 4 + x 6, x 0 + x 2,
    -x 1 - x 3 - x 4 + x 6, x 1 - x 3 - x 4 - x 6, -x 5 - x 7,
    x 1 + x 3 - x 4 + x 6, -x 5 + x 7]
  else ![-x 0 + x 5, x 1, -x 2 - x 7, x 3, x 4, x 0 + x 5, x 6, -x 2 + x 7]
def qjApply (s : Bool) (x : Carrier K) : Carrier K :=
  if s then ![x 2,x 6,-x 0,x 4,x 3,-x 7,x 1,x 5]
  else ![x 5,x 1,-x 7,x 3,x 4,-x 0,x 6,x 2]
def qiLinear (s : Bool) : Carrier K →ₗ[K] Carrier K where
  toFun := qiApply s
  map_add' x y := by cases s <;> ext i <;> fin_cases i <;> simp [qiApply] <;> ring
  map_smul' a x := by cases s <;> ext i <;> fin_cases i <;> simp [qiApply] <;> ring
theorem qi_apply (s : Bool) (x : Carrier K) : (quaternionI s).val.val x = qiApply s x := by
  have h : (quaternionI s).val.val.toLinearMap = qiLinear s := by
    apply linearMap_ext
    intro i
    apply funext
    exact (by decide +kernel : ∀ s i j,
      (quaternionI s).val.val (basisVector i) j = qiLinear s (basisVector i) j) s i
  exact LinearMap.congr_fun h x

def qjLinear (s : Bool) : Carrier K →ₗ[K] Carrier K where
  toFun := qjApply s
  map_add' x y := by cases s <;> ext i <;> fin_cases i <;> simp [qjApply] <;> ring
  map_smul' a x := by cases s <;> ext i <;> fin_cases i <;> simp [qjApply]
theorem qj_apply (s : Bool) (x : Carrier K) : (quaternionJ s).val.val x = qjApply s x := by
  have h : (quaternionJ s).val.val.toLinearMap = qjLinear s := by
    apply linearMap_ext
    intro i
    apply funext
    exact (by decide +kernel : ∀ s i j,
      (quaternionJ s).val.val (basisVector i) j = qjLinear s (basisVector i) j) s i
  exact LinearMap.congr_fun h x

def genApply (i : Fin 5) (x : Carrier K) : Carrier K :=
  (![fun x => ![x 0-x 5,x 1,x 2+x 7,x 3,x 4,x 5,x 6,x 7],
     fun x => ![x 0,x 1,x 2,x 3,x 4,x 0+x 5,x 6,-x 2+x 7],
     fun x => ![x 0-x 2,x 1-x 3+x 4+x 6,x 2,x 3-x 6,x 4+x 6,x 5+x 7,x 6,x 7],
     fun x => ![x 0,x 1,x 0+x 2,x 1+x 3,-x 1+x 4,x 5,x 1+x 3-x 4+x 6,-x 5+x 7],
     fun x => ![x 0,-x 1,-x 2,x 3,x 4,-x 5,-x 6,x 7]] :
     Fin 5 → Carrier K → Carrier K) i x

def genLinear (i : Fin 5) : Carrier K →ₗ[K] Carrier K where
  toFun := genApply i
  map_add' x y := by fin_cases i <;> ext j <;> fin_cases j <;> simp [genApply] <;> ring
  map_smul' a x := by fin_cases i <;> ext j <;> fin_cases j <;> simp [genApply] <;> ring

theorem gen_apply (i : Fin 5) (x : Carrier K) : (generator i).val.val x = genApply i x := by
  have h : (generator i).val.val.toLinearMap = genLinear i := by
    apply linearMap_ext
    intro k
    apply funext
    exact (by decide +kernel : ∀ i k j,
      (generator i).val.val (basisVector k) j = genLinear i (basisVector k) j) i k
  exact LinearMap.congr_fun h x

def qmap (s : Bool) : QuaternionGroup 2 → P
  | .a i => quaternionI s ^ i.val
  | .xa i => quaternionJ s * quaternionI s ^ i.val

def qApply (s : Bool) : QuaternionGroup 2 → Carrier K → Carrier K
  | .a i => (qiApply s)^[i.val]
  | .xa i => qjApply s ∘ (qiApply s)^[i.val]

theorem qmap_apply (s : Bool) (q : QuaternionGroup 2) (x : Carrier K) :
    (qmap s q).val.val x = qApply s q x := by
  have hp (n : ℕ) (y : Carrier K) :
      (quaternionI s ^ n).val.val y = (qiApply s)^[n] y := by
    change ((quaternionI s).val.val ^ n) y = _
    rw [LinearEquiv.pow_apply]
    exact congrFun (congrArg (fun f : Carrier K → Carrier K => f^[n])
      (funext (qi_apply s))) y
  cases q with
  | a i => exact hp i.val x
  | xa i =>
    change (quaternionJ s).val.val ((quaternionI s ^ i.val).val.val x) = _
    rw [qj_apply, hp]
    rfl

end Atlas.G2.TernaryLocals.Involution.CoreCalculation
