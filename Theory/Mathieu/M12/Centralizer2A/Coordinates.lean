module

public import Theory.Mathieu.M12.Centralizer2A.SixPointAction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Twelve-point coordinates for C₂ × S₅

The six-point action is doubled. The central factor interchanges the two
six-element sets, and S₅ acts identically on their six labels. The displayed
coordinate equivalence uses the actual M₁₂ point labels; membership is proved
in `Embedding`. Source context: Aschbacher–Smith 16.1.5(4), p.1171.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12Centralizer2A

abbrev C2 := Multiplicative (ZMod 2)

def point : C2 × Fin 6 → Fin 12 := fun p =>
  if p.1 = 1 then ![0,1,3,6,8,9] p.2 else ![2,4,10,7,5,11] p.2

def pointInverse : Fin 12 → C2 × Fin 6 :=
  ![(1,0),(1,1),(Multiplicative.ofAdd 1,0),(1,2),(Multiplicative.ofAdd 1,1),
    (Multiplicative.ofAdd 1,4),(1,3),(Multiplicative.ofAdd 1,3),(1,4),(1,5),
    (Multiplicative.ofAdd 1,2),(Multiplicative.ofAdd 1,5)]

def pointEquiv : C2 × Fin 6 ≃ Fin 12 where
  toFun := point
  invFun := pointInverse
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairAction : C2 × Equiv.Perm (Fin 6) →* Equiv.Perm (C2 × Fin 6) where
  toFun p := (Equiv.mulLeft p.1).prodCongr p.2
  map_one' := by ext p <;> simp
  map_mul' p q := by ext x <;> simp [mul_assoc]

noncomputable def representation : C2 × Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 12) :=
  pointEquiv.permCongrHom.toMonoidHom.comp
    (pairAction.comp ((MonoidHom.id C2).prodMap sixAction))

theorem representation_apply (p : C2 × Equiv.Perm (Fin 5)) (x : C2 × Fin 6) :
    representation p (pointEquiv x) = pointEquiv (p.1 * x.1, sixAction p.2 x.2) := by
  change pointEquiv ((Equiv.mulLeft p.1).prodCongr (sixAction p.2)
    (pointEquiv.symm (pointEquiv x))) = _
  rw [pointEquiv.symm_apply_apply]
  rfl

theorem representation_injective : Function.Injective representation := by
  intro p q hpq
  have h (i : Fin 6) : (p.1, sixAction p.2 i) = (q.1, sixAction q.2 i) := by
    apply pointEquiv.injective
    simpa only [representation_apply, mul_one] using
      congrArg (fun f : Equiv.Perm (Fin 12) => f (pointEquiv (1,i))) hpq
  exact Prod.ext (congrArg (fun z : C2 × Fin 6 => z.1) (h 0))
    (sixAction_injective (Equiv.ext fun i => congrArg (fun z : C2 × Fin 6 => z.2) (h i)))

end Sporadic.Mathieu.M12Centralizer2A
