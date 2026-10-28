module
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms

/-!
# The base subgroups of the automorphism group of A₄ × A₄

The literal regular wreath product S₄ wr C₂ contains its alternating base
and its normal elementary Klein four base. Coordinate subgroups retain the
actual factor action used in the proof of Aschbacher–Smith 14.1.10,
combined manuscript (1 March 2004), printed p.978.
-/

@[expose] public section
namespace AlternatingFourPair.Thompson
open Subgroup
abbrev base : Subgroup W := (RegularWreathProduct.rightHom : W →* Q).ker
@[simp] theorem mem_base (w : W) : w ∈ base ↔ w.right = 1 := Iff.rfl

def baseMap : (Q → D) →* W where
  toFun a := ⟨a, 1⟩
  map_one' := rfl
  map_mul' a b := by ext i <;> simp

@[simp] theorem baseMap_left (a : Q → D) : (baseMap a).left = a := rfl
@[simp] theorem baseMap_right (a : Q → D) : (baseMap a).right = 1 := rfl
 theorem baseMap_injective : Function.Injective baseMap := fun _ _ h => congrArg RegularWreathProduct.left h

def coordinateSubgroup (P : Subgroup D) : Subgroup W where
  carrier := {w | w.right = 1 ∧ ∀ i, w.left i ∈ P}
  one_mem' := ⟨rfl, fun _ => P.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨by simp [ha, hb], ?_⟩
    intro i
    simpa [ha] using P.mul_mem (hA i) (hB i)
  inv_mem' := by
    rintro a ⟨ha, hA⟩
    refine ⟨by simp [ha], ?_⟩
    intro i
    simpa [ha] using P.inv_mem (hA i)

@[simp] theorem mem_coordinateSubgroup (P : Subgroup D) (w : W) :
    w ∈ coordinateSubgroup P ↔ w.right = 1 ∧ ∀ i, w.left i ∈ P := Iff.rfl

def alternatingBase : Subgroup W := coordinateSubgroup (alternatingGroup (Fin 4))
def kleinBase : Subgroup W := coordinateSubgroup (pCore 2 D)

@[simp] theorem mem_alternatingBase (w : W) :
    w ∈ alternatingBase ↔ w.right = 1 ∧ ∀ i, w.left i ∈ alternatingGroup (Fin 4) := Iff.rfl
@[simp] theorem mem_kleinBase (w : W) :
    w ∈ kleinBase ↔ w.right = 1 ∧ ∀ i, w.left i ∈ pCore 2 D := Iff.rfl

instance coordinateSubgroup_normal (P : Subgroup D) [P.Normal] :
    (coordinateSubgroup P).Normal where
  conj_mem w hw g := by
    refine ⟨by simp [hw.1], ?_⟩
    intro i
    simpa [hw.1, mul_assoc] using Subgroup.Normal.conj_mem (inferInstance : P.Normal) (w.left (g.right⁻¹ * i))
      (hw.2 _) (g.left i)

instance kleinBase_normal : kleinBase.Normal := inferInstanceAs (coordinateSubgroup (pCore 2 D)).Normal
instance alternatingBase_normal : alternatingBase.Normal := inferInstanceAs (coordinateSubgroup (alternatingGroup (Fin 4))).Normal

def coordinateEquiv (P : Subgroup D) : coordinateSubgroup P ≃* (Q → P) where
  toFun w i := ⟨w.val.left i, w.property.2 i⟩
  invFun a := ⟨baseMap (fun i => (a i).val), rfl, fun i => (a i).property⟩
  left_inv w := by apply Subtype.ext; ext i; rfl; exact w.property.1.symm
  right_inv a := rfl
  map_mul' a b := by ext i; simp [a.property.1]

end AlternatingFourPair.Thompson
