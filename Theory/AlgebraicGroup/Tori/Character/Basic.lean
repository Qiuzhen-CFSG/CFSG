module

public import Theory.AlgebraicGroup.Morphism.Operations
public import Theory.AlgebraicGroup.Tori.Character.Defs

universe u

/-! The pointwise commutative group structure on algebraic-group characters. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Characters form a commutative group under pointwise multiplication. -/
public noncomputable instance torusCharacterCommGroup
    (T : Variety k) [AlgebraicGroup T] :
    CommGroup (TorusCharacter (k := k) T) := by
  have hcomm : ∀ x y : Variety.Point (KMult k), x * y = y * x := by
    rw [← isMulCommutative_iff]
    exact dVariety_isMulCommutative 1
  let oneChar : TorusCharacter (k := k) T :=
    { toVariety := Variety.Morphism.const _ _ 1
      map_one := rfl
      map_mul := by
        intro _ _
        exact (one_mul (1 : Variety.Point (KMult k))).symm }
  let mulChar (f g : TorusCharacter (k := k) T) :
      TorusCharacter (k := k) T :=
    { toVariety := (mulMorphism (KMult k)).comp
        (f.toVariety.pair g.toVariety)
      map_one := by
        change f.toVariety.toFun 1 * g.toVariety.toFun 1 = 1
        rw [f.map_one, g.map_one, one_mul]
      map_mul := by
        intro x y
        change f.toVariety.toFun (x * y) * g.toVariety.toFun (x * y) =
          (f.toVariety.toFun x * g.toVariety.toFun x) *
            (f.toVariety.toFun y * g.toVariety.toFun y)
        rw [f.map_mul, g.map_mul]
        calc
          (f.toVariety.toFun x * f.toVariety.toFun y) *
              (g.toVariety.toFun x * g.toVariety.toFun y) =
              f.toVariety.toFun x *
                (f.toVariety.toFun y * g.toVariety.toFun x) *
                  g.toVariety.toFun y := by simp [mul_assoc]
          _ = f.toVariety.toFun x *
                (g.toVariety.toFun x * f.toVariety.toFun y) *
                  g.toVariety.toFun y :=
            congrArg
              (fun z ↦ f.toVariety.toFun x * z * g.toVariety.toFun y)
              (hcomm (f.toVariety.toFun y) (g.toVariety.toFun x))
          _ = (f.toVariety.toFun x * g.toVariety.toFun x) *
                (f.toVariety.toFun y * g.toVariety.toFun y) := by
              simp [mul_assoc] }
  let invChar (f : TorusCharacter (k := k) T) :
      TorusCharacter (k := k) T :=
    { toVariety := (invMorphism (KMult k)).comp f.toVariety
      map_one := by
        change (f.toVariety.toFun 1)⁻¹ = 1
        rw [f.map_one, inv_one]
      map_mul := by
        intro x y
        change (f.toVariety.toFun (x * y))⁻¹ =
          (f.toVariety.toFun x)⁻¹ * (f.toVariety.toFun y)⁻¹
        rw [f.map_mul, mul_inv_rev]
        exact hcomm _ _ }
  exact
    { one := oneChar
      mul := mulChar
      inv := invChar
      mul_assoc := by
        intro f g h
        apply AlgebraicGroup.Morphism.ext
        funext x
        change (f.toVariety.toFun x * g.toVariety.toFun x) *
            h.toVariety.toFun x =
          f.toVariety.toFun x *
            (g.toVariety.toFun x * h.toVariety.toFun x)
        exact mul_assoc _ _ _
      one_mul := by
        intro f
        apply AlgebraicGroup.Morphism.ext
        funext x
        change 1 * f.toVariety.toFun x = f.toVariety.toFun x
        exact one_mul _
      mul_one := by
        intro f
        apply AlgebraicGroup.Morphism.ext
        funext x
        change f.toVariety.toFun x * 1 = f.toVariety.toFun x
        exact mul_one _
      inv_mul_cancel := by
        intro f
        apply AlgebraicGroup.Morphism.ext
        funext x
        change (f.toVariety.toFun x)⁻¹ * f.toVariety.toFun x = 1
        exact inv_mul_cancel _
      mul_comm := by
        intro f g
        apply AlgebraicGroup.Morphism.ext
        funext x
        change f.toVariety.toFun x * g.toVariety.toFun x =
          g.toVariety.toFun x * f.toVariety.toFun x
        exact hcomm _ _ }

end Theory.AlgebraicGroup
