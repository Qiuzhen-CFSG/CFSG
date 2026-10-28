module
public import Theory.Representation.SL3.PointRadicalDualDisplacement

/-!
# The size of a fixed subgroup on the doubled dual

Each covector fixed by the point radical annihilates the defining point.
The two remaining coordinates in each summand give an injection into F⁴,
even when the fixed subgroup is only additive, rather than F-linear.

The original nonblock application bounds the component-core intersection
with Q through its actual doubled-dual quotient.
Source: Aschbacher--Smith, C.1.34(3), pp.136--137, and the point-radical
action in the conclusion of original 4.3.2, pp.618--619.
-/

public section
namespace Representation.SL3ParabolicNatural
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F] [Finite F]

/-- The doubled-dual point-radical fixed subgroup has at most |F|⁴ elements. -/
theorem doubledDual_pointRadical_fixed_card_le
    (B : AddSubgroup (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hB : ∀ v ∈ B, ∀ g : pointRadicalSL F,
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) g.val.val v = v) :
    Nat.card B ≤ Nat.card F ^ 4 := by
  let j : B → (Fin 2 → F) × (Fin 2 → F) := fun v =>
    (![dualVectorCoordinates v.val.1 1,dualVectorCoordinates v.val.1 2],
      ![dualVectorCoordinates v.val.2 1,dualVectorCoordinates v.val.2 2])
  have hz (v : B) : dualVectorCoordinates v.val.1 0 = 0 ∧
      dualVectorCoordinates v.val.2 0 = 0 :=
    ⟨pointRadical_dual_fixed_coordinate v.val.1
        (fun g => congrArg Prod.fst (hB v.val v.property g)),
      pointRadical_dual_fixed_coordinate v.val.2
        (fun g => congrArg Prod.snd (hB v.val v.property g))⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Prod.ext
    · apply dualVectorCoordinates.injective
      ext i
      fin_cases i
      · exact (hz x).1.trans (hz y).1.symm
      · exact congrArg (fun z => z.1 0) he
      · exact congrArg (fun z => z.1 1) he
    · apply dualVectorCoordinates.injective
      ext i
      fin_cases i
      · exact (hz x).2.trans (hz y).2.symm
      · exact congrArg (fun z => z.2 0) he
      · exact congrArg (fun z => z.2 1) he
  have hh := Nat.card_le_card_of_injective j hj
  rw [Nat.card_prod,Nat.card_fun,Nat.card_fin] at hh
  simpa only [←pow_add] using hh
end Representation.SL3ParabolicNatural
