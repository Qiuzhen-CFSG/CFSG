module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model

/-!
# Words for a normal eight in the literal max4 subgroup

The seed is the sixth power of the signed word
[-1,2,1,1,1,-2,-1,-2,-1,-1] in the two actual program outputs.
Its seven conjugates use [], [y], [y,x], [y,y], [y,y,x], [y,y,y],
and [y,y,x,y], with right conjugation w⁻¹ z w. All words are constructed
inside max4, so relative membership needs no ambient order assertion.

Source context: the retained ATLAS J4G1-max4W1 program and
Kleidman–Wilson (1988), pp.484–510. The identities are certified separately.
-/

@[expose] public section

namespace Janko4.LocalStructure.SymmetricLinear.NormalEight
open Janko4.GeneratorCertificates

def x : max4Subgroup :=
  ⟨(max4Program a b).1, Subgroup.subset_closure (by simp)⟩

def y : max4Subgroup :=
  ⟨(max4Program a b).2, Subgroup.subset_closure (by simp)⟩

theorem closure_x_y : Subgroup.closure ({x, y} : Set max4Subgroup) = ⊤ := by
  have h : max4Subgroup.subtype ⁻¹' {(max4Program a b).1, (max4Program a b).2} =
      ({x, y} : Set max4Subgroup) := by
    ext g
    change (g.val = x.val ∨ g.val = y.val) ↔ (g = x ∨ g = y)
    simp only [Subtype.val_inj]
  rw [← h]
  exact Subgroup.closure_preimage_eq_top _

def matrix : max4Subgroup →* BinaryMatrix := toMatrix.comp max4Subgroup.subtype

theorem matrix_injective : Function.Injective matrix :=
  toMatrix_injective.comp Subtype.val_injective

def seedBase : max4Subgroup := x⁻¹ * y * x * x * x * y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * x⁻¹

def seed : max4Subgroup := seedBase ^ 6

def e2 : max4Subgroup := y⁻¹ * seed * y

def e3 : max4Subgroup := x⁻¹ * e2 * x

def e4 : max4Subgroup := y⁻¹ * e2 * y

def e5 : max4Subgroup := x⁻¹ * e4 * x

def e6 : max4Subgroup := y⁻¹ * e4 * y

def e7 : max4Subgroup := y⁻¹ * e5 * y

def element : Fin 8 → max4Subgroup := ![1, seed, e2, e3, e4, e5, e6, e7]

@[simp] theorem element_zero : element 0 = 1 := rfl

end Janko4.LocalStructure.SymmetricLinear.NormalEight
