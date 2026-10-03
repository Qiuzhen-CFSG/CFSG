module

public import Theory.SpecificGroups.UnitaryThree.PermutationModel
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The scalar torus of the Hermitian root group

The units of F₉ act on the Hermitian root group by scaling. Packaging this
action as a homomorphism permits comparison of cyclic torus actions on a
single generator. The unit group has order eight.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section IV.
-/

namespace UnitaryThree

/-- The scalar action of the order-eight torus on the root group. -/
public def scaleHom : FiniteField.Nineˣ →* MulAut Root where
  toFun := scaleAut
  map_one' := by
    apply MulEquiv.ext
    intro p
    exact scale_one p
  map_mul' r s := by
    apply MulEquiv.ext
    intro p
    exact scale_mul r s p

@[simp] public theorem scaleHom_apply (r : FiniteField.Nineˣ) (p : Root) :
    scaleHom r p = scale r p := by rfl

/-- Different scalars induce different root automorphisms. -/
public theorem scaleHom_injective : Function.Injective scaleHom := by
  intro r s hrs
  let p : Root := ⟨(1, 1), by decide⟩
  have he := congrArg (fun f : MulAut Root => (f p).val.1) hrs
  change (r : FiniteField.Nine) * 1 = (s : FiniteField.Nine) * 1 at he
  exact Units.ext (by simpa only [mul_one] using he)

/-- The scalar torus has order eight. -/
public theorem torus_card : Nat.card FiniteField.Nineˣ = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units, FiniteField.Nine.card]

end UnitaryThree
