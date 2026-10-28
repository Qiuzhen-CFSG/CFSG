module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The binary tetrahedral matrix model

The order-three automorphism of Q8 cycles its noncentral generator pairs.
Its semidirect product with the cyclic group of order three is isomorphic
to SL2(ZMod3), via three explicit two-by-two matrices. Finite calculations
verify the quaternion relations, action compatibility, and surjectivity;
the equal orders then give an equivalence.

Extracted from the independent binary-tetrahedral model in GLS3 5.2.4,
`Theory/Alternating/proposition_5_2_4.lean`. Public names retain their
historical namespace for source consumers. The action is exposed because
both finite verification and downstream presentation maps compute with it.
This lower model supports the q=3 central-cover step of ABG II.3 Proposition 2.
-/

namespace GLS3.Chapter5.SchurPresentation

@[expose] public def q8Cycle : MulAut (QuaternionGroup 2) := by
  let f : QuaternionGroup 2 → QuaternionGroup 2
    | .a i => if i.val % 2 = 0 then .a i else .xa i
    | .xa i => if i.val % 2 = 0 then .a (3 + i) else .xa (i + 1)
  have hf (x y : QuaternionGroup 2) : f (x * y) = f x * f y := by
    rcases x with i | i <;> rcases y with j | j <;>
      fin_cases i <;> fin_cases j <;> decide
  have hf3 (x : QuaternionGroup 2) : f (f (f x)) = x := by
    rcases x with i | i <;> fin_cases i <;> decide
  exact {
    toFun := f
    invFun := f ∘ f
    left_inv := hf3
    right_inv := hf3
    map_mul' := hf }

public theorem q8Cycle_a_one :
    q8Cycle (QuaternionGroup.a 1) = QuaternionGroup.xa 1 := by decide

public theorem q8Cycle_xa_zero :
    q8Cycle (QuaternionGroup.xa 0) = QuaternionGroup.a 3 := by decide

@[expose] public def q8C3Action :
    Multiplicative (ZMod 3) →* MulAut (QuaternionGroup 2) where
  toFun k := q8Cycle ^ (Multiplicative.toAdd k).val
  map_one' := by
    ext x
    rcases x with i | i <;> fin_cases i <;> decide
  map_mul' := by
    intro x y
    change ZMod 3 at x y
    fin_cases x <;> fin_cases y <;>
      ext q <;> rcases q with i | i <;> fin_cases i <;> decide

public abbrev SL23 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private def slI : SL23 :=
  ⟨![![0, 1], ![2, 0]], by decide⟩

private def slJ : SL23 :=
  ⟨![![2, 1], ![1, 1]], by decide⟩

private def slS : SL23 :=
  ⟨![![1, 1], ![0, 1]], by decide⟩

private def q8MatrixHom : QuaternionGroup 2 →* SL23 where
  toFun
    | .a i => slI ^ i.val
    | .xa i => slJ * slI ^ i.val
  map_one' := by decide
  map_mul' := by
    intro x y
    rcases x with i | i <;> rcases y with j | j <;>
      fin_cases i <;> fin_cases j <;> decide

private def c3MatrixHom : Multiplicative (ZMod 3) →* SL23 where
  toFun k := slS ^ (Multiplicative.toAdd k).val
  map_one' := by decide
  map_mul' := by
    intro x y
    change ZMod 3 at x y
    fin_cases x <;> fin_cases y <;> decide

private theorem matrix_action_compat (k : Multiplicative (ZMod 3))
    (x : QuaternionGroup 2) :
    q8MatrixHom (q8C3Action k x) =
      c3MatrixHom k * q8MatrixHom x * (c3MatrixHom k)⁻¹ := by
  change ZMod 3 at k
  fin_cases k <;> rcases x with i | i <;> fin_cases i <;> decide

private def binaryTetrahedralToSL :
    (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) →* SL23 :=
  SemidirectProduct.lift q8MatrixHom c3MatrixHom (by
    intro k
    apply MonoidHom.ext
    intro x
    exact matrix_action_compat k x)

@[instance_reducible]
private def binaryTetrahedralFintype :
    Fintype (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) :=
  Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

private theorem sl23_fintype_card : Fintype.card SL23 = 24 := by decide

private theorem sl23_card : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  exact sl23_fintype_card

private theorem binaryTetrahedralToSL_surjective :
    Function.Surjective binaryTetrahedralToSL := by
  let := binaryTetrahedralFintype
  all_goals decide
public noncomputable def binaryTetrahedralEquivSL :
    (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) ≃* SL23 := by
  letI := binaryTetrahedralFintype
  haveI : Fintype SL23 := Fintype.ofFinite _
  apply MulEquiv.ofBijective binaryTetrahedralToSL
  apply (Fintype.bijective_iff_surjective_and_card binaryTetrahedralToSL).2
  constructor
  · exact binaryTetrahedralToSL_surjective
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      SemidirectProduct.card, sl23_card]
    norm_num [QuaternionGroup.card]


end GLS3.Chapter5.SchurPresentation

