module

public import Theory.SpecificGroups.UnitaryThree.PermutationModel
public import Theory.GroupTheory.PGroup.OrderTwentySevenNormalForm

/-!
# Recognition of the Hermitian root group of order twenty-seven

Every nonabelian group of order 27 and exponent three is isomorphic to the
Hermitian root group over F₉. Choose two noncommuting elements and put their
central commutator in the third coordinate. The normal-form multiplication
law agrees with the one for two explicit Hermitian roots. Those concrete
normal forms enumerate the 27 roots, giving a homomorphism into the abstract
group. Its image is nonabelian, hence is the whole group; equal orders then
make it an isomorphism.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section IV, printed pp. 7–10.
-/

open scoped commutatorElement

namespace UnitaryThree

private def firstRoot : Root := ⟨(1, 1), by decide⟩
private def secondRoot : Root := ⟨(⟨0, 1⟩, 1), by decide⟩

private def rootNormalForm : OrderTwentySeven.Coordinates → Root :=
  OrderTwentySeven.evaluate firstRoot secondRoot ⁅secondRoot, firstRoot⁆

set_option maxRecDepth 10000 in
private theorem rootNormalForm_bijective : Function.Bijective rootNormalForm := by
  decide +kernel

private theorem root_noncommutative : ¬ IsMulCommutative Root := by
  have h : firstRoot * secondRoot ≠ secondRoot * firstRoot := by decide +kernel
  intro hcomm
  exact h (hcomm.is_comm.comm _ _)

private noncomputable def rootNormalEquiv : OrderTwentySeven.Coordinates ≃ Root :=
  Equiv.ofBijective rootNormalForm rootNormalForm_bijective

private theorem rootNormalForm_product (s t : OrderTwentySeven.Coordinates) :
    rootNormalForm (OrderTwentySeven.coordinateProduct s t) =
      rootNormalForm s * rootNormalForm t := by
  apply OrderTwentySeven.evaluate_coordinateProduct
  · exact OrderTwentySeven.commutator_mem_center
      (by rw [Nat.card_eq_fintype_card, root_card]) root_noncommutative _ _
  · simp [commutatorElement_def, mul_assoc]
  · exact root_cube _
  · exact root_cube _
  · exact root_cube _

/-- A nonabelian group of order 27 in which every element cubes to one is the
Hermitian root group over F₉. No additional hypothesis on its center is needed. -/
public theorem nonempty_mulEquiv_root {P : Type*} [Group P] [Finite P]
    (hP : Nat.card P = 27) (hcube : ∀ p : P, p ^ 3 = 1)
    (hnoncomm : ∃ x y : P, x * y ≠ y * x) : Nonempty (P ≃* Root) := by
  classical
  obtain ⟨x, y, hxy⟩ := hnoncomm
  have hncomm : ¬ IsMulCommutative P := fun h => hxy (h.is_comm.comm x y)
  let c := ⁅y, x⁆
  have hc : c ∈ Subgroup.center P :=
    OrderTwentySeven.commutator_mem_center hP hncomm y x
  have hs : y * x = c * x * y := by simp [c, commutatorElement_def, mul_assoc]
  let e := rootNormalEquiv
  let f : Root →* P :=
    { toFun := fun p => OrderTwentySeven.evaluate x y c (e.symm p)
      map_one' := by
        have he : e (0, 0, 0) = 1 := by
          change rootNormalForm (0, 0, 0) = 1
          simp [rootNormalForm, OrderTwentySeven.evaluate]
        rw [← he, e.symm_apply_apply]
        simp [OrderTwentySeven.evaluate]
      map_mul' := by
        intro p q
        have he : e.symm (p * q) =
            OrderTwentySeven.coordinateProduct (e.symm p) (e.symm q) := by
          apply e.injective
          rw [e.apply_symm_apply]
          change p * q = rootNormalForm
            (OrderTwentySeven.coordinateProduct (e.symm p) (e.symm q))
          rw [rootNormalForm_product]
          exact (congrArg₂ (· * ·) (e.apply_symm_apply p) (e.apply_symm_apply q)).symm
        rw [he]
        exact OrderTwentySeven.evaluate_coordinateProduct x y c hc hs
          (hcube x) (hcube y) (hcube c) _ _ }
  have hfe (t : OrderTwentySeven.Coordinates) :
      f (e t) = OrderTwentySeven.evaluate x y c t := by
    change OrderTwentySeven.evaluate x y c (e.symm (e t)) = _
    rw [e.symm_apply_apply]
  have hx : x ∈ f.range := by
    refine ⟨e (1, 0, 0), ?_⟩
    rw [hfe]
    simp [OrderTwentySeven.evaluate]
  have hy : y ∈ f.range := by
    refine ⟨e (0, 1, 0), ?_⟩
    rw [hfe]
    simp [OrderTwentySeven.evaluate]
  have hrange : f.range = ⊤ :=
    OrderTwentySeven.subgroup_eq_top_of_noncommuting hP f.range ⟨x, hx⟩ ⟨y, hy⟩
      (fun h => hxy (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp hrange
  have hbij : Function.Bijective f := hsurj.bijective_of_nat_card_le (by
    rw [Nat.card_eq_fintype_card, root_card, hP])
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

end UnitaryThree
