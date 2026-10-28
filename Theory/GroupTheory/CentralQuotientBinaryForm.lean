module
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic

/-!
A scalar character of the derived group gives an alternating form on a central
binary quotient. The scalar character is separate from the central kernel.
The commutator map descends in each variable because the kernel is central;
central commutators prove additivity. A nonzero commutator value makes the
form nonzero, and automorphisms fixing the derived group preserve its values.
This is the elementary class-two construction used in Stellmacher p.42.
-/

open scoped commutatorElement IsMulCommutative

namespace Subgroup
variable {Q : Type*} [Group Q]

private theorem central_commutator_mul_right
    (N : Subgroup Q) (hcentral : N ≤ Subgroup.center Q)
    (hderived : _root_.commutator Q ≤ N) (left right other : Q) :
    ⁅left, right * other⁆ = ⁅left, right⁆ * ⁅left, other⁆ := by
  have hcomm := Subgroup.mem_center_iff.mp
    (hcentral (hderived (Subgroup.commutator_mem_commutator (Subgroup.mem_top left)
      (Subgroup.mem_top other)))) right
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅left, right⁆ * right * ⁅left, other⁆ * right⁻¹ =
        ⁅left, right⁆ * (right * ⁅left, other⁆) * right⁻¹ := by simp [mul_assoc]
    _ = ⁅left, right⁆ * (⁅left, other⁆ * right) * right⁻¹ := by rw [hcomm]
    _ = _ := by simp [mul_assoc]

private theorem central_commutator_mul_left
    (N : Subgroup Q) (hcentral : N ≤ Subgroup.center Q)
    (hderived : _root_.commutator Q ≤ N) (left right other : Q) :
    ⁅left * right, other⁆ = ⁅left, other⁆ * ⁅right, other⁆ := by
  have hcomm := Subgroup.mem_center_iff.mp
    (hcentral (hderived (Subgroup.commutator_mem_commutator (Subgroup.mem_top right)
      (Subgroup.mem_top other)))) left
  have hswap := Subgroup.mem_center_iff.mp
    (hcentral (hderived (Subgroup.commutator_mem_commutator (Subgroup.mem_top left)
      (Subgroup.mem_top other)))) ⁅right, other⁆
  rw [commutatorElement_mul_left_eq_conj_mul]
  rw [hcomm]
  simpa [mul_assoc] using hswap

private def centralCommutatorHom
    (N : Subgroup Q) (hcentral : N ≤ Subgroup.center Q)
    (hderived : _root_.commutator Q ≤ N)
    (coordinates : _root_.commutator Q →* Multiplicative (ZMod 2)) (left : Q) :
    Q →* Multiplicative (ZMod 2) where
  toFun right := coordinates ⟨⁅left, right⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top left) (Subgroup.mem_top right)⟩
  map_one' := by
    simp only [commutatorElement_one_right]
    exact coordinates.map_one
  map_mul' right other := by
    rw [← map_mul]
    apply congrArg coordinates
    apply Subtype.ext
    exact central_commutator_mul_right N hcentral hderived left right other

private theorem centralCommutatorHom_ker
    (N : Subgroup Q) (hcentral : N ≤ Subgroup.center Q)
    (hderived : _root_.commutator Q ≤ N)
    (coordinates : _root_.commutator Q →* Multiplicative (ZMod 2)) (left : Q) :
    N ≤ (centralCommutatorHom N hcentral hderived coordinates left).ker := by
  intro right hright
  change coordinates ⟨⁅left, right⁆, _⟩ = 1
  rw [← map_one coordinates]
  apply congrArg coordinates
  apply Subtype.ext
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp (hcentral hright) left)

private def quotientCommutatorHom
    (N : Subgroup Q) [N.Normal] (hcentral : N ≤ Subgroup.center Q)
    (hderived : _root_.commutator Q ≤ N)
    (coordinates : _root_.commutator Q →* Multiplicative (ZMod 2)) :
    Q →* ((Q ⧸ N) →* Multiplicative (ZMod 2)) where
  toFun left := QuotientGroup.lift N
    (centralCommutatorHom N hcentral hderived coordinates left)
    (centralCommutatorHom_ker N hcentral hderived coordinates left)
  map_one' := by
    apply MonoidHom.ext
    intro point
    refine QuotientGroup.induction_on point ?_
    intro right
    change coordinates ⟨⁅1, right⁆, _⟩ = 1
    simp only [commutatorElement_one_left]
    exact coordinates.map_one
  map_mul' left other := by
    apply MonoidHom.ext
    intro point
    refine QuotientGroup.induction_on point ?_
    intro right
    change coordinates ⟨⁅left * other, right⁆, _⟩ =
      coordinates ⟨⁅left, right⁆, _⟩ * coordinates ⟨⁅other, right⁆, _⟩
    rw [← map_mul]
    apply congrArg coordinates
    apply Subtype.ext
    exact central_commutator_mul_left N hcentral hderived left other right

private def quotientCommutatorBihom
    (N : Subgroup Q) [N.Normal] (hcentral : N ≤ Subgroup.center Q)
    (hderived : _root_.commutator Q ≤ N)
    (coordinates : _root_.commutator Q →* Multiplicative (ZMod 2)) :
    (Q ⧸ N) →* ((Q ⧸ N) →* Multiplicative (ZMod 2)) :=
  QuotientGroup.lift N (quotientCommutatorHom N hcentral hderived coordinates) (by
    intro left hleft
    apply MonoidHom.ext
    intro point
    refine QuotientGroup.induction_on point ?_
    intro right
    change coordinates ⟨⁅left, right⁆, _⟩ = 1
    rw [← map_one coordinates]
    apply congrArg coordinates
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hcentral hleft) right).symm)

private def bihomToBilinForm
    {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (bihom : E →* (E →* Multiplicative (ZMod 2))) :
    LinearMap.BilinForm (ZMod 2) (Additive E) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun left => AddMonoidHom.toZModLinearMap 2
        { toFun := fun right => (bihom left.toMul right.toMul).toAdd
          map_zero' := by exact congrArg Multiplicative.toAdd (map_one (bihom left.toMul))
          map_add' := fun right other =>
            congrArg Multiplicative.toAdd (map_mul (bihom left.toMul) right.toMul other.toMul) }
      map_zero' := by
        apply LinearMap.ext
        intro right
        exact congrArg (fun hom : E →* Multiplicative (ZMod 2) =>
          (hom right.toMul).toAdd) bihom.map_one
      map_add' := by
        intro left other
        apply LinearMap.ext
        intro right
        exact congrArg (fun hom : E →* Multiplicative (ZMod 2) =>
          (hom right.toMul).toAdd) (bihom.map_mul left.toMul other.toMul) }


public theorem exists_nonzero_invariant_central_quotient_form
    (N : Subgroup Q) [N.Characteristic] [IsElementaryAbelian 2 (Q ⧸ N)]
    (hcentral : N ≤ Subgroup.center Q) (hderived : _root_.commutator Q ≤ N)
    (coordinates : _root_.commutator Q →* Multiplicative (ZMod 2))
    (left right : Q)
    (hne : coordinates ⟨⁅left, right⁆, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top left) (Subgroup.mem_top right)⟩ ≠ 1) :
    ∃ form : LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ N)),
      form ≠ 0 ∧ form.IsAlt ∧
      ∀ (aut : MulAut Q), (∀ point : _root_.commutator Q, aut point = point) →
        ∀ first second : Q ⧸ N,
          form (Additive.ofMul (Subgroup.quotientAut N aut first))
              (Additive.ofMul (Subgroup.quotientAut N aut second)) =
            form (Additive.ofMul first) (Additive.ofMul second) := by
  let form := bihomToBilinForm (quotientCommutatorBihom N hcentral hderived coordinates)
  have heval (first second : Q) :
      form (Additive.ofMul (QuotientGroup.mk' N first))
          (Additive.ofMul (QuotientGroup.mk' N second)) =
        (coordinates ⟨⁅first, second⁆, Subgroup.commutator_mem_commutator
          (Subgroup.mem_top first) (Subgroup.mem_top second)⟩).toAdd := rfl
  refine ⟨form, ?_, ?_, ?_⟩
  · intro hzero
    apply hne
    have hvalue := heval left right
    rw [hzero] at hvalue
    exact congrArg Multiplicative.ofAdd hvalue.symm
  · intro point
    change form (Additive.ofMul point.toMul) (Additive.ofMul point.toMul) = 0
    generalize point.toMul = quotient
    refine QuotientGroup.induction_on quotient ?_
    intro representative
    change form (Additive.ofMul (QuotientGroup.mk' N representative))
      (Additive.ofMul (QuotientGroup.mk' N representative)) = 0
    rw [heval]
    simp only [commutatorElement_self]
    exact congrArg Multiplicative.toAdd coordinates.map_one
  · intro aut hfix first second
    refine QuotientGroup.induction_on first ?_
    intro first
    refine QuotientGroup.induction_on second ?_
    intro second
    change form (Additive.ofMul (Subgroup.quotientAut N aut (QuotientGroup.mk' N first)))
      (Additive.ofMul (Subgroup.quotientAut N aut (QuotientGroup.mk' N second))) =
      form (Additive.ofMul (QuotientGroup.mk' N first))
        (Additive.ofMul (QuotientGroup.mk' N second))
    simp only [Subgroup.quotientAut_apply_mk, heval]
    apply congrArg (fun point : _root_.commutator Q => (coordinates point).toAdd)
    apply Subtype.ext
    change ⁅aut first, aut second⁆ = ⁅first, second⁆
    rw [← map_commutatorElement]
    exact hfix ⟨⁅first, second⁆, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top first) (Subgroup.mem_top second)⟩

end Subgroup
