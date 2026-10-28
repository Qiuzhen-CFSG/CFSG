module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreAbelianBounds
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary subgroups of the original quaternion--cyclic point core

An elementary subgroup meets the cyclic-four center in order at most two.
Its join with that center is abelian and therefore has order at most sixteen.
The product formula gives an order-eight bound for the original elementary
subgroup, without an extra rank hypothesis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims

/-- The original quaternion--cyclic point-core shape has elementary-two
rank at most three. -/
theorem CoreShape.elementary_card_le_eight {Q : Type*} [Group Q] [Finite Q]
    (h : CoreShape Q) (E : Subgroup Q) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 8 := by
  let Z := center Q
  obtain ⟨e⟩ := h.center_model
  let : IsCyclic Z := e.isCyclic.mpr inferInstance
  have hZ4 : Nat.card Z = 4 := by rw [Nat.card_congr e.toEquiv]; simp
  let := hE
  let C := E ⊓ Z
  let : IsCyclic C := isCyclic_of_injective (inclusion (show C ≤ Z from inf_le_right))
    (inclusion_injective _)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion (show C ≤ E from inf_le_left)) (inclusion_injective _)
  have hC2 : Nat.card C ≤ 2 := by
    have hd := IsElementaryAbelian.exponent_dvd_p 2 C
    rw [IsCyclic.exponent_eq_card] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hZC : Z ≤ centralizer (E : Set Q) := fun z hz x _ => mem_center_iff.mp hz x
  let A := E ⊔ Z
  let : IsMulCommutative A := le_centralizer_iff_isMulCommutative.mp
    (sup_le (le_centralizer_iff.mpr (sup_le E.le_centralizer hZC))
      (le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hZC) Z.le_centralizer)))
  have hA16 : Nat.card A ≤ 16 := h.abelian_card_le A
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes E Z
    (hZC.trans (centralizer_le_normalizer _))
  change Nat.card E * Nat.card Z = Nat.card C * Nat.card A at hp
  rw [hZ4] at hp
  nlinarith

end CFSG.Quasithin.HigmanSims
