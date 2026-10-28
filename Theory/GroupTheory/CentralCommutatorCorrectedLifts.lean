module

public import Theory.GroupTheory.CentralCommutatorLiftCorrection

open scoped commutatorElement IsMulCommutative

universe u

namespace Subgroup

public theorem exists_commuting_involutions_mod_elementary_eight
    {G : Type u} [Group G] [Finite G] (D : Subgroup G) [D.Normal]
    (hD : IsElementaryAbelian 2 D) (hDcard : Nat.card D = 8)
    (hGcard : Nat.card G = 32)
    (hderived : _root_.commutator G ≤ D ⊓ center G)
    (hcentralizer : centralizer (D : Set G) = D)
    (hcenter : Nat.card (center G) = 2) :
    ∃ x y : G, x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ Commute x y ∧
      D ⊔ zpowers x ⊔ zpowers y = ⊤ := by
  classical
  have hDne : D ≠ ⊤ := by
    intro htop
    rw [htop, card_top, hGcard] at hDcard
    omega
  obtain ⟨first, hfirst⟩ := SetLike.exists_not_mem_of_ne_top D hDne
  obtain ⟨firstCorrection, hfirstCorrection, hfirstSquare⟩ :=
    exists_involutory_correction_of_central_commutator D hD hderived
      hcentralizer hcenter first hfirst
  have hfirstOut : first * firstCorrection ∉ D := by
    intro hmem
    apply hfirst
    simpa only [mul_inv_cancel_right] using
      D.mul_mem hmem (D.inv_mem hfirstCorrection)
  have hcard : Nat.card (D ⊔ zpowers (first * firstCorrection) : Subgroup G) = 16 := by
    rw [card_sup_zpowers_of_normalizing_involution D _ hfirstSquare hfirstOut
      (by rw [normalizer_eq_top]; trivial), hDcard]
  have hproper : D ⊔ zpowers (first * firstCorrection) ≠ ⊤ := by
    intro htop
    rw [htop, card_top, hGcard] at hcard
    omega
  let intermediate : Subgroup G := D ⊔ zpowers (first * firstCorrection)
  obtain ⟨second, hsecond⟩ :=
    SetLike.exists_not_mem_of_ne_top intermediate hproper
  obtain ⟨actualFirstCorrection, hactualFirstCorrection, secondCorrection,
      hsecondCorrection, hfirstSquare, hsecondSquare, hcommute, hgen⟩ :=
    exists_corrected_lifts_of_central_commutator D hD hDcard hGcard hderived
      hcentralizer hcenter (first * firstCorrection) second hfirstOut hsecond
  exact ⟨first * firstCorrection * actualFirstCorrection, second * secondCorrection,
    hfirstSquare, hsecondSquare, hcommute, hgen⟩

end Subgroup

#print axioms Subgroup.exists_commuting_involutions_mod_elementary_eight
