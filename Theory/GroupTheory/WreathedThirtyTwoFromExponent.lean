module

public import Theory.GroupTheory.SmallExponentSylowShapes
public import Theory.GroupTheory.WreathedThirtyTwo
public import ABG.ChapterII.Section1.WreathedRegularModel

/-!
# Recognizing W32 from the degree-three Sylow shapes

A semidihedral group of order 32 has a rotation of order 16, so cannot
have exponent dividing eight. A wreathed group of order 32 has height two;
its proved presentation is the concrete regular wreath product C4 wr C2.
This turns the exact order and power bounds into the model required by
the source sign and graph consumers in Aschbacher--Smith F.6.18(11).
-/

public section
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem wreathedThirtyTwo_of_shape_card_exponent
    (h : Stellmacher.IsSemidihedralGroup G ∨ ABG.IsWreathedGroup G)
    (hc : Nat.card G = 32) (he : ∀ x : G, x ^ 8 = 1) :
    Nonempty (G ≃* WreathedThirtyTwo) := by
  rcases h with h | ⟨n, h⟩
  · obtain ⟨n, hn, hcard, a, _, ha, _, _, _⟩ := h
    have hd : 2 ^ (n - 1) ∣ 8 := ha ▸ orderOf_dvd_of_pow_eq_one (he a)
    have hb : 2 ^ (n - 1) ≤ 2 ^ 3 := Nat.le_of_dvd (by decide) hd
    have hn3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
    have hn5 : n = 5 := Nat.pow_right_injective (by decide : 1 < 2) (hcard.symm.trans hc)
    omega
  · have hn : 2 * n + 1 = 5 :=
      Nat.pow_right_injective (by decide : 1 < 2) (h.2.1.symm.trans hc)
    have hn2 : n = 2 := by omega
    subst n
    exact h.nonempty_mulEquiv_regularWreath

end Theory.GroupTheory
