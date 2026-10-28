module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.NeighborCount
public import Mathlib.Logic.Equiv.Option
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Every original C₃ point has a noncollinear point

If every point were collinear with x, the thirty-neighbor count would give
31 points in total. The point stabilizer order is prime to seven, from its
actual A₆/S₆ quotient and two-core. Its index 31 would make the whole group
order prime to seven, contradicting the PSL₃(2) plane quotient.

Source: the noncomplete-graph argument in I.5.9(3i), printed p.422. The
argument uses cardinal identities directly and does not assume global
finiteness in advance.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_group_card_coprime_seven : (Nat.card (S.family 0)).Coprime 7 := by
  have hc : (Nat.card (S.family 0 ⧸ pCore 2 (S.family 0))).Coprime 7 := by
    rcases S.point_C3 rfl with he | he
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
  have h := (pCore 2 (S.family 0)).card_mul_index
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := S.family 0)).exists_card_eq
  rw [← h, hn]
  exact ((by decide : Nat.Coprime 2 7).pow_left n).mul_left hc

include S in
theorem seven_dvd_ambient_card : 7 ∣ Nat.card G := by
  obtain ⟨e⟩ := S.plane_quotient
  have hd : 7 ∣ Nat.card (S.family 2 ⧸ pCore 2 (S.family 2)) := by
    rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_PSL]
    decide
  exact (hd.trans (card_quotient_dvd_card _)).trans (S.family 2).card_subgroup_dvd_card

theorem c3_exists_noncollinear (x : S.Point) : ∃ y : S.Point, ¬ S.Collinear x y := by
  classical
  by_contra! hall
  let N := {y : S.Point // x ≠ y ∧ S.Collinear x y}
  have hcN : Nat.card N = 30 := S.c3_neighbors_card x
  let : Finite N := Nat.finite_of_card_ne_zero (by rw [hcN]; decide)
  let e : N ≃ {y : S.Point // y ≠ x} := {
    toFun y := ⟨y.val, y.property.1.symm⟩
    invFun y := ⟨y.val, y.property.symm, hall y.val⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let f := (Equiv.optionCongr e).trans (Equiv.optionSubtypeNe x)
  have hc : Nat.card S.Point = 31 := by
    let := Fintype.ofFinite N
    rw [← Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_option,
      ← Nat.card_eq_fintype_card, hcN]
  have hg := (S.family 0).card_mul_index
  change Nat.card (S.family 0) * Nat.card S.Point = Nat.card G at hg
  rw [hc] at hg
  have hp : (Nat.card G).Coprime 7 := by
    rw [← hg]
    exact S.point_group_card_coprime_seven.mul_left (by decide)
  exact (by decide : ¬ Nat.Coprime 7 7) (hp.coprime_dvd_left S.seven_dvd_ambient_card)

end Quasithin.I5.DSystem
