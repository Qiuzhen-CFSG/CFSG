module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.Reconstruction
public import Theory.SpecificGroups.SymplecticSix.OrderRank
public import Theory.SpecificGroups.SymplecticSix.Simplicity
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Mathlib.GroupTheory.IndexNormal

/-!
# The full symplectic image in C₃ recognition

The point stabilizer's actual A₆ or S₆ quotient, together with its two-core
of order at least 32, gives group order at least 725760. The marked faithful
six-space action therefore has index at most two in the actual Sp₆(2).
Its proved order and simplicity force this index to be one.

The hypotheses retained below are the earlier incidence conclusions of
I.5.8–14 and the local core bound proved in the last paragraph of I.5.15.
Neither an ambient order nor a recognition conclusion is an input.
Deriving these earlier facts from D1–D5 remains explicit.

Source: Aschbacher–Smith I.5.15 and the C₃ case of I.5.1, printed p.424.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_quotient_card_ge :
    360 ≤ Nat.card (S.family 0 ⧸ pCore 2 (S.family 0)) := by
  rcases S.point_C3 rfl with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide

theorem card_ge_half_sp (d : GeometryData S)
    (hQ : 32 ≤ Nat.card (pCore 2 (S.family 0))) : 725760 ≤ Nat.card G := by
  have hlocal := (pCore 2 (S.family 0)).card_mul_index
  have hglobal := (S.family 0).card_mul_index
  change Nat.card (S.family 0) * Nat.card S.Point = Nat.card G at hglobal
  rw [d.card_points] at hglobal
  have hlo : 32 * 360 ≤ Nat.card (S.family 0) := by
    calc
      _ ≤ Nat.card (pCore 2 (S.family 0)) *
          Nat.card (S.family 0 ⧸ pCore 2 (S.family 0)) :=
        Nat.mul_le_mul hQ (point_quotient_card_ge S)
      _ = _ := hlocal
  calc
    _ = (32 * 360) * 63 := by decide
    _ ≤ Nat.card (S.family 0) * 63 := Nat.mul_le_mul_right _ hlo
    _ = Nat.card G := hglobal

theorem symplecticMark_surjective (d : GeometryData S)
    (hQ : 32 ≤ Nat.card (pCore 2 (S.family 0))) (m : SymplecticMark S) :
    Function.Surjective m.hom := by
  let : IsSimpleGroup (PSp (ZMod 2)) := isSimpleGroup_binary
  let : IsSimpleGroup (Sp (ZMod 2)) :=
    (EvenProjective.equiv (F := ZMod 2)).isSimpleGroup
  have hc : Nat.card (Sp (ZMod 2)) = 1451520 := card_sp_of_card_two (by simp)
  have hrange : Nat.card m.hom.range = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective m.hom_injective).toEquiv).symm
  have hsize := m.hom.range.card_mul_index
  rw [hc, hrange] at hsize
  have hlo := card_ge_half_sp S d hQ
  have hi : m.hom.range.index ≤ 2 := by nlinarith
  have hpos : 0 < m.hom.range.index := Nat.pos_of_ne_zero
    (by intro h; rw [h, mul_zero] at hsize; contradiction)
  have ht : m.hom.range = ⊤ := by
    have hcases : m.hom.range.index = 1 ∨ m.hom.range.index = 2 := by omega
    rcases hcases with h | h
    · exact Subgroup.index_eq_one.mp h
    rcases (Subgroup.normal_of_index_eq_two h).eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.index_bot, hc] at h
      contradiction
    · exact ht
  exact MonoidHom.range_eq_top.mp ht

/-- The actual I.5.15 recognition, with its earlier geometric and local inputs explicit. -/
def equivSp6_of_geometry (d : GeometryData S)
    (hQ : 32 ≤ Nat.card (pCore 2 (S.family 0))) : G ≃* Sp (ZMod 2) :=
  let m := Classical.choice (exists_symplecticMark S d)
  MulEquiv.ofBijective m.hom ⟨m.hom_injective, symplecticMark_surjective S d hQ m⟩

end Quasithin.I5.C3Recognition
