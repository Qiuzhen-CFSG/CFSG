module

public import Theory.GroupTheory.ExponentFourSylowSections

/-!
# C2 times D8 is not dihedral

Its order would force a dihedral rotation of order eight, contradicting
its fourth-power identity. This distinguishes the split-sixteen source
branch from every odd PSL2 or PGL2 Sylow in F.6.18, printed p.310.
-/

public section
namespace Theory.GroupTheory

theorem split_sixteen_not_dihedral (n : ℕ)
    (e : (Multiplicative (ZMod 2) × DihedralGroup 4) ≃* DihedralGroup n) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [split_sixteen_card, DihedralGroup.nat_card] at hc
  have hn : n = 8 := by omega
  subst n
  have hp := split_sixteen_pow_four (e.symm (DihedralGroup.r 1))
  have hr : (DihedralGroup.r 1 : DihedralGroup 8) ^ 4 = 1 := by
    simpa only [map_pow, e.apply_symm_apply, map_one] using congrArg e hp
  exact (by decide : (DihedralGroup.r 1 : DihedralGroup 8) ^ 4 ≠ 1) hr

end Theory.GroupTheory
