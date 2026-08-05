/-
Solution to the Glauberman ZJ challenge.

Imports `ZJDefs` (shared with `ZJChallenge`) and the repository. `ZJDefs`
transcribes the two repository definitions verbatim, so those two bridges are
`rfl`; the third identifies the centre of `J(S)` written with Mathlib's
`Subgroup.center` with the repository's `centerIn`.
-/

import ZJDefs
import FeitThompson.BGsection6.theorem_6_2

namespace ZJ

private theorem thompsonSubgroup_eq {G : Type*} [Group G] (P : Subgroup G) :
    thompsonSubgroup P = _root_.thompsonSubgroup P := rfl

private theorem pPrimeCore_eq (p : ℕ) (G : Type*) [Group G] :
    pPrimeCore p G = _root_.pPrimeCore p G := rfl

private theorem map_center_eq_centerIn {G : Type*} [Group G] (H : Subgroup G) :
    (Subgroup.center H).map H.subtype = _root_.centerIn H := by
  ext x
  simp only [_root_.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_map,
    Subgroup.mem_center_iff, Subgroup.coe_subtype, Subtype.exists, Subtype.ext_iff,
    Subgroup.coe_mul]
  aesop

theorem glauberman_zj {G : Type*} [Group G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    ((Subgroup.center (thompsonSubgroup S.toSubgroup)).map
        (thompsonSubgroup S.toSubgroup).subtype ⊔ pPrimeCore p G).Normal := by
  rw [thompsonSubgroup_eq, map_center_eq_centerIn, pPrimeCore_eq]
  exact theorem_6_2 hodd S

end ZJ
