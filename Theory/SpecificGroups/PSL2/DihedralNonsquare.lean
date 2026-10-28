module

public import GorensteinWalter.PSL2DihedralSylow

/-!
# Non-involutory elements in odd PSL₂ Sylow subgroups

The actual dihedral Sylow model and eight-divisibility put a rotation of
order at least four in every Sylow two-subgroup. This supplies the local
noncommutativity input when an elementary normal actor permutes components.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter BenderSuzuki.MatrixGroups
namespace Theory.PSL2
/-- A Sylow of odd PSL₂ with order divisible by eight contains an element of order at least four. -/
theorem exists_sylow_nonsquare_of_eight_dvd
    {F : Type*} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F))
    (h8 : 8 ∣ Nat.card (PSL2MatrixGroup F)) (Q : Sylow 2 (PSL2MatrixGroup F)) :
    ∃ s : PSL2MatrixGroup F, s ∈ (Q : Subgroup (PSL2MatrixGroup F)) ∧ s ^ 2 ≠ 1 := by
  obtain ⟨m, _, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hodd Q
  have h8Q : 8 ∣ Nat.card Q := Q.pow_dvd_card_of_pow_dvd_card (n := 3) h8
  have hh : 8 ≤ 2 * 2 ^ m := by
    have := Nat.le_of_dvd (Nat.card_pos (α := Q)) h8Q
    simpa only [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] using this
  have hm : 2 ≤ m := by
    by_contra! h
    (interval_cases m; norm_num at hh)
  let s : Q := e.symm (DihedralGroup.r 1)
  refine ⟨s, s.property, ?_⟩
  intro hs
  have he : (DihedralGroup.r (1 : ZMod (2 ^ m))) ^ 2 = 1 := by
    have hs' : s ^ 2 = 1 := Subtype.ext hs
    simpa only [s, map_pow, map_one, MulEquiv.apply_symm_apply] using congrArg e hs'
  have hd := orderOf_dvd_of_pow_eq_one he
  rw [DihedralGroup.orderOf_r_one] at hd
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  have hge := Nat.pow_le_pow_right (by decide : 0 < 2) hm
  norm_num at hge
  omega
end Theory.PSL2
