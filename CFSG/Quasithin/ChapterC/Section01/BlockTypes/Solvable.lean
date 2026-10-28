module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# A solvable block cannot have the higher even-field rank-one type

The defining quotient of an L₂(2ⁿ) block, n>1, is a nontrivial perfect
PSL₂ group. It cannot be a quotient of a solvable group. This leaves the
literal A₃ branch in the solvable C.1.18 application of 15.4.7.

Source: Aschbacher--Smith C.1.12 and 15.4.7, printed pp.124 and1158.
-/

public section
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Group.IsSolvable L]

/-- Higher even-field rank-one blocks are nonsolvable. -/
theorem IsL2EvenBlock.not_solvable {n : ℕ} (h : IsL2EvenBlock L n) : False := by
  have hn := h.1
  obtain ⟨F,_,_,hF,hPSL,_⟩ := h.2.2
  obtain ⟨K,_,_,hK,⟨e⟩⟩ := hPSL
  have hlarge : 3 < Nat.card K := by
    rw [hK]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    have h4 : 4 ≤ 2^n := hh
    omega
  let : Group.IsPerfect PSL(2,K) := GorensteinWalter.psl2_isPerfect_of_card_gt_three K hlarge
  let : Group.IsSolvable PSL(2,K) := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.not_isSolvable PSL(2,K) inferInstance
end CFSG.Quasithin.ChapterC
