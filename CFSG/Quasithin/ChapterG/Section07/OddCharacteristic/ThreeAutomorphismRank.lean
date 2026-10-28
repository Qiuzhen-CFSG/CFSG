module

public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.Models
public import Theory.SpecificGroups.OddThreeRank.Automorphisms

/-!
# The automorphism rank input for the three-dimensional branch of G.7.3

For each genuine model denoted by `(S)L₃^ε(p)`, the inner two-rank is at
most two and the outer contribution at most one. The special groups use
faithful descent of automorphisms through their whole centers. In particular,
the proof covers nontrivial central covers and arbitrary automorphisms.

Source: Aschbacher–Smith, G.7.3(1), printed p.348 (PDF p.359). This is the
intrinsic rank input to that argument, independent of the small-module bound.
The unitary coefficient field has order `p²` and conjugation `x ↦ x^p`.
-/

public section

open Theory.GroupTheory Theory.SpecificGroups.OddThreeRank
open BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

/-- The intrinsic automorphism two-rank bound for all four three-dimensional
odd-prime alternatives, including the special central covers. -/
theorem linearUnitaryThree_automorphism_two_rank_le_three
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmodel : IsLinearUnitaryThree L p) :
    primeRank 2 (MulAut L) ≤ 3 := by
  rcases hmodel with h | h | h | h
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    exact (primeRank_equiv 2 (MulAut.congr e)).le.trans
      (psl3_automorphism_two_rank_le_three hp ho hF)
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    exact (primeRank_equiv 2 (MulAut.congr e)).le.trans
      (sl3_automorphism_two_rank_le_three hp ho hF)
  · obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv L e.toEquiv
    let _ : IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J) :=
      IsQuasisimple.of_mulEquiv e
    exact (primeRank_equiv 2 (MulAut.congr e)).le.trans
      (quasisimple_psu3_automorphism_two_rank_le_three J hp ho hF hconj)
  · obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    let _ : IsQuasisimple J.specialSubgroup := IsQuasisimple.of_mulEquiv e
    exact (primeRank_equiv 2 (MulAut.congr e)).le.trans
      (su3_automorphism_two_rank_le_three J hp ho hF hconj)

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
