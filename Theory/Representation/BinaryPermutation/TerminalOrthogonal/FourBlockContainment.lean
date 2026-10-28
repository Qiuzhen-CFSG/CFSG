module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockPoint
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Lifting block containment to the alternating subgroup

An internal block transposition corrects the parity of a conjugator without
changing the unordered block stabilizer. Two-perfect subgroups contained in
that stabilizer lie in its literal A₄ × A₄ two-residual.

These are the permutation-side inputs to the original weight-four residual
alignment in Aschbacher--Smith 12.6.19, printed p.828 of the combined
manuscript of 1 March 2004. They require block containment and do not claim
that an arbitrary elementary-nine section has already been placed there.
-/

public section
namespace BinaryPermutation.TerminalOrthogonal.FourBlockPoint
open Subgroup FourBlockResidual

/-- An odd internal block transposition corrects parity without losing
containment in the same unordered four-block stabilizer. -/
theorem even_conjugator_of_conjugate_le (B : Subgroup S8)
    (h : ∃ s : S8, B.map (MulAut.conj s).toMonoidHom ≤ H) :
    ∃ s : alternatingGroup (Fin 8),
      B.map (MulAut.conj (s : S8)).toMonoidHom ≤ H := by
  obtain ⟨s,hs⟩ := h
  by_cases he : s ∈ alternatingGroup (Fin 8)
  · exact ⟨⟨s,he⟩,hs⟩
  · let t : S8 := Equiv.swap 0 1
    have ht : t ∈ H := by decide
    have hts : t*s ∈ alternatingGroup (Fin 8) := by
      change Equiv.Perm.sign s ≠ 1 at he
      change Equiv.Perm.sign (t*s) = 1
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hh | hh
      · exact (he hh).elim
      · rw [map_mul,hh]
        norm_num [t,Equiv.Perm.sign_swap]
    refine ⟨⟨t*s,hts⟩,?_⟩
    have hc : (MulAut.conj (t*s)).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp (MulAut.conj s).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [hc,←map_map]
    exact (map_mono hs).trans_eq (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer ht))

/-- Two-perfect subgroups of the unordered block stabilizer lie in its literal A₄ × A₄ residual. -/
theorem twoPerfect_le_residual_of_le_stabilizer (B : Subgroup FourBlockResidual.S8)
    (hp : IsPPerfect 2 B) (hb : B ≤ FourBlockResidual.H) :
    B ≤ FourBlockResidual.R := by
  have h := embedded_pResidual_mono 2 hb
  have ht : (pResidual 2 B).map B.subtype = B := by
    rw [(pResidual_eq_top_iff 2 B).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  rw [ht,FourBlockPoint.intermediate_residual _ FourBlockResidual.R_le_H le_rfl] at h
  exact h

end BinaryPermutation.TerminalOrthogonal.FourBlockPoint
