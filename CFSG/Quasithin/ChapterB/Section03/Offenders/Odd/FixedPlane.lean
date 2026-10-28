module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import Theory.Representation.BinaryOffender.Stability
public import Theory.GroupTheory.SubgroupConjugation

/-!
# A common fixed plane for five-point offenders

Inside any two-subgroup of S₅, all best offenders on the binary augmentation
core lie in one conjugate of the disjoint-transposition group. That group has
fixed codimension two. Conjugate to a Sylow containing the standard group and
apply the odd-degree offender classification inside that Sylow.

The actual Chapter 13.2 application transfers maximal elementary subgroups
of T through its marked five-point action, giving |C_V(J(T))|≥4.
Source: Aschbacher–Smith B.3.2 and 13.2.11, printed pp.83–84 and 881.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.ChapterB.Offenders

theorem exists_five_offender_bound (P : Subgroup (Equiv.Perm (Fin 5)))
    (hP : IsPGroup 2 P) :
    ∃ D₀ : Subgroup (Equiv.Perm (Fin 5)),
      fixedCodim (BinaryPermutation.coreRepresentation (Fin 5)) D₀ = 2 ∧
      ∀ A, IsBestOffender (BinaryPermutation.coreRepresentation (Fin 5)) A →
        A ≤ P → A ≤ D₀ := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨R, hDR, _⟩ := Odd.exists_sylow_containing_D (Or.inl rfl : 5 = 5 ∨ 5 = 7)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 5)) R S
  have hcancel (A : Subgroup (Equiv.Perm (Fin 5))) :
      (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
    change (A.conjBy g⁻¹).conjBy g = A
    rw [conjBy_conjBy, mul_inv_cancel, conjBy_one]
  have hgmap : (R : Subgroup (Equiv.Perm (Fin 5))).map (MulAut.conj g).toMonoidHom = S := by
    have hh := congrArg (fun U : Sylow 2 (Equiv.Perm (Fin 5)) =>
      (U : Subgroup (Equiv.Perm (Fin 5)))) hg
    exact hh
  refine ⟨(D 5).map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · rw [fixedCodim_map_conj]
    exact Odd.fixedCodim_core_disjointTranspositions (Or.inl rfl) le_rfl
  · intro A hA hAP
    have hAS : A ≤ S := hAP.trans hPS
    have hinv : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ R := by
      apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).mp
      rw [hcancel, hgmap]
      exact hAS
    have hB := Odd.caseAFamily_le_D_of_le_sylow (Or.inl rfl) R hDR
      ((Odd.isBestOffender_core_iff_caseAFamily (Or.inl rfl) _).mp (hA.map_conj _ g⁻¹)) hinv
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hB
    rw [hcancel] at hh
    exact hh

end CFSG.Quasithin.ChapterB.Offenders
