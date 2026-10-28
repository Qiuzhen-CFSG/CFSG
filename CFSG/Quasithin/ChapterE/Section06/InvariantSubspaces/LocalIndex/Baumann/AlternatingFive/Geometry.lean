module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.SourceSylow
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Two conjugate four-groups for Baumann's Argument

The four-group D = ⟨(01),(23)⟩ consists of two commuting transpositions.
Conjugation by the even five-cycle (01234) gives ⟨(12),(34)⟩. Together
these groups contain every adjacent transposition, so they generate S₅.
Each has fixed codimension two on the natural module; A₅ has fixed
codimension four by transitivity and the odd-degree permutation decomposition.
Conjugating this construction gives the same pair for every conjugate of D.

These are calculations in the concrete model. Identifying the image of the
local Thompson subgroup with a conjugate of D is a separate obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(3),
printed p.155; B.2.18(d) and B.3.2(1),(4), pp.80 and 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive

open Subgroup CFSG.Quasithin.ChapterB.Offenders
open BinaryPermutation Representation.BinaryOffender

private def rot : Equiv.Perm (Fin 5) := Fin.cycleRange 4
private theorem rot_even : rot ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, rot, Fin.sign_cycleRange]
  decide

/-- A₅ has no fixed vectors on the four-dimensional natural module. -/
theorem fixedCodim_alternating :
    fixedCodim (naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)) = 4 := by
  let h := alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
  let : Subsingleton (MulAction.orbitRel.Quotient (alternatingGroup (Fin 5)) (Fin 5)) :=
    (MulAction.pretransitive_iff_subsingleton_quotient _ _).mp h
  rw [fixedCodim_natural_eq_full_odd (Fin 5) (by decide),
    fixedCodim_full_eq_card_sub_card_orbits, Nat.card_unique]
  decide

private theorem D_sup_conjugate :
    D 5 ⊔ (D 5).map (MulAut.conj rot).toMonoidHom = ⊤ := by
  apply top_unique
  rw [← Subgroup.closure_eq_top_of_mclosure_eq_top
    (Equiv.Perm.mclosure_swap_castSucc_succ 4)]
  apply (Subgroup.closure_le _).mpr
  rintro s ⟨i, rfl⟩
  fin_cases i
  · exact mem_sup_left (pairSwap_mem (n := 5) 0 (by decide))
  · have he : (MulAut.conj rot) (pairSwap 5 0) = Equiv.swap (1 : Fin 5) 2 := by
      decide +kernel
    exact mem_sup_right (mem_map.mpr ⟨pairSwap 5 0, pairSwap_mem (n := 5) 0 (by decide), he⟩)
  · exact mem_sup_left (pairSwap_mem (n := 5) 1 (by decide))
  · have he : (MulAut.conj rot) (pairSwap 5 1) = Equiv.swap (3 : Fin 5) 4 := by
      decide +kernel
    exact mem_sup_right (mem_map.mpr ⟨pairSwap 5 1, pairSwap_mem (n := 5) 1 (by decide), he⟩)

/-- Every conjugate of D has an A₅-conjugate which, together with it,
generates S₅ and satisfies the dimension equality of B.2.18(d). -/
theorem exists_model_conjugate_pair {B : Subgroup (Equiv.Perm (Fin 5))} (hB : IsConjugateTo B (D 5)) :
    ∃ g ∈ alternatingGroup (Fin 5),
      B ⊔ B.map (MulAut.conj g).toMonoidHom = ⊤ ∧
      fixedCodim (naturalRepresentation (Fin 5)) B +
        fixedCodim (naturalRepresentation (Fin 5)) (B.map (MulAut.conj g).toMonoidHom) =
          fixedCodim (naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)) := by
  obtain ⟨d, rfl⟩ := hB
  let g := d * rot * d⁻¹
  have hg : g ∈ alternatingGroup (Fin 5) :=
    (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem rot rot_even d
  have he : ((D 5).map (MulAut.conj d).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      ((D 5).map (MulAut.conj rot).toMonoidHom).map (MulAut.conj d).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [g, MulAut.conj_apply, mul_assoc]
  refine ⟨g, hg, ?_, ?_⟩
  · rw [he, ← Subgroup.map_sup, D_sup_conjugate]
    exact map_top_of_surjective _ (MulAut.conj d).surjective
  · simp only [fixedCodim_map_conj]
    rw [Odd.fixedCodim_natural_disjointTranspositions (Or.inl rfl) (by decide),
      fixedCodim_alternating]

/-- The two source transpositions generate the literal subgroup D. -/
theorem D_eq_closure_swaps : D 5 = Subgroup.closure {Equiv.swap (0 : Fin 5) 1, Equiv.swap (2 : Fin 5) 3} := by
  unfold D disjointTranspositions
  congr 1
  ext s
  constructor
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp [pairSwap]
  · rintro (rfl | hs)
    · exact ⟨0, by decide, rfl⟩
    · rw [Set.mem_singleton_iff] at hs
      subst s
      exact ⟨1, by decide, rfl⟩

/-- The two generators of D commute. -/
theorem swaps_commute : Commute (Equiv.swap (0 : Fin 5) 1) (Equiv.swap (2 : Fin 5) 3) := by
  change Equiv.swap (0 : Fin 5) 1 * Equiv.swap (2 : Fin 5) 3 =
    Equiv.swap (2 : Fin 5) 3 * Equiv.swap (0 : Fin 5) 1
  decide +kernel

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive

end
