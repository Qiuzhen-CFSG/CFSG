module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Complete

/-!
# The four minimal offenders on the natural degree-eight module

The complete binary permutation classification leaves disjoint transposition
subgroups, the exceptional group, hyperplanes, and regular elementary eights.
Every non-even hyperplane and the exceptional group contains a transposition.
For a nonstrong best offender that transposition has equal weight, so minimality
eliminates these extra families. The remaining ranks and fixed codimensions are
proved from the concrete action computations, then transported by conjugacy.

This classifies minimal **best** offenders. Applying it to the source family of
minimal maximum-elementary action images still requires the B.2.5 lifting clauses;
that transfer is explicit in `Selection.lean`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.2,
printed pp.83–84, and the proof of 15.3.25, printed pp.1133–1134.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders

/-- Source cases (i)–(iv); each realization specifies an actual permutation subgroup. -/
inductive EightCase
  | regular | transposition | disjoint | even
  deriving DecidableEq

namespace EightCase

/-- The concrete subgroup geometry of a source offender case. -/
def Realizes (c : EightCase) (A : Subgroup (Equiv.Perm (Fin 8))) : Prop :=
  match c with
  | .regular => IsRegularEight A
  | .transposition => IsConjugateTo A (disjointTranspositions 8 1)
  | .disjoint => IsConjugateTo A (D 8)
  | .even => IsConjugateTo A (evenPart 8)

/-- Predicted actor rank, certified by `dimensions`. -/
def actorRank : EightCase → ℕ
  | .regular => 3
  | .transposition => 1
  | .disjoint => 4
  | .even => 3

/-- Predicted natural fixed codimension, certified by `dimensions`. -/
def codim : EightCase → ℕ
  | .transposition => 1
  | _ => 3

/-- The two dimensions are derived from the concrete action computations. -/
theorem dimensions {c : EightCase} {A : Subgroup (Equiv.Perm (Fin 8))}
    (h : c.Realizes A) :
    rank A = c.actorRank ∧ fixedCodim (naturalRepresentation (Fin 8)) A = c.codim := by
  cases c with
  | regular => exact ⟨rank_eq_three_of_isRegularEight h, fixedCodim_natural_regularEight h⟩
  | transposition =>
    exact ⟨h.rank_eq.trans (Eight.rank_disjointTranspositions 1),
      (h.fixedCodim_eq _).trans (Eight.fixedCodim_disjointTranspositions (by decide) (by decide)).2.2.2⟩
  | disjoint =>
    exact ⟨h.rank_eq.trans Eight.rank_D,
      (h.fixedCodim_eq _).trans (Eight.fixedCodim_disjointTranspositions (by decide) (by decide)).2.2.2⟩
  | even => exact ⟨h.rank_eq.trans Eight.rank_evenPart,
      (h.fixedCodim_eq _).trans Eight.fixedCodim_evenPart.2.2.2⟩

/-- The surviving disjoint-transposition case has an odd permutation.
This is the action-image exclusion needed for S0, whose image lies in A8. -/
theorem disjoint_not_le_alternating {A : Subgroup (Equiv.Perm (Fin 8))}
    (h : EightCase.disjoint.Realizes A) : ¬ A ≤ alternatingGroup (Fin 8) := by
  obtain ⟨g, rfl⟩ := h
  intro hle
  have hp := hle (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (pairSwap_mem (n := 8) (m := 4) 0 (by decide)))
  change Equiv.Perm.sign (g * pairSwap 8 0 * g⁻¹) = 1 at hp
  have hs : Equiv.Perm.sign (pairSwap 8 0) = -1 := by decide +kernel
  simp only [map_mul, map_inv, hs] at hp
  have hh := congrArg (fun x => (Equiv.Perm.sign g)⁻¹ * x * Equiv.Perm.sign g) hp
  simp at hh

end EightCase

private theorem single_eq_zpowers :
    disjointTranspositions 8 1 = zpowers (pairSwap 8 0) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨i, hi, rfl⟩
    have hi0 : i = 0 := Fin.ext (by change i.val = 0; omega)
    subst i
    exact mem_zpowers _
  · exact zpowers_le.mpr (pairSwap_mem 0 (by decide))

private theorem pairSwap_conjugate (i : Fin 4) :
    IsConjugateTo (zpowers (pairSwap 8 i)) (disjointTranspositions 8 1) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap
    (show (0 : Fin 8) ≠ 1 by decide)
    (show (⟨2 * i.val, by omega⟩ : Fin 8) ≠ ⟨2 * i.val + 1, by omega⟩ by
      intro h; have hh := congrArg Fin.val h; change 2 * i.val = 2 * i.val + 1 at hh; omega))
  refine ⟨g, ?_⟩
  rw [single_eq_zpowers, MonoidHom.map_zpowers]
  exact congrArg zpowers hg.symm

private theorem pairSwap_in_hyperplane {H : Subgroup (Equiv.Perm (Fin 8))}
    (hH : H ⋖ D 8) (hne : H ≠ evenPart 8) : ∃ i : Fin 4, pairSwap 8 i ∈ H := by
  obtain ⟨m, _, rfl⟩ := Eight.hyperplane_eq_kernel hH
  have hm : m ≠ 15 := by
    intro h; apply hne; rw [h, Eight.evenPart_eq_hyperplaneKernel]
  have ht : ∀ m : Fin 16, m ≠ 15 → ∃ i : Fin 4, ∃ j : Fin 16,
      Eight.hyperplaneForm m (Eight.hyperplaneCoeffs j) = 0 ∧
        Eight.dWords j = pairSwap 8 i := by decide +kernel
  obtain ⟨i, j, hj, he⟩ := ht m hm
  exact ⟨i, (Eight.mem_hyperplaneKernel _ _).mpr ⟨j, hj, he⟩⟩

private theorem conjugate_trans (A B C : Subgroup (Equiv.Perm (Fin 8)))
    (hAB : IsConjugateTo A B) (hBC : IsConjugateTo B C) : IsConjugateTo A C := by
  obtain ⟨g, rfl⟩ := hAB
  obtain ⟨h, rfl⟩ := hBC
  refine ⟨g * h, ?_⟩
  rw [map_map]
  rfl

private theorem minimal_nonstrong_eq_single
    {A H : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsMinimalBestOffender (naturalRepresentation (Fin 8)) A)
    (hns : ¬ IsStrongOffender (naturalRepresentation (Fin 8)) A)
    (hconj : IsConjugateTo A H) (i : Fin 4) (hi : pairSwap 8 i ∈ H) :
    IsConjugateTo A (disjointTranspositions 8 1) := by
  obtain ⟨g, rfl⟩ := hconj
  let B := (zpowers (pairSwap 8 i)).map (MulAut.conj g).toMonoidHom
  have hB : IsConjugateTo B (disjointTranspositions 8 1) :=
    conjugate_trans B _ _ ⟨g, rfl⟩ (pairSwap_conjugate i)
  have hbest : IsBestOffender (naturalRepresentation (Fin 8)) B :=
    hB.isBestOffender _ (Eight.isBestOffender_natural_of_caseAFamily
      (caseAFamily_disjointTranspositions (by decide) (by decide)))
  have hdimA := fixedCodim_add_finrank (naturalRepresentation (Fin 8))
    (H.map (MulAut.conj g).toMonoidHom)
  have hdimB := fixedCodim_add_finrank (naturalRepresentation (Fin 8)) B
  have hbound := (hA.1.isOffender _).2
  have hnot : ¬ fixedCodim (naturalRepresentation (Fin 8))
      (H.map (MulAut.conj g).toMonoidHom) < rank (H.map (MulAut.conj g).toMonoidHom) :=
    fun h => hns ⟨hA.1.1, h⟩
  have hr := (EightCase.dimensions (c := .transposition) hB)
  have he := hA.2 B hbest ⟨map_mono (zpowers_le.mpr hi), by
    unfold weight
    dsimp [EightCase.actorRank, EightCase.codim] at hr
    omega⟩
  exact he ▸ hB

/-- The four source cases follow from equal-weight minimality in the actual
natural representation. In particular the exceptional and other hyperplane
families disappear because they contain a transposition of equal weight. -/
theorem minimalBest_realizes {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsMinimalBestOffender (naturalRepresentation (Fin 8)) A) :
    ∃ c : EightCase, c.Realizes A := by
  by_cases hs : IsStrongOffender (naturalRepresentation (Fin 8)) A
  · exact ⟨.disjoint, (Eight.isStrongOffender_natural_iff A).mp hs⟩
  rcases (Eight.isBestOffender_natural_iff A).mp hA.1 with hf | hr
  · rcases hf with ⟨m, hm, _, hc⟩ | hc | hc | ⟨H, hH, hn, hc⟩
    · exact ⟨.transposition, minimal_nonstrong_eq_single hA hs hc 0
        (pairSwap_mem 0 (by change 0 < m; omega))⟩
    · exact ⟨.transposition, minimal_nonstrong_eq_single hA hs hc 2
        (subset_closure (Or.inr ⟨2, by decide, rfl⟩))⟩
    · exact ⟨.even, hc⟩
    · obtain ⟨i, hi⟩ := pairSwap_in_hyperplane hH hn
      exact ⟨.transposition, minimal_nonstrong_eq_single hA hs hc i hi⟩
  · exact ⟨.regular, hr⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
end
