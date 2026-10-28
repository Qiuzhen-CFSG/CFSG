module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Contracts
public import CFSG.Quasithin.ChapterB.Section03.Offenders
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Offenders on the natural A₆, S₆ and S₇ modules

The B.3.2 classification includes each transposition subgroup. Its conjugates
therefore generate the symmetric group. The even degree-six offenders are the
conjugates of the rank-two even part of the three-pair group. An odd element
centralizing that representative corrects each conjugator to an element of A₆.
There are no strong offenders on A₆; Thompson replacement gives ratio one,
and simplicity gives generation of A₆ by these offenders.

Source: Aschbacher–Smith, combined manuscript, B.3.2 and B.3.4 (pp.83–85),
applied in K.1–K.1.2 (p.452). All classifications used here are proved APIs.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.ChapterK.Alternating.NaturalOffenders

private theorem symmetric_generated {n : ℕ} (hn : 2 ≤ n)
    (hbest : IsBestOffender (naturalRepresentation (Fin n)) (disjointTranspositions n 1)) :
    offenderSubgroup (naturalRepresentation (Fin n)) = ⊤ := by
  let N := offenderSubgroup (naturalRepresentation (Fin n))
  let : N.Normal := offenderSubgroup_normal _
  apply top_unique
  rw [← Equiv.Perm.closure_isSwap]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, b, hab, rfl⟩
  let i : Fin (n / 2) := ⟨0, by omega⟩
  have ht : pairSwap n i ∈ N :=
    hbest.le_offenderSubgroup _ (pairSwap_mem i (by dsimp [i]; omega))
  have hc : IsConj (pairSwap n i) (Equiv.swap a b) :=
    Equiv.Perm.isConj_swap
      (by intro he; have hv := congrArg Fin.val he; dsimp [i] at hv; omega) hab
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  exact hc ▸ Subgroup.Normal.conj_mem (inferInstance : N.Normal) _ ht c

theorem sixSymmetric_generated : offenderSubgroup (naturalRepresentation (Fin 6)) = ⊤ :=
  symmetric_generated (by decide) ((Six.isBestOffender_natural_iff _).mpr
    (Or.inl (caseAFamily_disjointTranspositions (by decide) (by decide))))

theorem sevenSymmetric_generated : offenderSubgroup (naturalRepresentation (Fin 7)) = ⊤ :=
  symmetric_generated (by decide) ((Odd.isBestOffender_natural_iff_caseAFamily (Or.inr rfl) _).mpr
    (caseAFamily_disjointTranspositions (by decide) (by decide)))

private abbrev sixActor : Subgroup (alternatingGroup (Fin 6)) :=
  (evenPart 6).subgroupOf (alternatingGroup (Fin 6))

private theorem sixActor_best : IsBestOffender (alternatingNatural 6) sixActor :=
  ((Six.best_natural_even_iff _).mpr (IsConjugateTo.refl _)).1.subgroupOf _ inf_le_right

theorem six_best_conjugate {A : Subgroup (alternatingGroup (Fin 6))}
    (hA : IsBestOffender (alternatingNatural 6) A) :
    IsConjugateTo (A.map (alternatingGroup (Fin 6)).subtype) (evenPart 6) :=
  (Six.best_natural_even_iff _).mp ⟨hA.map_subtype _, map_subtype_le _⟩

theorem six_best_dimensions {A : Subgroup (alternatingGroup (Fin 6))}
    (hA : IsBestOffender (alternatingNatural 6) A) :
    rank A = 2 ∧ fixedCodim (alternatingNatural 6) A = 2 := by
  have hc := six_best_conjugate hA
  refine ⟨?_, ?_⟩
  · rw [← rank_map_injective _ (alternatingGroup (Fin 6)).subtype_injective,
      hc.rank_eq, Six.rank_evenPart]
  · change fixedCodim ((naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype) A = 2
    unfold fixedCodim
    rw [fixedSpace_comp_map]
    change fixedCodim (naturalRepresentation (Fin 6))
      (A.map (alternatingGroup (Fin 6)).subtype) = 2
    rw [hc.fixedCodim_eq]
    exact Six.fixedCodim_evenPart.2.2.2

theorem sixNatural_ratio : quadraticRatio (alternatingNatural 6) = 1 := by
  apply quadraticRatio_eq_one_of_no_strong _ ⟨sixActor, sixActor_best.isOffender _⟩
  intro A hA
  obtain ⟨B, _, hB, hs⟩ := hA.exists_bestOffender _
  have hd := six_best_dimensions hB
  exact (Nat.ne_of_lt hs.2) (hd.2.trans hd.1.symm)

theorem sixNatural_generated : offenderSubgroup (alternatingNatural 6) = ⊤ := by
  let : (offenderSubgroup (alternatingNatural 6)).Normal := offenderSubgroup_normal _
  exact (alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp)).resolve_left
    (offenderSubgroup_ne_bot_of_ff _ ⟨sixActor, sixActor_best.isOffender _⟩)

private theorem evenPart_odd_conjugation :
    (evenPart 6).map (MulAut.conj (pairSwap 6 0)).toMonoidHom = evenPart 6 := by
  have hc (a : Equiv.Perm (Fin 6)) (ha : a ∈ evenPart 6) :
      (MulAut.conj (pairSwap 6 0)) a = a := by
    let : IsElementaryAbelian 2 (D 6) := Six.elementary_disjointTranspositions 3
    have hcomm := mul_comm' (⟨pairSwap 6 0, pairSwap_mem 0 (by decide)⟩ : D 6)
      ⟨a, ha.1⟩
    have h : pairSwap 6 0 * a = a * pairSwap 6 0 := congrArg Subtype.val hcomm
    change pairSwap 6 0 * a * (pairSwap 6 0)⁻¹ = a
    rw [h, mul_inv_cancel_right]
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    change (MulAut.conj (pairSwap 6 0)) a ∈ evenPart 6
    rwa [hc a ha]
  · intro a ha
    exact ⟨a, ha, hc a ha⟩

theorem even_conjugator {A : Subgroup (Equiv.Perm (Fin 6))}
    (hA : IsConjugateTo A (evenPart 6)) :
    ∃ g : alternatingGroup (Fin 6),
      A = (evenPart 6).map (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom := by
  classical
  obtain ⟨g, rfl⟩ := hA
  by_cases hg : g ∈ alternatingGroup (Fin 6)
  · exact ⟨⟨g, hg⟩, rfl⟩
  have hs : Equiv.Perm.sign g = -1 := (Int.units_eq_one_or _).resolve_left hg
  have hgt : g * pairSwap 6 0 ∈ alternatingGroup (Fin 6) := by
    change Equiv.Perm.sign (g * pairSwap 6 0) = 1
    rw [map_mul, hs]
    decide +revert
  refine ⟨⟨g * pairSwap 6 0, hgt⟩, ?_⟩
  have hcomp : (MulAut.conj (g * pairSwap 6 0)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj (pairSwap 6 0)).toMonoidHom := by
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← Subgroup.map_map, evenPart_odd_conjugation]

end CFSG.Quasithin.ChapterK.Alternating.NaturalOffenders
