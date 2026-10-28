module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.KnownCases
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.Alternating.Aut

/-!
# Alternating cases of the outer-group inspection

For n ≥ 5 other than six, conjugation by Sₙ covers the full automorphism
group of Aₙ. Hence Out(Aₙ) is a quotient of Sₙ/Aₙ and is a two-group.
The exceptional degree six uses the already proved outer order four.
Transport along the actual model isomorphism gives every alternating case
in Theorem C. The sporadic cases, including the separate abelian-outer
assertion for J₁, remain to be established.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Theorem C on
printed p.33 and the outer-group inspection in the proof of 1.3.4 on p.510.
The conjugation theorem is GLS3, Theorem 5.2.1, proved in `Theory.Alternating.Aut`.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory

private theorem alternating_outer_isPGroup_two_of_ne_six
    (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  have htwo : IsPGroup 2 (Equiv.Perm (Fin n) ⧸ A) := IsPGroup.of_card hcard
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

/-- Every nonabelian alternating group satisfies the structural outer restriction. -/
theorem alternating_outer_cyclicNormalOddQuotient (n : ℕ) (hn : 5 ≤ n) :
    HasCyclicNormalOddQuotient (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases hn6 : n = 6
  · subst n
    exact alternating_six_outer_cyclicNormalOddQuotient
  · exact hasCyclicNormalOddQuotient_of_isPGroup_two
      (alternating_outer_isPGroup_two_of_ne_six n hn hn6)

/-- The actual alternating-model witness in Theorem C discharges its outer case. -/
theorem alternating_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 8)
    (iso : Section02.LocalModels.IsAlternating S n) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  obtain ⟨e⟩ := iso
  exact (alternating_outer_cyclicNormalOddQuotient n hn.1).of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
