module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuOne.Reduction
public import Theory.Mathieu.M11.RankOneSolvablePair
public import Theory.Mathieu.M11.Properties.OuterRestriction

/-!
# Rank-one E-generation for an M₁₁ generalized Fitting subgroup

The native involution centralizer and Sylow three-normalizer can be conjugated
to contain any given Sylow two-subgroup. The former is maximal, and the order
of the latter prevents containment, so they generate M₁₁. Their proved
solvability gives E.1.13 for both members. E-member inheritance proves the
ambient bound. Since every M₁₁ automorphism is inner, self-centralization of
F*(G) also handles every source-allowed ambient extension.

Source: Aschbacher–Smith, E.1.12–14, printed p.214, citing Asc82a Lemma 4.9.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterE.MathieuOne
variable {G : Type*} [Group G] [Finite G]

/-- The native solvable generating pair discharges both local E-generation bounds. -/
theorem m11_isEGenerated : IsEGenerated 1 M11 := by
  classical
  let T : Sylow 2 M11 := Classical.choice inferInstance
  obtain ⟨H, J, hH, hJ, hj, hsH, hsJ⟩ := M11RankOne.exists_solvable_pair T
  let := hsH
  let := hsJ
  apply isEGenerated_of_family T {H, J}
  · simpa only [sSup_pair] using hj
  · intro A hA
    rcases hA with rfl | hA
    · exact ⟨hH, isEGenerated_one_of_solvable⟩
    · have he : A = J := hA
      subst A
      exact ⟨hJ, isEGenerated_one_of_solvable⟩

/-- E.1.14(4), upper bound for the M₁₁ generalized Fitting subgroup case. -/
theorem isEGenerated_of_m11_socle (e : generalizedFitting G ≃* M11) :
    IsEGenerated 1 G := by
  obtain ⟨a⟩ := ambient_equiv_of_inner_automorphisms e m11_automorphism_inner
  exact m11_isEGenerated.map_equiv a.symm
end CFSG.Quasithin.ChapterE.MathieuOne
