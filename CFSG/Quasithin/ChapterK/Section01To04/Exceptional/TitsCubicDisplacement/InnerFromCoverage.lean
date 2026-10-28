module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Reduction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.FullDerivedAction
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The Tits outer-involution input on the actual carrier

The full binary Ree group acts bijectively on its derived subgroup, identified
with Parrott's group. Full binary involution coverage therefore makes every
involutory automorphism inner. Centerlessness ensures its inner representative
also has square one. The coverage premise belongs to the existing
`qt-16-tits-binary-involution-coverage` producer; no group-family tag or change
of carrier is used here.

Source: GM04 Lemma 8.8, internal p.57; Aschbacher--Smith 16.1.4, p.1171.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
open Subgroup Tits.InvolutionRootGeometry

/-- Full binary involution coverage supplies the exact inner-actor premise. -/
theorem inner_from_binary_coverage (hcover : BinaryInvolutionCoverage)
    (a : MulAut Tits.ParrottGroup) (ha : a ^ 2 = 1) :
    ∃ x : Tits.ParrottGroup, x ^ 2 = 1 ∧ a = MulAut.conj x := by
  by_cases he : a = 1
  · exact ⟨1, by simp, by simp [he]⟩
  have hbij := ReeF4.Parabolics.OuterLocal.binaryDerivedAction_bijective derivedEquiv.symm
  obtain ⟨x, hx, _⟩ := involution_inner_root_of_binary_coverage hbij hcover a ha he
  refine ⟨x, ?_, hx⟩
  apply MulAut.conj_injective_of_center_eq_bot
    (Tits.RelativeSylowMarking.center_eq_bot Tits.parrottFiniteImageEquiv)
  rw [map_pow, ← hx, ha, map_one]

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
