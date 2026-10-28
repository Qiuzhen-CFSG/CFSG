module
public import Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori.Covers
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.UnitaryFiveFourCover
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankOneAliases
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.Arithmetic
/-!
# The full even-characteristic unitary Case II

Tail permutations exchange three independent torus directions in the literal
root normalizer or line parabolic. Arbitrary lifts through the original
central quotient therefore commute and force an odd-prime rank-three
two-local subgroup in G. This bounds the degree by five and restricts the
five-dimensional fixed field to order four. The completed low-dimensional
cover calculations and the actual SU5(4) recognition then exclude every
remaining unitary catalogue parameter.

All maps retain the original central quotient and the given Hermitian form,
transported through a proved identity basis. No quotient quasithinness or
prime-primary-center hypothesis is used.
Source: Aschbacher--Smith A.2.18, printed p.40.
-/
public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram Theory.SpecificGroups.UnitaryRootNormalizer
open Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G] [IsQuasisimple G]

/-- Swapped torus directions bound the degree in the original central quotient. -/
theorem unitary_center_quotient_degree_le_five (hG : IsQuasithin G)
    {d a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) d (2 ^ a)) : d ≤ 5 := by
  by_contra hd
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 6 ≤ d by omega)
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := iso
  let : CharP F 2 := charP_binary ha hcard
  obtain ⟨C,hC⟩ := exists_binary_identity_basis J ha hcard hconj
  let f := centralQuotientCover (e.trans (projectiveEquiv J C hC))
  have hq : 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide : 1 ≤ 2) ha
  have heven : Even (2 ^ a) := even_two.pow_of_ne_zero (by omega)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show 2 ^ a + 1 ≠ 1 by omega)
  have ho : Odd p := by
    apply hp.odd_of_ne_two
    intro he
    subst p
    obtain ⟨b,hb⟩ := heven
    obtain ⟨c,hc⟩ := hd
    omega
  exact six_cover_not_quasithin k (identityGram J) rfl f.toMonoidHom f.surjective
    f.ker_le_center hcard hq hconj hp ho hd hG

/-- Outside fixed-field order four, the actual line parabolic excludes every PSU5 central cover. -/
theorem unitary_five_center_quotient_field_eq_four (hG : IsQuasithin G)
    {a : ℕ} (ha : 0 < a) (hqPrimePow : IsPrimePow (2 ^ a))
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) 5 (2 ^ a)) : 2 ^ a = 4 := by
  by_contra hne
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := iso
  let : CharP F 2 := charP_binary ha hcard
  obtain ⟨C,hC⟩ := exists_binary_identity_basis J ha hcard hconj
  let f := centralQuotientCover (e.trans (projectiveEquiv J C hC))
  obtain ⟨p,hp,ho,hd,hp5⟩ := Theory.SpecificGroups.UnitaryFive.exists_odd_prime_ne_five_dvd_succ
    hqPrimePow (even_two.pow_of_ne_zero (by omega)) hne
  exact five_cover_not_quasithin (identityGram J) rfl f.toMonoidHom f.surjective
    f.ker_le_center hcard (Nat.pow_le_pow_right (by decide : 1 ≤ 2) ha) hconj hp ho hd hp5 hG

/-- The full unitary Case II follows from original proper-section induction and actual model maps. -/
theorem caseII_unitary_of_source {K : GroupClass.{u}}
    {S : Type u} [Group S] [Finite S] {p d a : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (ha : 0 < a) (hp : KnownSimple.UnitaryParameters d (2 ^ a))
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) d (2 ^ a)) : False := by
  have hd := unitary_center_quotient_degree_le_five h.1 ha iso
  have hmin := hp.2.1
  interval_cases d
  · have ha2 : 2 ≤ a := by
      by_contra hn
      have : a = 1 := by omega
      have hh := hp.2.2.1 rfl
      simp [this] at hh
    exact caseII_unitary_two_of_source h ih ha2 iso
  · have ha2 : 2 ≤ a := by
      by_contra hn
      have : a = 1 := by omega
      exact hp.2.2.2 rfl (by simp [this])
    exact caseII_unitary_three_of_source h ih ha2 iso
  · exact caseII_unitary_four_of_source h ih ha iso
  · have hq := unitary_five_center_quotient_field_eq_four h.1 ha hp.1 iso
    exact caseII_unitary_five_four_of_source h ih (hq ▸ iso)
end CFSG.Quasithin.ChapterA.Section02.EvenLie
