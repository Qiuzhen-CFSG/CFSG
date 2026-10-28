module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import Theory.GroupTheory.ReducedNormal.Defs
public import Stellmacher.ElementaryAbelianMaxGlobal
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Solvable
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.Rank

/-!
# The solvable Thompson-image branch of E.2.3

B.2.7 supplies the actual stable images of the largest elementary subgroups.
The solvable B.6.9 theorem makes their span the entire offender subgroup
of the faithful centralizer quotient. Consequently the same internal
natural SL₂(2) factors decompose the original J(H) image, and the original
Sylow acts transitively on them. The original rank-three bound, via A.1.31,
limits this family to one or two; no rank monotonicity through an arbitrary
kernel is assumed.

The witnesses retain the quotient map and the natural intertwiners on
actual commutator supports. This proves the solvable factor and transitivity
part of E.2.3(1). The separate Baumann Sylow and omega-center assertions of
(2) are not assumed or asserted here.

Source: Aschbacher–Smith, E.2.3, printed pp.216–217 (1 March 2004).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.SolvableSource
variable {G : Type*} [Group G] [Finite G]

variable {H : Type*} [Group H] [Finite H]

/-- The actual solvable reduced quotient has exactly the Thompson-image factors. -/
theorem solvable_factors
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hcore : pCore 2 H = ⊥) (hsolv : Group.IsSolvable H)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2) :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (d.count = 1 ∨ d.count = 2) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = offenderSubgroup ρ ∧
      (∀ i j, ∃ t : T,
        (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [← hker, he]
    exact le_top
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  obtain ⟨d, hst, hjg, _, _⟩ :=
    ChapterB.thompson_factors_of_solvable_action U q hq hker T hJ hsolv hcore
  have hfaith := NormalElementaryQuotient.representation_injective U q hq hker
  have hall := d.stable_generated_eq (T.mapSurjective hq) hp hcore hfaith hst
  have hgen := (ChapterB.stable_offender_generation (T.mapSurjective hq) hp ρ hst hcore).2
  rw [hall] at hgen
  refine ⟨d, d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank q hq hrank,
    hjg.trans hall, ?_⟩
  intro i j
  obtain ⟨t, ht⟩ := d.toSolvableFFFactors.factor_transitive (T.mapSurjective hq) hp hcore hgen i j
  obtain ⟨x, hx, hxt⟩ := t.property
  exact ⟨⟨x, hx⟩, by simpa only [hxt] using ht⟩

/-- Original reduced U, with the literal centralizer quotient and its action. -/
theorem source_solvable_factors
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2)
    (hsolv : letI := hU.normal; Group.IsSolvable (G ⧸ centralizer (U : Set G))) :
    let := hU.normal
    let := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (d.count = 1 ∨ d.count = 2) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = offenderSubgroup ρ ∧
      (∀ i j, ∃ t : T,
        (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) := by
  let := hU.normal
  let := hU.elementary
  exact solvable_factors T hP U _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hsolv hJ hrank

end CFSG.Quasithin.ChapterB.RankOneBaumann.SolvableSource
