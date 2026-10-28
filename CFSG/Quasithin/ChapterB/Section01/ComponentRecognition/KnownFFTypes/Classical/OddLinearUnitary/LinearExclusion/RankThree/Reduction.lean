module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds

/-!
# Source reductions for the odd-prime linear-three exclusion

Three conjugates of a nonidentity involution bound binary degree by six times
the rank of an actual actor of ratio at most two. Degree at least twelve
therefore excludes rank-one actors and forces degree twelve for rank-two actors.
In degree twelve the only remaining actors have rank two and fixed dimension
at least eight, or rank three and fixed dimension at least six. This keeps graph
outer actors in the second branch.

The model generation, degree and fixed-space calculations are explicit inputs.
These reductions do not assert the unconditional PSL₃ exclusion. They are used
by `RankThree.source_exclusion_of_calculations`, whose remaining premises must
be discharged in the final source assembly.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle, Classification
of 2F-modules I, (2.6) and Proposition 4.2, manuscript pp.4, 9--10.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem core_nontrivial : Nontrivial (generalizedFitting G) := by
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  exact (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial

/-- Preserve the actual actor rank in the degree estimate. -/
theorem source_degree_le_six_rank
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹))
    (hq : cubicRatio ρ ≤ 2) :
    Module.finrank (ZMod 2) V ≤ 6 * primeRank 2 G := by
  let : Nontrivial (generalizedFitting G) := core_nontrivial ρ h
  simpa only [show (3 : ℕ) * (2 * primeRank 2 G) = 6 * primeRank 2 G by omega] using
    finrank_le_of_cubicRatio_conjugates ρ (generalizedFitting G)
      h.faithful h.irreducible le_rfl hgen hq

omit [Finite G] in
/-- Three conjugates bound the degree using the selected actor's own rank,
including actors whose rank is smaller than the rank of G. -/
theorem source_degree_le_six_actor_rank
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹))
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 6 * rank A := by
  let : Nontrivial (generalizedFitting G) := core_nontrivial ρ h
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  obtain ⟨g, hg⟩ := hgen t ht1 ht2
  have hdegree := finrank_le_mul_fixedCodim_of_conjugate_generation ρ
    (generalizedFitting G)
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ _ h.faithful h.irreducible) t g hg
  have hfixed : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hmono := Submodule.finrank_mono hfixed
  have hnullA := fixedCodim_add_finrank ρ A
  have hnullt := fixedCodim_add_finrank ρ (zpowers t)
  omega

omit [Finite G] in
/-- Degree at least twelve excludes rank-one actors at threshold two. -/
theorem actor_rank_at_least_two
    (hdim : 12 ≤ Module.finrank (ZMod 2) V)
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹))
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) : 2 ≤ rank A := by
  have := source_degree_le_six_actor_rank ρ h hgen hA hsmall
  omega

omit [Finite G] in
/-- A rank-two actor forces degree exactly twelve once the lower bound is known. -/
theorem degree_twelve_of_rank_two_actor
    (hdim : 12 ≤ Module.finrank (ZMod 2) V)
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹))
    {A : Subgroup G} (hA : IsElementaryTwo A) (hrank : rank A = 2)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V = 12 := by
  have := source_degree_le_six_actor_rank ρ h hgen hA hsmall
  omega

omit h in
/-- Any degree bound exceeding eighteen for p ≥ 5 leaves only the prime three. -/
theorem prime_eq_three_of_degree_bounds {p d : ℕ}
    (hp : p.Prime) (ho : Odd p) (hhi : d ≤ 18)
    (hlo : 5 ≤ p → 18 < d) : p = 3 := by
  have hp2 := hp.two_le
  have hne : p ≠ 2 := by intro he; subst p; norm_num at ho
  by_contra he
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by intro he; subst p; norm_num at hp
    omega
  exact (not_lt_of_ge hhi) (hlo hp5)

/-- In degree twelve a small cubic actor must be a four-group with at least
an eight-dimensional fixed space, or an eight-group with at least a
six-dimensional fixed space. The graph outer case remains in the statement. -/
theorem source_twelve_actor_witness
    (hdim : Module.finrank (ZMod 2) V = 12) (hrank : primeRank 2 G ≤ 3)
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹))
    (hq : cubicRatio ρ ≤ 2) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧
      ((rank A = 2 ∧ 8 ≤ Module.finrank (ZMod 2) (fixedSpace ρ A)) ∨
       (rank A = 3 ∧ 6 ≤ Module.finrank (ZMod 2) (fixedSpace ρ A))) := by
  obtain ⟨A, hA, hc, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  have hlo := actor_rank_at_least_two ρ h hdim.ge hgen hA hsmall
  have hhi := rank_le_of_primeRank_le hA hrank
  have hnull := fixedCodim_add_finrank ρ A
  refine ⟨A, hA, hc, ?_⟩
  by_cases htwo : rank A = 2
  · exact Or.inl ⟨htwo, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- The source common-fixed-space calculations rule out the two remaining
actor ranks. Their construction is a separate model calculation. -/
theorem source_twelve_exclusion_of_fixed_spaces
    (hdim : Module.finrank (ZMod 2) V = 12) (hrank : primeRank 2 G ≤ 3)
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹))
    (htwo : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 6)
    (hthree : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 3 →
      Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 5) : 2 < cubicRatio ρ := by
  apply lt_of_not_ge
  intro hq
  obtain ⟨A, hA, _, hbad | hbad⟩ := source_twelve_actor_witness ρ h hdim hrank hgen hq
  · have := htwo A hA hbad.1
    omega
  · have := hthree A hA hbad.1
    omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
