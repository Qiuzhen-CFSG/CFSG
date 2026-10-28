module
public import CFSG.Quasithin.ChapterG.Section10.FittingSource
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Solvable
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.SourceCubic
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer

/-!
# The solvable strict branch of the rank-one recognition argument

For an original G.10 action of dimension greater than four, solvability
forces irreducibility and the degree-six Fitting branch. The existing source
argument then constructs a normal subgroup of order three. Faithful
irreducibility makes its nonidentity elements fixed-free. A rank-two
involution in degree six cannot invert this cubic subgroup, so it centralizes
it; the cubic rotates the three nonzero vectors of its moved plane.

Thus the nontransitivity in 6.2.16(6) forces a solvable dotted actor to have
dimension at most four. This proves the required degree-six source branch
without a supplied extraspecial model or the full G.11.2 catalogue. The
source actor, representation and SQTK cover are retained literally.
The four-dimensional and nonsolvable branches remain separate obligations.

Source: Aschbacher--Smith, G.10.4--5, G.9.4(5), and the elimination of
G.11.2(3) in the proof of 6.2.19, printed pp.354--355,358--359,691.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The solvable original G.10 action above dimension four has a transitive
stabilizer on each rank-two moved plane supplied by its elementary actor. -/
theorem stabilizerTransitive_of_solvable_degree_gt_four {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G))
    (hs : Group.IsSolvable G) (hd : 4 < finrank (ZMod 2) V)
    (a : G) (haX : a ∈ X) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2) :
    RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a) := by
  have hi : Representation.IsIrreducible ρ := by
    by_contra hred
    have hfour := (h.reducible_degree_and_solvable hred).1
    omega
  let : Representation.IsIrreducible ρ := hi
  have hX : X ≠ ⊥ := by
    intro he
    have ha1 : a = 1 := mem_bot.mp (he ▸ haX)
    rw [ha1, RankTwo.movedSpace, map_one, sub_self, LinearMap.range_zero,
      finrank_bot] at hr
    omega
  have h6 : finrank (ZMod 2) (Additive X) = 2 ∧ finrank (ZMod 2) V = 6 := by
    rcases h.solvable_irreducible_cases cover hs hi hX with h1 | h2 | h3 | h4 | h6
    · have := h1.2.1; omega
    · have := h2.2.1; omega
    · have := h3.2.1; omega
    · have := h4.2.1; omega
    · exact h6
  have d := h.fittingHypothesis_of_solvable cover hs hi
  have d2 : Section09.FittingHypothesis K ρ X 2 := h6.1 ▸ d
  have hc : IsPGroup 3 (⁅fittingSubgroup G, X⁆ : Subgroup G) := by
    by_contra hn
    have hb := (Section09.FittingRecognition.caseTwo_from_source d2 (by decide) hn).1
    omega
  obtain ⟨C, hCn, hCc⟩ :=
    Section09.FittingRecognition.Six.normal_cubic_of_source_degree_six d2 hc h6.2
  let : C.Normal := hCn
  obtain ⟨c, hc3⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hCc])
  have hc3G : orderOf (c : G) = 3 := (orderOf_coe c).trans hc3
  have hC : zpowers (c : G) = C := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr c.property)
    rw [Nat.card_zpowers, hc3G, hCc]
  have hcn : (zpowers (c : G)).Normal := by rw [hC]; exact hCn
  exact RankTwo.stabilizerTransitive_of_rank_two_normal_three ρ a c h6.2
    (by simpa only [pow_two] using ha2) hc3G hcn
    (RankTwo.fixed_free_of_faithful_irreducible_normal_three ρ h.faithful c hc3G hcn) hr

/-- The nontransitivity supplied by 6.2.16(6) removes every solvable strict
branch above dimension four, without an extraspecial model classification. -/
theorem solvable_degree_le_four_of_rank_two_nontransitive {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G))
    (hs : Group.IsSolvable G) (a : G) (haX : a ∈ X) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) :
    finrank (ZMod 2) V ≤ 4 := by
  by_contra hd
  exact hnt (h.stabilizerTransitive_of_solvable_degree_gt_four cover hs
    (Nat.lt_of_not_ge hd) a haX ha2 hr)
end CFSG.Quasithin.ChapterG.Section10.Hypothesis
