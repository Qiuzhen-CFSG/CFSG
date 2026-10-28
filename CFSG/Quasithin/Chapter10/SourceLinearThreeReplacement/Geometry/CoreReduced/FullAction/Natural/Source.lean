module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Natural.PointAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Source

/-!
# The original moved-factor fixed line and the full-action contradiction

The point centralizer C_L(a) lies in G_z because L centralizes b. If an element
of the first moved factor outside ⟨a⟩ centralizes V_z, transitivity of C_L(a)
forces that whole factor to centralize V_z. The specified Sylow exchanger
then forces its partner to do so as well. This contradicts noncentralization
by V and proves the precise fixed line needed for the transvection argument.

The application uses the full faithful action and its proved reducedness,
as required by the corrected G.3.1. No irreducibility premise is added.
Source: Aschbacher--Smith 10.2.11(3), printed p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Natural
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

theorem pointCentralizer_le_diagonal (c : Configuration s a b) :
    L ⊓ centralizer ({a} : Set G) ≤ centralizer ({a*b} : Set G) := by
  intro g hg
  have ha : Commute g a := mem_centralizer_singleton_iff.mp hg.2
  have hb : Commute g b := s.crossed c.second_mem g hg.1
  exact mem_centralizer_singleton_iff.mpr (ha.mul_right hb).eq

theorem moved_fixed_eq_line (c : Configuration s a b)
    (hc : centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2))
    (hn : ¬ D.fullModule ≤ centralizer (centralizerModule a b : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a := by
  have hWC : centralizerModule a b ≤ centralizer (centralizerModule a b : Set G) :=
    (hc.trans inf_le_right).trans (centralizer_le (hc.trans inf_le_left))
  have haC : a ∈ centralizer (centralizerModule a b : Set G) :=
    hWC (le_conjugateSpanBy _ _ (mem_sup_left (mem_zpowers a)))
  have hnorm : centralizer ({a*b} : Set G) ≤
      normalizer (centralizer (centralizerModule a b : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _)
  apply le_antisymm ?_ (zpowers_le.mpr
    (show a ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) from
      ⟨c.first_mem, haC⟩))
  intro x hx
  by_contra hxline
  have hx1 : x ≠ 1 := fun he => hxline (he ▸ (zpowers a).one_mem)
  have hxa : x ≠ a := fun he => hxline (he ▸ mem_zpowers a)
  have hAC : ⁅D.fullModule,L⁆ ≤ centralizer (centralizerModule a b : Set G) := by
    intro y hy
    by_cases hy1 : y = 1
    · exact hy1 ▸ (centralizer (centralizerModule a b : Set G)).one_mem
    by_cases hya : y = a
    · exact hya ▸ haC
    obtain ⟨g, hgL, hga, hgy⟩ := exists_pointCentralizer_conjugating c
      ⟨x,hx.1⟩ ⟨y,hy⟩ hx1 hxa hy1 hya
    have hgN := hnorm (pointCentralizer_le_diagonal c ⟨hgL,hga⟩)
    have hh := (mem_normalizer_iff.mp hgN x).mp hx.2
    change g * x * g⁻¹ = y at hgy
    exact hgy ▸ hh
  apply hn
  rw [s.generated]
  refine sup_le hAC ?_
  rintro _ ⟨y,hy,rfl⟩
  exact (mem_normalizer_iff.mp (hnorm (c.sylow_le s.exchange_mem)) y).mp (hAC hy)

/-- The fixed-line input, with no irreducibility or fixed-subgroup premise. -/
theorem movedFactorFixedAt (T : Sylow 2 G) : MovedFactorFixedAt T := by
  intro L D s a b c _hseed hc hn
  exact moved_fixed_eq_line c hc hn

/-- The full-action contradiction now has its original natural input proved. -/
theorem fullActionCentralizationAt (T : Sylow 2 G) : FullActionCentralizationAt T :=
  fullActionCentralization_of_moved_factor (movedFactorFixedAt T)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Natural
