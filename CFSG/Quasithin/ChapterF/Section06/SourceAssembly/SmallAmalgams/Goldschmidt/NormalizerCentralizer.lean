module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerSingularity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerThreeClosed

/-!
# The source track normalizer has a cubic centralizer

The original first-singularity and nontrivial track-fixer hypotheses supply
the distance-two quotient action and a regularity length at least four.
The three-closed exclusion therefore applies to the literal local normalizer
quotient, and the semilocal centralizer theorem supplies a cubic divisor.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.3),
printed p.395. No auxiliary regularity, quotient-identification or
three-closed premise remains in this application.
-/

public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The actual track-fixer centralizer has order divisible by three at the
first vertex, under the source first-singularity hypotheses. -/
theorem normalizer_centralizer_three_dvd (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false)
    (ht1 : t.vertex 1 = RankTwo.base F true) (hQ : trackFixer t ≠ ⊥)
    {s : ℕ} (hs : 5 ≤ s) (hsodd : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) (hv : v.type = false) :
    3 ∣ Nat.card ((centralizer (trackFixer t : Set G)).subgroupOf (F false)) := by
  let _ := normalizerQuotientAction h t ht0
  have hcandidate := h.trackFixer_normalizerCandidate t ht0 ht1 hQ hs hsodd hshort p hp hn hv
  obtain ⟨r, hr, _, _, _, hcards⟩ :=
    normalizerQuotient_source h t ht0 ht1 hQ hs hsodd hshort p hp hn hv
  exact normalizer_centralizer_three_dvd_of_regularity h t ht0 hcandidate r hr hcards

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
