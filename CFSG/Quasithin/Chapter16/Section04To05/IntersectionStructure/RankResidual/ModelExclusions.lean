module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.RankResidual.Transport
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.Covers

/-!
# Excluding the central covers in A.3.18(3)

For the ordinary component in Lemma 16.4.5, (E1) already excludes every
model in A.3.18(3): its image modulo O_{3'}(C_G(i)) is the centerless
quotient L/O₂(L). The signed SL₃ models with the source congruence, and
the three exceptional triple covers, all have nontrivial centers. The
previous chapter proves these model facts on the actual carriers; here
we supply their component, odd-core and rank hypotheses from §16.4.
Thus both subcases (3a) and (3b) are excluded by their common model clause.

This does not yet restrict the projective models in A.3.18(2) to even
characteristic, or assert either of the alternatives of Lemma 16.4.5.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
A.3.18(3), pp.51–52, and Lemma 16.4.5, p.1184.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections
open Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

/-- The common, concrete model clause of A.3.18(3). The quotient here is
the source's quotient by the prime-to-three core. -/
def CentralCoverImageAlternative (L I : Subgroup G) : Prop :=
  (∃ (unitary : Bool) (q : ℕ), q % 3 = (if unitary then 2 else 1) ∧
    IsSLSign ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))) unitary 3 q) ∨
  IsAlternatingCover ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))) 6 ∨
  IsAlternatingCover ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))) 7 ∨
  IsM22Cover ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I)))

/-- All four types in A.3.18(3) are impossible, including for an
ordinary component with a nontrivial central two-cover. -/
theorem StandardSetup.no_central_cover_image
    {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L)
    (hr : 1 < primeRank 3 L) {i : G}
    (hi : i ∈ centralizer (L : Set G)) (hi2 : orderOf i = 2) :
    ¬ CentralCoverImageAlternative L (involutionCentralizer i) := by
  have hL := h.involution_component hi hi2
  exact fun hm => SignedReduction.no_central_image_model hL.1 hL.2
    (hG.evenType.oddCore i hi2) (by omega) hm

/-- The image component in A.3.18 is the actual intrinsic two-core
quotient of L. This lets an (E2) model comparison keep its field parameter. -/
noncomputable def StandardSetup.componentCoreImageEquiv
    {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L)
    (hr : 1 < primeRank 3 L) {i : G}
    (hi : i ∈ centralizer (L : Set G)) (hi2 : orderOf i = 2) :
    (L ⧸ pCore 2 L) ≃*
      (L.subgroupOf (involutionCentralizer i)).map
        (QuotientGroup.mk' (pPrimeCore 3 (involutionCentralizer i))) := by
  have hL := h.involution_component hi hi2
  exact SignedReduction.localQuotientEquiv hL.1 hL.2
    (hG.evenType.oddCore i hi2) (by omega)

end CFSG.Quasithin.Chapter16.Intersections
