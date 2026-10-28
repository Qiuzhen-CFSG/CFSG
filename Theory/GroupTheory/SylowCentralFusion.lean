module

public import Theory.GroupTheory.SylowCentralFusion.CenterSelection
public import Theory.GroupTheory.SylowCentralFusion.CentralConjugate
public import Theory.GroupTheory.SylowCentralFusion.NoncentralSelection

/-!
# Assembly of the two central-involution fusion selections

The center-containing selection is proved by centric fusion. For the
normal-closure selection, Burnside fusion handles central conjugates, and
maximal Sylow-centralizer order handles noncentral conjugates. The common
local argument supplies both odd-order movers and both centralizer-normalizer
conditions, preserving each selected subgroup.

`centralInvolutionFusion` proves the published two-witness contract without
additional premises. The two selections may be different; the second retains
the normal-closure consequence of the source's conjugate-generation clause.
Source: Glauberman's Lemma 1, pp.155–156, Math. Z. 93 (1966),
DOI 10.1007/BF01111033.
-/

public section
namespace SylowCentralFusion
open Subgroup
universe u

/-- Assemble the exact published contract from the remaining noncentral
normal-closure branch. All other source clauses are discharged here. -/
theorem centralInvolutionFusion_of_noncentralNormalClosureSelection
    (noncentral : NoncentralNormalClosureSelection.{u}) :
    CentralInvolutionFusion.{u} := by
  intro G _ _ T z hz2 hzT hc hf
  constructor
  · exact exists_center_witness T z hzT hc hf
  · obtain ⟨g, hgT, hgm⟩ := hf
    have hs : ∃ s : NormalizerSelection T z,
        s.subgroup ≤ normalClosure ({z} : Set G) := by
      by_cases hgc : g * z * g⁻¹ ∈ centralizer (T : Set G)
      · exact exists_normalClosure_normalizerSelection_of_central_conjugate
          T z hzT hc ⟨g, hgc, hgm⟩
      · exact noncentral G T z hz2 hzT hc ⟨g, hgT, hgc⟩
    obtain ⟨s, hs⟩ := hs
    obtain ⟨w, hw⟩ := s.exists_witness T z hc
    exact ⟨w, hw ▸ hs⟩

/-- Glauberman's two selections for a central involution with a distinct
conjugate in its Sylow two-subgroup: one contains the ambient Sylow center,
and the other lies in the involution's normal closure. Each has the exact
Sylow normalizer and an odd-order mover normalizing its Sylow centralizer. -/
theorem centralInvolutionFusion : CentralInvolutionFusion.{u} :=
  centralInvolutionFusion_of_noncentralNormalClosureSelection
    noncentralNormalClosureSelection

end SylowCentralFusion
