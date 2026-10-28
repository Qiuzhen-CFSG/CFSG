module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Checks

/-!
# From eleven relators and eleven seeds to all residual Fi23 edges

Well-founded induction on the checked rank table proves every A-edge
membership. Rank-zero cases use the two loop hypotheses, tree identities,
and seed memberships in either orientation. At positive rank, the cyclic
relator identity isolates the target from smaller-rank edges.

The eleven actual permutation identities and eleven seed memberships remain
explicit hypotheses. This is a finite-certificate reduction, not an
unconditional stabilizer theorem. Source: ATLAS F23G1-p31671B0 and GLS3
Table 5.3u; the Fischer paragraph near line 1042 of
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

theorem a_edges_of_rank_certificates
    (hRelations : ∀ i : Fin 11, wordValue (relator i) = 1)
    (hSeeds : ∀ x : Fin 31671, seed x = true → edge generatorA x ∈ KernelUpperData.first)
    (hAloops : ∀ x : Fin 31671, generatorA x = x → edge generatorA x ∈ KernelUpperData.first)
    (hBloops : ∀ x : Fin 31671, generatorB x = x → edge generatorB x ∈ KernelUpperData.first)
    (x : Fin 31671) : edge generatorA x ∈ KernelUpperData.first := by
  induction x using (measure rank).wf.induction with
  | h x ih =>
    have hc := point_checked x
    have hx : Fin.ofNat 31671 x.val = x := by simp
    simp only [pointTest, hx] at hc
    by_cases hz : rank x = 0
    · rw [if_pos hz] at hc
      simp only [zeroTest, Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with ((hfix | htree) | hseed) | hseed
      · exact hAloops x (by simpa only [generatorA_apply_eq_sourceA] using hfix)
      · rw [a_tree_edge_eq_one x htree]
        exact KernelUpperData.first.one_mem
      · exact hSeeds x hseed
      · have hm := hSeeds (sourceA x) hseed
        rw [← generatorA_apply_eq_sourceA, a_edge_reverse] at hm
        simpa only [inv_inv] using KernelUpperData.first.inv_mem hm
    · rw [if_neg hz] at hc
      obtain ⟨w, hw, hp⟩ : ∃ w, rotated x = 0 :: w ∧
          pathBelow rank (rank x) w (sourceA (start x)) = true := by
        cases hr : rotated x with
        | nil => simp only [positiveTest, hr, Bool.false_eq_true] at hc
        | cons s w =>
          simp only [positiveTest, hr, Bool.and_eq_true, decide_eq_true_eq] at hc
          exact ⟨w, congrArg (fun s => s :: w) hc.1, hc.2⟩
      have hr : wordValue (0 :: w) = 1 := by
        rw [← hw]
        exact wordValue_cut _ _ (hRelations (relationIndex x))
      have hm : edge generatorA (start x) ∈ KernelUpperData.first := by
        apply first_edge_mem w (start x) hr
        apply pathBelow_mem rank (rank x) hBloops (fun y hy => ih y hy)
        simpa only [generatorA_apply_eq_sourceA] using hp
      by_cases hs : code x / 33554432 == 0
      · simpa only [start, if_pos hs] using hm
      · simp only [start, if_neg hs, ← generatorA_apply_eq_sourceA, a_edge_reverse] at hm
        simpa only [inv_inv] using KernelUpperData.first.inv_mem hm

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links
