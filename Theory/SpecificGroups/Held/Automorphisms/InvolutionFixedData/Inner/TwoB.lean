module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Reduction
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Max5Upper

/-!
# The exact order of the inner Held 2B fixed subgroup

The numerical consequence of the `D₈^{+3}.L₃(2)` row in GLS3 Table 5.3p
is order `2^7 * 168 = 21504`. Here the representative is the literal
ATLAS word `max5First ^ 4` in the degree-2058 carrier.

The existing odd symmetry of the representative's colored graph commutes
with `centralWord`. Its four images are checked using the already certified
`pcTable 0`, and the graph's four-point base proves equality. The unchanged
row-zero conjugator transports this odd symmetry to the graph centralizer
of `max5First ^ 4`. Every Held permutation is even, so max5 has index at
least two in that graph centralizer. Its bound 43008 and the existing max5
lower bound 21504 therefore give the exact local order.

Finally, the completed ambient-containment calculation identifies the
Held centralizer with max5; its two-group premise is discharged by the
representative's checked polycyclic words. Inner conjugation has precisely
this centralizer as its literal fixed subgroup. No global Held order or
simplicity assumption is needed, and no extension structure is asserted.

Sources: GLS3 Table 5.3p, printed p.277; the unchanged ATLAS HeG1-p2058B0
and HeG1-max5W1 words and the certificates cited by the imported modules.
The 2A structure and exhaustive involution coverage are separate results.
-/

namespace Held.InvolutionFixedData.TwoB
open Subgroup TwoLocalCandidates TwoLocalCandidates.MaximalNormalizerCatalogue
open LocalPairs.SylowGeometry.Calculations
open LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound

set_option maxRecDepth 4096 in
private theorem odd_commutes_centralWord :
    oddPermutation * representation centralWord = representation centralWord * oddPermutation := by
  have hz : representation centralWord ∈ NormalizerGraph.preservingGroup :=
    Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup centralWord.property
  have ho : oddPermutation ∈ NormalizerGraph.preservingGroup := odd_mem.1
  have hword : centralWord = TwoGroup.pcGenerator 0 := by
    simp [centralWord, word, commonWord, letter, TwoGroup.pcGenerator, mul_assoc]
    rfl
  have h : ∀ i : Fin 4,
      (oddPermutation * representation centralWord) ⟨i.val, by omega⟩ =
      (representation centralWord * oddPermutation) ⟨i.val, by omega⟩ := by
    rw [hword, ← TwoGroup.Tables.pcTable_eq]
    set_option maxRecDepth 16384 in
    decide +kernel
  let x := oddPermutation * representation centralWord
  let y := representation centralWord * oddPermutation
  have he : y⁻¹ * x = 1 := by
    apply NormalizerGraph.CardBound.four_fixed_eq_one
    · exact NormalizerGraph.preservingGroup.mul_mem
        (NormalizerGraph.preservingGroup.inv_mem
          (NormalizerGraph.preservingGroup.mul_mem hz ho))
        (NormalizerGraph.preservingGroup.mul_mem ho hz)
    · intro z hz
      have heq : x z = y z := h ⟨z.val, hz⟩
      change y.symm (x z) = z
      rw [heq]
      exact y.symm_apply_apply z
  exact (inv_mul_eq_one.mp he).symm

private theorem exists_odd_centralizer :
    ∃ σ : Equiv.Perm (Fin 2058),
      σ ∈ NormalizerGraph.preservingGroup ⊓
        centralizer ({representation (max5First ^ 4)} : Set (Equiv.Perm (Fin 2058))) ∧
      Equiv.Perm.sign σ ≠ 1 := by
  let q := representation (conjugator 0)
  let e := MulAut.conj q
  have hq : q ∈ NormalizerGraph.preservingGroup :=
    Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
      (conjugator 0).property
  have hz : e (representation (max5First ^ 4)) = representation centralWord := by
    have h := congrArg representation conjugator_zero_max5First_four
    simpa only [e, q, MulAut.conj_apply, map_mul, map_inv] using h
  refine ⟨e.symm oddPermutation, ⟨?_, ?_⟩, ?_⟩
  · change q⁻¹ * oddPermutation * q ∈ NormalizerGraph.preservingGroup
    exact NormalizerGraph.preservingGroup.mul_mem
      (NormalizerGraph.preservingGroup.mul_mem
        (NormalizerGraph.preservingGroup.inv_mem hq) odd_mem.1) hq
  · apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simp only [map_mul, e.apply_symm_apply, hz]
    exact odd_commutes_centralWord
  · change Equiv.Perm.sign (q⁻¹ * oddPermutation * q) ≠ 1
    rw [map_mul, map_mul, map_inv, odd_sign]
    simp

/-- The literal max5 candidate has exactly the order of the 2B row. -/
public theorem max5_card : Nat.card max5 = 21504 := by
  let D := NormalizerGraph.preservingGroup ⊓
    centralizer ({representation (max5First ^ 4)} : Set (Equiv.Perm (Fin 2058)))
  have hmap : max5.map representation ≤ D := by
    apply le_inf
    · rintro _ ⟨g, _, rfl⟩
      exact Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup g.property
    · exact (Subgroup.map_mono CentralInvolutionBounds.max5_le_centralizer).trans
        (by simpa only [Set.image_singleton] using
          map_centralizer_le_centralizer_image ({max5First ^ 4} : Set He) representation)
  let L := (max5.map representation).subgroupOf D
  have hproper : L ≠ ⊤ := by
    obtain ⟨σ, hσ, hodd⟩ := exists_odd_centralizer
    intro he
    have hm : (⟨σ, hσ⟩ : D) ∈ L := he ▸ Subgroup.mem_top _
    obtain ⟨g, _, hg⟩ := hm
    change representation g = σ at hg
    apply hodd
    rw [← hg]
    simpa only [MonoidHom.comp_apply] using
      hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g
  have hi : 2 ≤ L.index := L.one_lt_index_of_ne_top hproper
  have he : Nat.card L = Nat.card max5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hmap).toEquiv,
      card_map_of_injective representation_injective]
  have hb : Nat.card max5 * 2 ≤ Nat.card D := by
    rw [← he, ← L.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  have hu : Nat.card D ≤ 43008 := CentralInvolutionBounds.graph_centralizer_card_le
  have hl := CentralInvolutionBounds.max5_card_lower_bound
  omega

/-- The completed ambient containment identifies the literal 2B centralizer. -/
public theorem centralizer_eq_max5 : centralizer ({max5First ^ 4} : Set He) = max5 :=
  max5_involution_centralizer_eq representative_isPGroup

end Held.InvolutionFixedData.TwoB

namespace Held.InvolutionFixedData
/-- The literal inner 2B automorphism has fixed subgroup of order 21504. -/
public theorem twoB_fixedSubgroup_card :
    Nat.card (MulAut.conj (TwoLocalCandidates.max5First ^ 4)).fixedSubgroup = 21504 := by
  rw [MulAut.fixedSubgroup_conj, TwoB.centralizer_eq_max5, TwoB.max5_card]
end Held.InvolutionFixedData
