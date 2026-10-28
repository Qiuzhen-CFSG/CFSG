module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.Alternatives
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.Obstructions
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.Native
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.Coverage

/-!
# Transitive small M₂₄ Sylow overgroups preserve a translated standard trio

The marked Sylow subgroup preserves an octad and a specified translate of the
standard trio. Checked prime-cycle obstructions put every eligible double-coset
representative in one of these stabilizers. The exhaustive native double-coset
coverage puts an overgroup in their union and hence in one of them.
Transitivity excludes the octad. Sylow conjugacy transports the result to any
Sylow subgroup, with the product of the Sylow and marked-trio conjugators as
the required native M₂₄ witness.

Both orders 9216 and 27648 are covered, and no solvability assumption is needed
in the finite containment argument. The 239,085 checked distinct native cosets
have the full index of the marked Sylow subgroup, so the coverage includes all
sextet-stabilizer possibilities.

Source: Aschbacher–Smith, printed p.511 (PDF p.528); GLS3 Table 5.3e;
Aschbacher, *Sporadic Groups*, Chapter 7, §20. See `TransitiveCoverage/source/`
for the finite data, provenance, and verification method.
-/

public section
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
open SylowNormalizer
open Subgroup MulAction

/-- The permutation-level coverage contract is exactly native group coverage. -/
theorem covers_iff_native : Covers ↔
    ∀ g : M24, ∃ (i : Fin 510) (s t : candidate),
      (s : M24) * representative i * (t : M24) = g := by
  constructor
  · intro hc g
    obtain ⟨i, s, t, he⟩ := hc g
    exact ⟨i, s, t, Subtype.ext he⟩
  · intro hc g
    obtain ⟨i, s, t, he⟩ := hc g
    exact ⟨i, s, t, congrArg Subtype.val he⟩

/-- Exhaustive double-coset coverage and the certified obstructions give
containment in one of the two actual marked stabilizers. -/
theorem marked_containment_of_covers (hcover : Covers) (H : Subgroup M24)
    (hS : candidate ≤ H) (hcard : Nat.card H = 9216 ∨ Nat.card H = 27648) :
    H ≤ octadStabilizer markedOctad ∨ H ≤ markedTrioStabilizer := by
  apply SubgroupClass.subset_union.mp
  intro g hg
  obtain ⟨i, s, t, he⟩ := hcover g
  have hr : representativePerm i ∈ H.map M24.subtype := by
    have h := (H.map M24.subtype).mul_mem
      ((H.map M24.subtype).mul_mem
        ((H.map M24.subtype).inv_mem (Subgroup.mem_map_of_mem _ (hS s.property)))
        (Subgroup.mem_map_of_mem _ hg))
      ((H.map M24.subtype).inv_mem (Subgroup.mem_map_of_mem _ (hS t.property)))
    change (s : M24).val⁻¹ * g.val * (t : M24).val⁻¹ ∈ H.map M24.subtype at h
    rw [← he] at h
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  rcases representative_stabilizes H hS hcard i hr with ho | ht
  · left
    have hs : (s : M24).val • markedOctadPoints = markedOctadPoints :=
      candidate_le_markedOctad s.property
    have ht : (t : M24).val • markedOctadPoints = markedOctadPoints :=
      candidate_le_markedOctad t.property
    change g.val • markedOctadPoints = markedOctadPoints
    rw [← he, mul_smul, mul_smul, ht, ho, hs]
  · right
    have hs : (s : M24).val • markedTrioParts = markedTrioParts :=
      candidate_le_markedTrio s.property
    have hu : (t : M24).val • markedTrioParts = markedTrioParts :=
      candidate_le_markedTrio t.property
    change g.val • markedTrioParts = markedTrioParts
    rw [← he, mul_smul, mul_smul, hu, ht, hs]

private theorem conjugate_pretransitive (H : Subgroup M24) (g : M24)
    (ht : IsPretransitive H (Fin 24)) :
    IsPretransitive (H.map (MulAut.conj g⁻¹).toMonoidHom) (Fin 24) := by
  constructor
  intro x y
  obtain ⟨h, hh⟩ := ht.exists_smul_eq (g • x) (g • y)
  refine ⟨⟨(MulAut.conj g⁻¹) h, Subgroup.mem_map_of_mem _ h.property⟩, ?_⟩
  have hc := congrArg (fun z : Fin 24 => g⁻¹ • z) hh
  change g⁻¹ • ((h : M24) • (g • x)) = g⁻¹ • (g • y) at hc
  change (g⁻¹ * (h : M24) * g) • x = y
  simpa only [mul_smul, inv_smul_smul] using hc

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement
open TransitiveCoverage SylowNormalizer
open Subgroup MulAction

/-- Transport the marked containment argument using native Sylow conjugacy. -/
theorem transitiveSmallSylowPlacement_of_covers (hcover : Covers) :
    TransitiveSmallSylowPlacement := by
  intro S H hSH _ hcard htrans
  have hp : IsPGroup 2 candidate := IsPGroup.of_card
    (show Nat.card candidate = 2 ^ 10 by rw [candidate_card]; norm_num)
  have hi : ¬ 2 ∣ candidate.index := by
    have hc := candidate.card_mul_index
    rw [candidate_card, m24_order] at hc
    have he : candidate.index = 239085 := by omega
    rw [he]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 (hp.toSylow hi) S
  have hmap : candidate.map (MulAut.conj g).toMonoidHom = S.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  let K := H.map (MulAut.conj g⁻¹).toMonoidHom
  have hCK : candidate ≤ K := by
    intro c hc
    apply Subgroup.mem_map.mpr
    refine ⟨(MulAut.conj g) c, hSH ?_, ?_⟩
    · rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hc
    · simp [MulAut.conj_apply, mul_assoc]
  have hcardK : Nat.card K = 9216 ∨ Nat.card K = 27648 := by
    have he : Nat.card K = Nat.card H :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    rwa [he]
  have htK : IsPretransitive K (Fin 24) := conjugate_pretransitive H g htrans
  have hKT : K ≤ markedTrioStabilizer :=
    (marked_containment_of_covers hcover K hCK hcardK).resolve_left
      (fun hO => not_pretransitive_of_le_markedOctad K hO htK)
  refine ⟨g * markedConjugator, ?_⟩
  intro h hh
  have hm := hKT (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hh)
  change (g⁻¹ * h * g) • markedTrioParts = markedTrioParts at hm
  have hc := congrArg (fun A : Finset (Finset (Fin 24)) => g • A) hm
  change h • ((g * markedConjugator) • standardTrio.parts) =
    (g * markedConjugator) • standardTrio.parts
  rw [mul_smul, markedConjugator_parts]
  simpa only [mul_smul, smul_inv_smul] using hc

/-- Every transitive solvable Sylow overgroup of either specified order lies
in the stabilizer of an actual M₂₄ translate of the standard trio. -/
theorem transitiveSmallSylowPlacement : TransitiveSmallSylowPlacement :=
  transitiveSmallSylowPlacement_of_covers covers

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement
