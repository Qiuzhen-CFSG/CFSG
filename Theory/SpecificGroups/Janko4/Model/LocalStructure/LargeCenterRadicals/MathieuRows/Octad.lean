module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Normalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The native octad radical and its full alternating quotient

The pointwise octad group in M24 has the octad as its common fixed set, so
its full normalizer is the setwise octad stabilizer. Pullback through the
literal max1 quotient gives an ambient radical of order 2^15, with the full
normalizer and intrinsic two-core retained. Its quotient is the concrete A8,
via the proved octad action and the exceptional PSL4(2) comparison.
The final exports identify these subgroups with the existing native Q and D.

Source: An--O'Brien--Wilson (2003), Section 4 and the 2^11:2^4 row of
Table 1, pp.122,124. This is distinct from the excluded 2^10:2^4 row.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open ElementaryNormalizerCover MathieuHallActors
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

/-- The full Mathieu normalizer of the pointwise octad group is its setwise stabilizer. -/
theorem octad_kernel_normalizer (O : Octad) :
    normalizer (octadPointwiseKernel O : Set M24) = octadStabilizer O := by
  apply le_antisymm
  · have hc : Nat.card (octadPointwiseKernel O) = 16 := by
      rw [← octad_core_map_eq_pointwise,
        card_map_of_injective (octadStabilizer O).subtype_injective]
      exact M24ChapterHStabilizers.OctadAction.core_card O
    have hn : octadPointwiseKernel O ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hc
      omega
    obtain ⟨z,hz,hz1⟩ := (octadPointwiseKernel O).bot_or_exists_ne_one.resolve_left hn
    intro g hg
    have hz' : g * z * g⁻¹ ∈ octadPointwiseKernel O :=
      (mem_normalizer_iff.mp hg z).mp hz
    have hz1' : g * z * g⁻¹ ≠ 1 := by
      change (MulAut.conj g) z ≠ 1
      intro he
      exact hz1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp he)
    change g • O.val = O.val
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_smul_finset.mp hj
      apply (octad_kernel_fixed_point_iff O _ hz' hz1' _).mp
      rw [mul_smul, mul_smul, inv_smul_smul,
        (octad_kernel_fixed_point_iff O z hz hz1 i).mpr hi]
    · simp
  · exact octad_stabilizer_le_normalizer_pointwiseKernel O

/-- The core equation in the full Mathieu normalizer uses the actual pointwise group. -/
theorem octad_kernel_normalizer_core (O : Octad) :
    (normalizer (octadPointwiseKernel O : Set M24)).pCoreIn 2 = octadPointwiseKernel O := by
  rw [octad_kernel_normalizer]
  exact octad_core_map_eq_pointwise O

/-- The native order-2^15 row is the literal preimage of the octad translations. -/
abbrev octadRadical (O : Octad) : Subgroup Model := preimage (octadPointwiseKernel O)

/-- The actual preimage has order 2^15. -/
theorem octadRadical_card (O : Octad) : Nat.card (octadRadical O) = 2^15 := by
  rw [preimage_card, ← octad_core_map_eq_pointwise,
    card_map_of_injective (octadStabilizer O).subtype_injective,
    M24ChapterHStabilizers.OctadAction.core_card]
  norm_num

/-- Its full ambient normalizer is the literal preimage of the octad stabilizer. -/
theorem octadRadical_normalizer (O : Octad) :
    normalizer (octadRadical O : Set Model) = preimage (octadStabilizer O) := by
  rw [normalizer_preimage, octad_kernel_normalizer]

/-- This actual preimage is radical in J4, not just in the Mathieu local. -/
theorem octadRadical_isPRadical (O : Octad) : (octadRadical O).IsPRadical 2 :=
  preimage_isPRadical _ (octad_kernel_normalizer_core O)

/-- The intrinsic full two-core is the literal restriction of the radical. -/
theorem octadRadical_full_core (O : Octad) :
    pCore 2 (normalizer (octadRadical O : Set Model)) =
      (octadRadical O).subgroupOf (normalizer (octadRadical O : Set Model)) :=
  radical_core_eq _ (octadRadical_isPRadical O)

/-- The full native normalizer quotient is the concrete alternating group A8. -/
def octadRadicalQuotientEquiv (O : Octad) :
    let N := normalizer (octadRadical O : Set Model)
    N ⧸ pCore 2 N ≃* alternatingGroup (Fin 8) :=
  (coreQuotientCongr (MulEquiv.subgroupCongr (octadRadical_normalizer O))).trans
    ((preimageQuotientEquiv (octadStabilizer O)).trans
      ((M24ChapterHStabilizers.OctadAction.quotientEquiv O).trans
        Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8))

/-- The preimage is exactly the Q already used by the native linear-five branch. -/
theorem standard_octadRadical_eq_Q : octadRadical standardOctad = LinearFive.Q := rfl

/-- The earlier Q/D definitions retain their full ambient normalizer equality. -/
theorem Q_normalizer_eq_D : normalizer (LinearFive.Q : Set Model) = LinearFive.D :=
  octadRadical_normalizer standardOctad

/-- The earlier native Q is an actual ambient radical. -/
theorem Q_isPRadical : LinearFive.Q.IsPRadical 2 := octadRadical_isPRadical standardOctad

/-- The earlier D has Q as its full ambient two-core. -/
theorem D_core_eq_Q : LinearFive.D.pCoreIn 2 = LinearFive.Q := by
  rw [← Q_normalizer_eq_D]
  exact Q_isPRadical.2

/-- The literal original D, modulo its intrinsic full core, is A8. -/
def D_quotientEquiv : LinearFive.D ⧸ pCore 2 LinearFive.D ≃* alternatingGroup (Fin 8) :=
  (coreQuotientCongr (MulEquiv.subgroupCongr Q_normalizer_eq_D.symm)).trans
    (octadRadicalQuotientEquiv standardOctad)

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
