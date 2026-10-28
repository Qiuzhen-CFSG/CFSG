module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive.Normalizer

/-!
# The local parameter of a marked deleted alternating-five section

The original section with trivial denominator gives linear coordinates on
the full numerator. Extending these same coordinates to the entire local
automizer embeds it in the actual deleted-module normalizer, whose parameter
is at most one. Component normalization is the only ambient group input.
Source: Aschbacher–Smith, 10.2.12, printed p.754.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G]

/-- The full local automizer of an actual deleted A₅ section has parameter at most one. -/
theorem moduleA_local_deleted_section_le_one
    (H W M : Subgroup G) [IsElementaryAbelian 2 W]
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : Representation.BinaryConjugationSection H W ⊥
      (((naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype).comp q))
    (hHM : H ≤ M)
    (hNH : M ⊓ normalizer (W : Set G) ≤ normalizer (H : Set G)) :
    moduleA ((automizerRepresentation W).comp (inducedAutomizer W M).subtype) ≤ 1 := by
  let N := M ⊓ normalizer (W : Set G)
  have hNB : N ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top]
    exact le_top
  have hk : commutatorPreimage N W ⊥ ≤ centralizer (W : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique (commutator_commutatorPreimage_le N W ⊥ hNB))
  obtain ⟨τ,f,hf,hfτ,hact⟩ := exists_local_section_normalizer H W ⊥ M
    ((naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)
    q hq c hHM hNH hNB hk
  have hci : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq,bot_subgroupOf]
  let E : Additive W ≃ₗ[ZMod 2] natural (Fin 5) :=
    LinearEquiv.ofBijective (c.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hci,c.onto⟩
  apply (moduleA_le_of_equivariant_injective
    ((automizerRepresentation W).comp (inducedAutomizer W M).subtype)
    _ f hf E ?_).trans moduleA_fiveDeleted_normalizer_le_one
  intro a w
  obtain ⟨n,rfl⟩ := localNormalizerAction_surjective W M a
  rw [hfτ]
  exact (hact n w.toMul).symm
end CFSG.Quasithin.ChapterE
