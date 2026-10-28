module

public import Stellmacher.SectionNine.NineFiveM12NormalizerEnumeration

@[expose] public section

namespace Stellmacher.SectionNine.M12Realization

open Sporadic.Mathieu
open scoped Pointwise

def M12MaskIndexCheck (permutation : Equiv.Perm (Fin 12)) : Prop :=
  ∀ source : Fin 132, ∃ target : Fin 132, ∀ point : Fin 12,
    (m12BlockMask source).testBit (permutation.symm point).val =
      (m12BlockMask target).testBit point.val

noncomputable instance : DecidablePred M12MaskIndexCheck :=
  fun _ => inferInstanceAs (Decidable (∀ _ : Fin 132, ∃ _ : Fin 132, ∀ _ : Fin 12, _))

theorem m12BlockAt_injective_for_mask_check : Function.Injective m12BlockAt := by
  have hcard : (Finset.univ.image m12BlockAt).card =
      (Finset.univ : Finset (Fin 132)).card := by
    rw [m12BlockAt_image, m12Blocks_cardinality]
    decide +kernel
  have hinj := Finset.card_image_iff.mp hcard
  intro source target heq
  exact hinj (Finset.mem_univ source) (Finset.mem_univ target) heq

theorem m12Perm_blockAt_bits_iff (permutation : Equiv.Perm (Fin 12))
    (source target : Fin 132) :
    permutation • m12BlockAt source = m12BlockAt target ↔
      ∀ point : Fin 12,
        (m12BlockMask source).testBit (permutation.symm point).val =
          (m12BlockMask target).testBit point.val := by
  constructor
  · intro heq point
    have hmem : permutation.symm point ∈ m12BlockAt source ↔
        point ∈ m12BlockAt target := by
      rw [← heq, Finset.mem_smul_finset]
      constructor
      · intro hpoint
        exact ⟨permutation.symm point, hpoint, by simp⟩
      · rintro ⟨preimage, hpreimage, hpoint⟩
        rw [← hpoint]
        simpa using hpreimage
    apply Bool.eq_iff_iff.mpr
    simpa [m12BlockAt, m12MaskBlock] using hmem
  · exact m12Perm_smul_blockAt_of_bits permutation source target

theorem preservesM12Blocks_iff_maskIndexCheck (permutation : Equiv.Perm (Fin 12)) :
    PreservesM12Blocks permutation ↔ M12MaskIndexCheck permutation := by
  constructor
  · intro hpreserves source
    have hsource : m12BlockAt source ∈ m12Blocks := by
      rw [← m12BlockAt_image]
      exact Finset.mem_image.mpr ⟨source, Finset.mem_univ _, rfl⟩
    have htarget : permutation • m12BlockAt source ∈ m12Blocks := by
      rw [← hpreserves]
      exact Finset.smul_mem_smul_finset hsource
    rw [← m12BlockAt_image] at htarget
    obtain ⟨target, _, htarget⟩ := Finset.mem_image.mp htarget
    exact ⟨target, (m12Perm_blockAt_bits_iff permutation source target).mp htarget.symm⟩
  · intro hcheck
    classical
    choose index hbits using hcheck
    have hblock : ∀ source, permutation • m12BlockAt source =
        m12BlockAt (index source) := fun source =>
      m12Perm_smul_blockAt_of_bits permutation source (index source) (hbits source)
    have hinj : Function.Injective index := by
      intro source target heq
      apply m12BlockAt_injective_for_mask_check
      apply (MulAction.injective permutation)
      change permutation • m12BlockAt source = permutation • m12BlockAt target
      rw [hblock, hblock, heq]
    have hsurj := (Finite.surjective_of_injective hinj)
    apply m12_blocks_smul_of_index permutation index _ hblock
    exact Finset.image_univ_of_surjective hsurj

def NormalizerMaskIndexCheck (parameters : NormalizerParameters) : Prop :=
  M12MaskIndexCheck (normalizerParameterPerm parameters)

noncomputable instance : DecidablePred NormalizerMaskIndexCheck :=
  fun _ => inferInstanceAs (Decidable (M12MaskIndexCheck _))

theorem normalizerParameterPerm_preservesM12Blocks_iff (parameters : NormalizerParameters) :
    PreservesM12Blocks (normalizerParameterPerm parameters) ↔
      NormalizerMaskIndexCheck parameters :=
  preservesM12Blocks_iff_maskIndexCheck (normalizerParameterPerm parameters)

noncomputable def normalizerLocalMaskParameters : Finset NormalizerParameters :=
  Finset.univ.filter (fun parameters =>
    NormalizerMaskIndexCheck parameters ∧
      NormalizesPlanePerms (normalizerParameterPerm parameters))

noncomputable def normalizerIntersectionMaskParameters : Finset NormalizerParameters :=
  normalizerLocalMaskParameters.filter (fun parameters =>
    CentralizesCenterPerm (normalizerParameterPerm parameters))

theorem normalizerLocalParameters_eq_maskParameters :
    normalizerLocalParameters = normalizerLocalMaskParameters := by
  ext parameters
  simp only [normalizerLocalParameters, normalizerLocalMaskParameters,
    Finset.mem_filter, normalizerParameterPerm_preservesM12Blocks_iff]

theorem normalizerIntersectionParameters_eq_maskParameters :
    normalizerIntersectionParameters = normalizerIntersectionMaskParameters := by
  rw [normalizerIntersectionParameters, normalizerIntersectionMaskParameters,
    normalizerLocalParameters_eq_maskParameters]

end Stellmacher.SectionNine.M12Realization
