module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.Five
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerComplementPair
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerFullThird

/-!
# Simultaneous canonical marking of the actual third local overlaps

The native sixty-element pair is aligned by a conjugator inside the actual
projective complement. Its order-180 neighbour retains its A5 complement
and order-thirty intersection. The proved pair-fixing correction then aligns
that entire neighbour. Thus the same actual third-local isomorphism marks
both full overlaps and retains the cubic kernel.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup SourceRecognition.CubicNormalizerModel

private theorem fixed_map (H : Subgroup Canonical) (τ : MulAut Canonical)
    (h : ∀ x ∈ H, τ x = x) : H.map τ.toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change τ x ∈ H
    rw [h x hx]
    exact hx
  · intro x hx
    exact ⟨x,hx,h x hx⟩

/-- The two raw native overlaps admit a simultaneous canonical correction. -/
theorem exists_raw_overlap_correction :
    ∃ τ : MulAut Canonical,
      rawPair.map τ.toMonoidHom = pair ∧
      rawThird.map τ.toMonoidHom = thirdOverlap ∧
      projection.ker.map τ.toMonoidHom = projection.ker := by
  obtain ⟨p,hp⟩ := exists_conjugating_pair_inr rawPair kernel_le_rawPair rawPair_card
  let σ := MulAut.conj (SemidirectProduct.inr p : Canonical)
  let C := rawThird.map σ.toMonoidHom
  let K := (SemidirectProduct.inr : P →* Canonical).range
  have hK : K.map σ.toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (K.le_normalizer ⟨p,rfl⟩)
  have hker : projection.ker.map σ.toMonoidHom = projection.ker :=
    Subgroup.Normal.map_conj_eq _ _
  have hkerC : projection.ker ≤ C := hker ▸ map_mono kernel_le_rawThird
  have hi : (rawThird ⊓ K).map σ.toMonoidHom = C ⊓ K := by
    rw [map_inf _ _ _ σ.injective,hK]
  have hfive : Nonempty ((C ⊓ K : Subgroup Canonical) ≃* alternatingGroup (Fin 5)) :=
    ⟨(MulEquiv.subgroupCongr hi.symm).trans
      (((rawThird ⊓ K).equivMapOfInjective σ.toMonoidHom σ.injective).symm.trans
        rawThird_complement_equiv.some)⟩
  have hcard : Nat.card (C ⊓ pair : Subgroup Canonical) = 30 := by
    rw [←hp,←map_inf _ _ _ σ.injective,card_map_of_injective σ.injective,inf_comm]
    exact rawPair_inf_rawThird_card
  obtain ⟨ρ,hfix,hfixker,_hcomp,hthird⟩ := exists_full_third_alignment C hkerC hfive hcard
  refine ⟨σ.trans ρ,?_,?_,?_⟩
  · change rawPair.map (ρ.toMonoidHom.comp σ.toMonoidHom) = _
    rw [←map_map,hp,fixed_map _ _ hfix]
  · change rawThird.map (ρ.toMonoidHom.comp σ.toMonoidHom) = _
    rw [←map_map]
    exact hthird
  · change projection.ker.map (ρ.toMonoidHom.comp σ.toMonoidHom) = _
    rw [←map_map,hker,fixed_map _ _ hfixker]

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
