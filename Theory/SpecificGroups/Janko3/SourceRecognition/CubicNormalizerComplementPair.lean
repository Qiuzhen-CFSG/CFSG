module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModelPair

/-!
# Aligning the full pair while retaining the cubic complement

Full pairs contain the cubic kernel, so their conjugacy can be realized by
an element of the fixed projective complement. Consequently split recognition
can retain a given complement while aligning the entire pair subgroup.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel

/-- The full pair conjugator may be chosen inside the projective complement. -/
theorem exists_conjugating_pair_inr (H : Subgroup Model) (hH : projection.ker ≤ H)
    (hcH : Nat.card H = 60) :
    ∃ p : P, H.map (MulAut.conj (SemidirectProduct.inr p)).toMonoidHom = pair := by
  obtain ⟨g,hg⟩ := exists_conjugating_pair H hH hcH
  let t : Model := SemidirectProduct.inr (projection g)
  have hp : projection t = projection g := rfl
  have hcomp (x : Model) : projection.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (projection x)).toMonoidHom.comp projection := by
    apply MonoidHom.ext
    intro y
    change projection (x * y * x⁻¹) = projection x * projection y * (projection x)⁻¹
    simp only [map_mul,map_inv]
  have him : (H.map (MulAut.conj t).toMonoidHom).map projection = pair.map projection := by
    rw [←hg,map_map,map_map,hcomp,hcomp,hp]
  have hk : projection.ker ≤ H.map (MulAut.conj t).toMonoidHom := by
    rw [←Subgroup.Normal.map_conj_eq projection.ker t]
    exact map_mono hH
  exact ⟨projection g,map_injective_of_ker_le projection hk kernel_le_pair him⟩

private theorem inr_conj_range (p : P) :
    (SemidirectProduct.inr : P →* Model).range.map
      (MulAut.conj (SemidirectProduct.inr p)).toMonoidHom =
      (SemidirectProduct.inr : P →* Model).range := by
  apply le_antisymm
  · rintro _ ⟨_,⟨q,rfl⟩,rfl⟩
    refine ⟨p * q * p⁻¹,?_⟩
    simp only [map_mul,map_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
  · rintro _ ⟨q,rfl⟩
    refine ⟨SemidirectProduct.inr (p⁻¹ * q * p),⟨_,rfl⟩,?_⟩
    change SemidirectProduct.inr p * SemidirectProduct.inr (p⁻¹ * q * p) *
      (SemidirectProduct.inr p)⁻¹ = SemidirectProduct.inr q
    rw [map_mul,map_mul,map_inv]
    group

/-- Split recognition aligns the whole pair while retaining the supplied
complement, and hence all original subgroups inside that complement. -/
theorem exists_splitEquiv_pair
    {E : Type*} [Group E] [Finite E]
    (V K H : Subgroup E) [V.Normal] (hcomp : V.IsComplement' K)
    (eK : K ≃* P) (hV : Nat.card V = 3) (hnc : ¬ V ≤ center E)
    (hVH : V ≤ H) (hH : Nat.card H = 60) :
    ∃ e : E ≃* Model,
      H.map e.toMonoidHom = pair ∧ V.map e.toMonoidHom = projection.ker ∧
      K.map e.toMonoidHom = (SemidirectProduct.inr : P →* Model).range := by
  obtain ⟨eV,e0,heV,heK,_,_⟩ := exists_splitEquiv V K hcomp eK hV hnc
  have hVm : V.map e0.toMonoidHom = projection.ker := by
    rw [projection_ker]
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact ⟨eV ⟨v,hv⟩,(heV ⟨v,hv⟩).symm⟩
    · rintro _ ⟨z,rfl⟩
      obtain ⟨v,rfl⟩ := eV.surjective z
      exact ⟨v,v.property,heV v⟩
  have hKm : K.map e0.toMonoidHom = (SemidirectProduct.inr : P →* Model).range := by
    apply le_antisymm
    · rintro _ ⟨k,hk,rfl⟩
      exact ⟨eK ⟨k,hk⟩,(heK ⟨k,hk⟩).symm⟩
    · rintro _ ⟨p,rfl⟩
      obtain ⟨k,rfl⟩ := eK.surjective p
      exact ⟨k,k.property,heK k⟩
  obtain ⟨p,hp⟩ := exists_conjugating_pair_inr (H.map e0.toMonoidHom)
    (hVm ▸ map_mono hVH) ((card_map_of_injective e0.injective).trans hH)
  refine ⟨e0.trans (MulAut.conj (SemidirectProduct.inr p)),?_,?_,?_⟩
  · change H.map ((MulAut.conj (SemidirectProduct.inr p)).toMonoidHom.comp e0.toMonoidHom) = _
    rw [←map_map,hp]
  · change V.map ((MulAut.conj (SemidirectProduct.inr p)).toMonoidHom.comp e0.toMonoidHom) = _
    rw [←map_map,hVm]
    exact Subgroup.Normal.map_conj_eq _ _
  · change K.map ((MulAut.conj (SemidirectProduct.inr p)).toMonoidHom.comp e0.toMonoidHom) = _
    rw [←map_map,hKm,inr_conj_range]

end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
