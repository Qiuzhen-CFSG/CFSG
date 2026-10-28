module

public import Theory.SpecificGroups.PSL3Four.CentralCover.EmbeddedPlane

/-!
# The original quotient of a full elementary-plane normalizer

The lifted affine projection gives the actual SL₂(4) quotient by the full
two-core, before and after the original ambient subgroup embedding.
-/

namespace Matrix.PSL3Four.FullPlaneNormalizer
open Subgroup ElementaryParabolic Theory.GroupTheory
open scoped MatrixGroups
variable {E : Type*} [Group E] [Finite E]

public theorem full_plane_quotient
    (f : E →* PSL) (hf : Function.Surjective f) (hk : Nat.card f.ker=4)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hkQ : f.ker≤Q) (hQ : Nat.card Q=64) :
    let N := normalizer (Q : Set E)
    Nonempty ((N ⧸ pCore 2 N) ≃* SL(2,F)) := by
  obtain ⟨g,b,hN⟩ := full_plane_normalizer_alignment f hf Q hkQ (by rw [hk,hQ])
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker=f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  change Nonempty (((normalizer (Q : Set E)) ⧸ pCore 2 (normalizer (Q : Set E))) ≃* SL(2,F))
  rw [hN]
  let P := liftedParabolic f' b
  let j := parabolicAffine f' b
  have hj : Function.Surjective j := parabolicAffine_surjective f' hf' b
  have hjk : IsPGroup 2 j.ker := by
    rw [parabolicAffine_ker]
    have hp : IsPGroup 2 f'.ker := IsPGroup.of_card (n := 2) (by rw [hker,hk]; decide)
    exact hp.comap_of_injective _ P.subtype_injective
  exact ⟨(j.pCoreQuotientEquiv hj hjk).trans (Matrix.SL2.affineCoreQuotientEquiv F)⟩

variable {G : Type*} [Group G] [Finite G]

public theorem embedded_plane_quotient
    (B W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : B →* PSL) (hf : Function.Surjective f) (hk : f.ker=center B)
    (hkc : Nat.card f.ker=4) (hWB : W≤B) (hZW : centerIn B≤W)
    (hWc : Nat.card W=64) :
    let L := (normalizer (W.subgroupOf B : Set B)).map B.subtype
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,F)) := by
  let Q := W.subgroupOf B
  let N := normalizer (Q : Set B)
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf hWB
  have hQc : Nat.card Q=64 := (Nat.card_congr (subgroupOfEquivOfLe hWB).toEquiv).trans hWc
  have hkQ : f.ker≤Q := by
    rw [hk]
    intro x hx
    exact hZW (by rw [centerIn_eq_map_center]; exact ⟨x,hx,rfl⟩)
  obtain ⟨e⟩ := full_plane_quotient f hf hkc Q hkQ hQc
  let j := (N.equivMapOfInjective B.subtype B.subtype_injective).toMonoidHom
  have hj : Function.Surjective j := (N.equivMapOfInjective B.subtype B.subtype_injective).surjective
  have hjk : IsPGroup 2 j.ker := by
    rw [j.ker_eq_bot (N.equivMapOfInjective B.subtype B.subtype_injective).injective]
    exact IsPGroup.of_bot
  exact ⟨(j.pCoreQuotientEquiv hj hjk).symm.trans e⟩

end Matrix.PSL3Four.FullPlaneNormalizer
