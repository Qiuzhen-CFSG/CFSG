module
public import Theory.SpecificGroups.Janko3.SourceRecognition.SingerFieldAffineExtension.Centralizer

/-!
# Extend a complement-preserving field-point marking to the full affine group

The translation group is the characteristic two-core. Its original action
and the preserved order-thirty complement yield exact root/actor coordinates
for the point-group automorphism. The root action normalizes the center of
the actor, hence its full F₄-linear centralizer. This constructs an automorphism
of the entire affine group extending the original marking pointwise and
preserving the full order-180 complement.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.SingerField.AffineExtension
open Subgroup
open BaumeisterParabolics
open Representation.CentralCubicNaturalFour

private theorem invariant_coordinates {A E : Type*} [Group A] [Group E]
    (i : A →* E) (hi : Function.Injective i) (φ : MulAut E)
    (h : i.range.map φ.toMonoidHom = i.range) :
    ∃ a : MulAut A, ∀ x, φ (i x) = i (a x) := by
  let e := MonoidHom.ofInjective hi
  let a := e.trans ((φ.subgroupMap i.range).trans ((MulEquiv.subgroupCongr h).trans e.symm))
  refine ⟨a,?_⟩
  intro x
  exact (MonoidHom.apply_ofInjective_symm hi
    ((MulEquiv.subgroupCongr h) ((φ.subgroupMap i.range) (e x)))).symm

private theorem centralizer_map (Q : Subgroup (MulAut (Multiplicative K)))
    (e : MulAut (MulAut (Multiplicative K))) :
    (centralizer (Q : Set _)).map e.toMonoidHom = centralizer (Q.map e.toMonoidHom : Set _) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro q hq
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e q) (mem_map_of_mem _ hq)

private theorem actor_extension (a : MulAut (Multiplicative K))
    (b : MulAut SingerField.normalizer)
    (hab : ∀ d x, a (action d x) = action (b d) (a x)) :
    ∃ σ : MulAut (K ≃ₗ[F] K),
      (∀ l x, a (linearAction l x) = linearAction (σ l) (a x)) ∧
      ∀ d : SingerField.normalizer, σ d = (b d : K ≃ₗ[F] K) := by
  let q := MulAut.conj a
  have hconj (d : SingerField.normalizer) : q (action d) = action (b d) := by
    apply MulEquiv.ext
    intro x
    change a (action d (a.symm x)) = action (b d) x
    rw [hab,a.apply_symm_apply]
  let Z := (center SingerField.normalizer).map action
  have hZ : Z.map q.toMonoidHom = Z := by
    apply le_antisymm
    · rintro _ ⟨_,⟨d,hd,rfl⟩,rfl⟩
      exact ⟨b d,(centerCongr b ⟨d,hd⟩).property,(hconj d).symm⟩
    · rintro _ ⟨d,hd,rfl⟩
      refine ⟨action (b.symm d),⟨b.symm d,(centerCongr b.symm ⟨d,hd⟩).property,rfl⟩,?_⟩
      change q (action (b.symm d)) = action d
      rw [hconj,b.apply_symm_apply]
  have hL : linearAction.range.map q.toMonoidHom = linearAction.range := by
    rw [range_eq_center_centralizer,centralizer_map,hZ]
  obtain ⟨σ,hσ⟩ := invariant_coordinates linearAction linearAction_injective q hL
  refine ⟨σ,?_,?_⟩
  · intro l x
    have hh := congrArg (fun e : MulAut (Multiplicative K) => e (a x)) (hσ l)
    change a (linearAction l (a.symm (a x))) = linearAction (σ l) (a x) at hh
    rwa [a.symm_apply_apply] at hh
  · intro d
    apply linearAction_injective
    exact (hσ d).symm.trans (hconj d)

private abbrev Full := Multiplicative K ⋊[linearAction] (K ≃ₗ[F] K)
private def embed : Model →* Full :=
  SemidirectProduct.map (MonoidHom.id _) SingerField.normalizer.subtype (fun _ => rfl)
private def fullCoordinates : Full ≃* Plane ⋊[naturalAction] LinearGroup :=
  SemidirectProduct.congr rootCoordinates matrixEquiv (by
    intro l
    apply MulEquiv.ext
    intro x
    change rootCoordinates (Multiplicative.ofAdd (l x.toAdd)) =
      naturalAction (matrixEquiv l) (rootCoordinates x)
    change Multiplicative.ofAdd (coordinates (l x.toAdd)) = _
    change Multiplicative.ofAdd (coordinates (l x.toAdd)) =
      Multiplicative.ofAdd (Representation.SL2FourNatural.SemilinearNormalizer.glEquiv
        (matrixEquiv l) (coordinates x.toAdd))
    rw [matrixEquiv,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
    change _ = Multiplicative.ofAdd (coordinates (l (coordinates.symm (coordinates x.toAdd))))
    rw [coordinates.symm_apply_apply])

/-- Every automorphism of the actual field-point group preserving its
order-thirty complement extends to the full affine group, with pointwise
agreement on the same field embedding and the full linear complement retained. -/
theorem point_automorphism_extends (φ : MulAut Model)
    (hc : pointComplement.map φ.toMonoidHom = pointComplement) :
    ∃ Φ : MulAut (Plane ⋊[naturalAction] LinearGroup),
      (∀ x : Model, Φ (affineEmbedding x) = affineEmbedding (φ x)) ∧
      (SemidirectProduct.inr : LinearGroup →* Plane ⋊[naturalAction] LinearGroup).range.map
        Φ.toMonoidHom =
        (SemidirectProduct.inr : LinearGroup →* Plane ⋊[naturalAction] LinearGroup).range := by
  have hr : root.range.map φ.toMonoidHom = root.range := by
    rw [←point_core,pCore_map_iso]
  obtain ⟨a,ha⟩ := invariant_coordinates root SemidirectProduct.inl_injective φ hr
  change ∀ x, φ (SemidirectProduct.inl x) = SemidirectProduct.inl (a x) at ha
  obtain ⟨b,hb⟩ := invariant_coordinates
    (SemidirectProduct.inr : SingerField.normalizer →* Model) SemidirectProduct.inr_injective φ hc
  have hab (d : SingerField.normalizer) (x : Multiplicative K) :
      a (action d x) = action (b d) (a x) := by
    apply (SemidirectProduct.inl_injective (φ := action))
    have hh := congrArg φ (SemidirectProduct.inl_aut d x)
    simp only [map_mul,map_inv,ha,hb] at hh
    rw [←map_inv,←SemidirectProduct.inl_aut] at hh
    exact hh
  obtain ⟨σ,hσ,hσb⟩ := actor_extension a b hab
  let Ψ : MulAut Full := SemidirectProduct.congr a σ (by
    intro l
    apply MulEquiv.ext
    intro x
    exact hσ l x)
  have hsmall (x : Model) : Ψ (embed x) = embed (φ x) := by
    have hx : φ x = ⟨a x.left,b x.right⟩ := by
      nth_rw 1 [←SemidirectProduct.inl_left_mul_inr_right x]
      rw [map_mul,ha,hb]
      exact (SemidirectProduct.mk_eq_inl_mul_inr _ _).symm
    rw [hx]
    apply SemidirectProduct.ext
    · rfl
    · exact hσb x.right
  let Φ := (MulAut.congr fullCoordinates) Ψ
  have hcoord (x : Model) : fullCoordinates (embed x) = affineEmbedding x := rfl
  have hinr (l : K ≃ₗ[F] K) : fullCoordinates (SemidirectProduct.inr l) =
      SemidirectProduct.inr (matrixEquiv l) := by
    apply SemidirectProduct.ext
    · exact map_one rootCoordinates
    · rfl
  refine ⟨Φ,?_,?_⟩
  · intro x
    change fullCoordinates (Ψ (fullCoordinates.symm (affineEmbedding x))) = _
    rw [←hcoord,fullCoordinates.symm_apply_apply,hsmall,hcoord]
  · have him (l : LinearGroup) : Φ (SemidirectProduct.inr l) =
        SemidirectProduct.inr (matrixEquiv (σ (matrixEquiv.symm l))) := by
      change fullCoordinates (Ψ (fullCoordinates.symm (SemidirectProduct.inr l))) = _
      rw [←show fullCoordinates (SemidirectProduct.inr (matrixEquiv.symm l)) =
        SemidirectProduct.inr l by rw [hinr,matrixEquiv.apply_symm_apply],
        fullCoordinates.symm_apply_apply]
      have he : Ψ (SemidirectProduct.inr (matrixEquiv.symm l)) =
          SemidirectProduct.inr (σ (matrixEquiv.symm l)) := by
        apply SemidirectProduct.ext
        · exact map_one a
        · rfl
      rw [he,hinr]
    apply le_antisymm
    · rintro _ ⟨_,⟨l,rfl⟩,rfl⟩
      exact ⟨_,(him l).symm⟩
    · rintro _ ⟨l,rfl⟩
      refine ⟨SemidirectProduct.inr (matrixEquiv (σ.symm (matrixEquiv.symm l))),⟨_,rfl⟩,?_⟩
      change Φ (SemidirectProduct.inr _) = _
      rw [him,matrixEquiv.symm_apply_apply,σ.apply_symm_apply,matrixEquiv.apply_symm_apply]
end Sporadic.Janko3.SourceRecognition.SingerField.AffineExtension
