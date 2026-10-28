module
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneTransport

/-!
# Pointwise compatibility of the original field and plane markings

The natural plane coordinates and its chosen complement determine the entire
field-affine embedding. Scalars and fourth-power Frobenius generate the linear
part, and the faithful natural action determines their images in the complement.
Consequently the actual affine normalizer isomorphism carries the same original
field embedding pointwise to the fixed field model, including the full overlap.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
namespace Sporadic.Janko3.SourceRecognition.PlaneTransport
variable {G : Type*} [Group G]

private theorem naturalAction_injective : Function.Injective naturalAction := by
  intro g h he
  apply Representation.SL2FourNatural.SemilinearNormalizer.glEquiv.injective
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd
    (congrArg (fun a : MulAut Plane => a (Multiplicative.ofAdd v)) he)

private theorem inr_image_mem (H : Subgroup G) (j : Model →* G)
    (hs : ∀ u : Kˣ, j (scalar u) ∈ H) (hf : j fieldElement ∈ H)
    (b : SingerField.normalizer) : j (SemidirectProduct.inr b) ∈ H := by
  have hprod : (b : K ≃ₗ[Representation.SL2FourNatural.F] K) ∈
      (torus : Set (K ≃ₗ[Representation.SL2FourNatural.F] K)) *
      (zpowers SingerField.frobenius : Set (K ≃ₗ[Representation.SL2FourNatural.F] K)) := by
    rw [← coe_mul_of_right_le_normalizer_left torus (zpowers SingerField.frobenius)
      (zpowers_le.mpr frobenius_normalizes)]
    exact b.property
  obtain ⟨t, ⟨u, rfl⟩, z, hz, he⟩ := hprod
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
  have hb : (SemidirectProduct.inr b : Model) = scalar u * fieldElement ^ n := by
    change SemidirectProduct.inr b = SemidirectProduct.inr _ *
      (SemidirectProduct.inr _) ^ n
    rw [← map_zpow, ← map_mul]
    exact congrArg SemidirectProduct.inr (Subtype.ext he.symm)
  rw [hb, map_mul, map_zpow]
  exact H.mul_mem (hs u) (H.zpow_mem hf n)

private theorem hom_eq_of_root_complement
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j k : Model →* G)
    (hj : ∀ x : Multiplicative K, j (root x) = (a.symm (rootCoordinates x) : G))
    (hk : ∀ x : Multiplicative K, k (root x) = (a.symm (rootCoordinates x) : G))
    (hjs : ∀ u : Kˣ, j (scalar u) ∈ C.map (normalizer (A : Set G)).subtype)
    (hjf : j fieldElement ∈ C.map (normalizer (A : Set G)).subtype)
    (hks : ∀ u : Kˣ, k (scalar u) ∈ C.map (normalizer (A : Set G)).subtype)
    (hkf : k fieldElement ∈ C.map (normalizer (A : Set G)).subtype) : j = k := by
  have hr (x : Multiplicative K) : j (root x) = k (root x) := (hj x).trans (hk x).symm
  apply SemidirectProduct.hom_ext
  · exact MonoidHom.ext hr
  · apply MonoidHom.ext
    intro b
    obtain ⟨c, hc, hcj⟩ := inr_image_mem _ j hjs hjf b
    obtain ⟨d, hd, hdk⟩ := inr_image_mem _ k hks hkf b
    change (c : G) = j (SemidirectProduct.inr b) at hcj
    change (d : G) = k (SemidirectProduct.inr b) at hdk
    have hcd : (⟨c,hc⟩ : C) = ⟨d,hd⟩ := by
      apply l.injective
      apply naturalAction_injective
      apply MulEquiv.ext
      intro v
      obtain ⟨x,rfl⟩ := a.surjective v
      rw [← ha, ← ha]
      apply congrArg a
      apply Subtype.ext
      obtain ⟨u,hu⟩ := rootCoordinates.surjective (a x)
      have hju : j (root u) = (x : G) := by rw [hj,hu,a.symm_apply_apply]
      have hku : k (root u) = (x : G) := by rw [hk,hu,a.symm_apply_apply]
      have hrel := (SemidirectProduct.inl_aut (φ := action) b u).symm
      have hjrel := congrArg j hrel
      have hkrel := congrArg k hrel
      simp only [map_mul, map_inv] at hjrel hkrel
      change j (SemidirectProduct.inr b) * j (root u) *
        (j (SemidirectProduct.inr b))⁻¹ = j (root ((action b) u)) at hjrel
      change k (SemidirectProduct.inr b) * k (root u) *
        (k (SemidirectProduct.inr b))⁻¹ = k (root ((action b) u)) at hkrel
      rw [←hcj,hju] at hjrel
      rw [←hdk,hku] at hkrel
      change (c : G) * (x : G) * (c : G)⁻¹ = (d : G) * (x : G) * (d : G)⁻¹
      exact hjrel.trans ((hr _).trans hkrel.symm)
    exact hcj.symm.trans ((congrArg (fun z : C => ((z : normalizer (A : Set G)) : G)) hcd).trans hdk)

/-- The original plane coordinates and complement determine the literal full
field embedding, without a choice of ambient recognition or presentation. -/
theorem fieldEmbedding_unique
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j k : Model →* G) (hj : FieldEmbedding A C a j) (hk : FieldEmbedding A C a k) : j = k :=
  hom_eq_of_root_complement A C l a ha j k hj.2.2.2.1 hk.2.2.2.1
    hj.2.2.2.2.1 hj.2.2.2.2.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2.1

/-- One affine normalizer marking preserves the original plane, the full chosen
complement, and every element of the same original field-affine subgroup. -/
theorem affine_equiv_preserving_fieldEmbedding
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : Model →* G) (hj : FieldEmbedding A C a j) :
    ∃ e : normalizer (A : Set G) ≃* Plane ⋊[naturalAction] LinearGroup,
      (∀ x : A, e (inclusion le_normalizer x) = SemidirectProduct.inl (a x)) ∧
      (∀ c : C, e c = SemidirectProduct.inr (l c)) ∧
      ∀ x : Model, e ⟨j x, hj.2.1 ⟨x,rfl⟩⟩ = affineEmbedding x := by
  obtain ⟨e,he,hc⟩ := affine_equiv_of_complement A C l a hC ha
  let k := (normalizer (A : Set G)).subtype.comp (e.symm.toMonoidHom.comp affineEmbedding)
  have hkr (b : LinearGroup) :
      ((e.symm (SemidirectProduct.inr b) : normalizer (A : Set G)) : G) ∈
        C.map (normalizer (A : Set G)).subtype := by
    have hh := hc (l.symm b)
    rw [l.apply_symm_apply] at hh
    rw [←hh,e.symm_apply_apply]
    exact ⟨l.symm b,(l.symm b).property,rfl⟩
  have hkroot (x : Multiplicative K) : k (root x) = (a.symm (rootCoordinates x) : G) := by
    change ((e.symm (affineEmbedding (root x)) : normalizer (A : Set G)) : G) = _
    have hh := he (a.symm (rootCoordinates x))
    rw [a.apply_symm_apply] at hh
    rw [affineEmbedding_root,←hh,e.symm_apply_apply]
    rfl
  have hks (u : Kˣ) : k (scalar u) ∈ C.map (normalizer (A : Set G)).subtype := by
    change ((e.symm (affineEmbedding (scalar u)) : normalizer (A : Set G)) : G) ∈ _
    rw [scalar,MonoidHom.comp_apply,affineEmbedding,SemidirectProduct.map_inr]
    exact hkr _
  have hkf : k fieldElement ∈ C.map (normalizer (A : Set G)).subtype := by
    change ((e.symm (affineEmbedding fieldElement) : normalizer (A : Set G)) : G) ∈ _
    rw [fieldElement,affineEmbedding,SemidirectProduct.map_inr]
    exact hkr _
  have hjk := hom_eq_of_root_complement A C l a ha j k
    hj.2.2.2.1 hkroot hj.2.2.2.2.1 hj.2.2.2.2.2.1 hks hkf
  refine ⟨e,he,hc,?_⟩
  intro x
  have hx : (⟨j x,hj.2.1 ⟨x,rfl⟩⟩ : normalizer (A : Set G)) = e.symm (affineEmbedding x) :=
    Subtype.ext (DFunLike.congr_fun hjk x)
  rw [hx,e.apply_symm_apply]

/-- The full affine model embeds in the original group and extends the same
field-affine embedding pointwise. This retains the entire G₁–G₂ overlap. -/
theorem affine_embedding_extending_fieldEmbedding
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : Model →* G) (hj : FieldEmbedding A C a j) :
    ∃ k : Plane ⋊[naturalAction] LinearGroup →* G,
      Function.Injective k ∧ k.range = normalizer (A : Set G) ∧
      k.comp affineEmbedding = j ∧
      (∀ x : Plane, k (SemidirectProduct.inl x) = (a.symm x : G)) ∧
      ∀ c : C, k (SemidirectProduct.inr (l c)) = ((c : normalizer (A : Set G)) : G) := by
  obtain ⟨e,he,hc,hj⟩ := affine_equiv_preserving_fieldEmbedding A C l a hC ha j hj
  let k := (normalizer (A : Set G)).subtype.comp e.symm.toMonoidHom
  refine ⟨k,Subtype.val_injective.comp e.symm.injective,?_,?_,?_,?_⟩
  · apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      exact (e.symm x).property
    · intro x hx
      refine ⟨e ⟨x,hx⟩,?_⟩
      change ((e.symm (e ⟨x,hx⟩) : normalizer (A : Set G)) : G) = x
      rw [e.symm_apply_apply]
  · apply MonoidHom.ext
    intro x
    have hh := congrArg e.symm (hj x)
    rw [e.symm_apply_apply] at hh
    exact (congrArg (fun z : normalizer (A : Set G) => (z : G)) hh).symm
  · intro x
    have hh := he (a.symm x)
    rw [a.apply_symm_apply] at hh
    change ((e.symm (SemidirectProduct.inl x) : normalizer (A : Set G)) : G) = _
    rw [←hh,e.symm_apply_apply]
    rfl
  · intro c
    change ((e.symm (SemidirectProduct.inr (l c)) : normalizer (A : Set G)) : G) = _
    rw [←hc c,e.symm_apply_apply]

end Sporadic.Janko3.SourceRecognition.PlaneTransport
