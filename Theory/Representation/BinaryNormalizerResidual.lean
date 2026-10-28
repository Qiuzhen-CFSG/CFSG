module
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
/-!
# Binary linear normalizer residuals under marked action equivalences

Conjugating invertible endomorphisms through the marked vector-space
isomorphism carries the actual action image and its full linear normalizer
to their counterparts. Restricting this conjugation to the normalizers
transports their two-residuals and hence the source residual-containment
bound. Self-normalizing model images give the bound immediately.

Source application: Aschbacher–Smith, 13.7.6, printed p.940, with the
actual action markings retained from the small-plane source alternatives.
-/

public section
namespace Representation.BinaryNormalizerResidual
open Subgroup BinaryOffender
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)
  (e : G ≃* H) (E : V ≃ₗ[ZMod 2] W)
  (hE : ∀ g v, E (ρ g v) = σ (e g) (E v))

@[expose] noncomputable def unitConj (E : V ≃ₗ[ZMod 2] W) :
    (Module.End (ZMod 2) V)ˣ ≃* (Module.End (ZMod 2) W)ˣ :=
  Units.mapEquiv E.conjRingEquiv.toMulEquiv

include hE in
theorem actionImage_map :
    (actionImage ρ).map (unitConj E).toMonoidHom = actionImage σ := by
  have hm (g : G) : unitConj E (ρ.asGroupHom g) = σ.asGroupHom (e g) := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    change E (ρ g (E.symm w)) = σ (e g) w
    rw [hE, E.apply_symm_apply]
  ext x
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, (hm g).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨ρ.asGroupHom (e.symm h), ⟨e.symm h, rfl⟩, by
      change unitConj E (ρ.asGroupHom (e.symm h)) = σ.asGroupHom h
      rw [hm, e.apply_symm_apply]⟩

include hE in
theorem normalizer_map :
    (linearNormalizer ρ).map (unitConj E).toMonoidHom = linearNormalizer σ := by
  rw [linearNormalizer, map_equiv_normalizer_eq, actionImage_map ρ σ e E hE]
  rfl

include hE in
theorem normalizer_eq_of_equiv (hn : linearNormalizer σ = actionImage σ) :
    linearNormalizer ρ = actionImage ρ := by
  apply map_injective (f := (unitConj E).toMonoidHom) (unitConj E).injective
  rw [normalizer_map ρ σ e E hE, actionImage_map ρ σ e E hE, hn]

theorem residual_le_of_normalizer_eq (hn : linearNormalizer ρ = actionImage ρ) :
    (pResidual 2 (linearNormalizer ρ)).map (linearNormalizer ρ).subtype ≤ actionImage ρ :=
  (map_subtype_le _).trans_eq hn

include hE in
theorem residual_le_of_equiv
    (hb : (pResidual 2 (linearNormalizer σ)).map (linearNormalizer σ).subtype ≤
      actionImage σ) :
    (pResidual 2 (linearNormalizer ρ)).map (linearNormalizer ρ).subtype ≤ actionImage ρ := by
  have hn (x : linearNormalizer ρ) : unitConj E x.val ∈ linearNormalizer σ := by
    rw [← normalizer_map ρ σ e E hE]
    exact mem_map_of_mem _ x.property
  let f : linearNormalizer ρ →* linearNormalizer σ :=
    ((unitConj E).toMonoidHom.comp (linearNormalizer ρ).subtype).codRestrict _ hn
  rintro x ⟨y, hy, rfl⟩
  have hh := hb (mem_map_of_mem (linearNormalizer σ).subtype
    (map_pResidual_le 2 f (mem_map_of_mem f hy)))
  have hm : unitConj E y.val ∈ (actionImage ρ).map (unitConj E).toMonoidHom := by
    rw [actionImage_map ρ σ e E hE]
    exact hh
  obtain ⟨z, hz, hzy⟩ := hm
  have he : z = y.val := (unitConj E).injective hzy
  change y.val ∈ actionImage ρ
  rwa [← he]
end Representation.BinaryNormalizerResidual
