module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoverNormalizer

/-!
# The full-normalizer action on the literal block-module model

The intrinsic quotient projection U→U/C_U(K) is transported through the
specified BlockModuleModel. Its whole K-action is the model actor, so
faithfulness identifies its internal kernel with O₂(K). Applying the
central-cover normalizer theorem gives the full N_G(K)-action, with kernel
C_N(U), on that same literal model quotient.

Source: Aschbacher–Smith, C.1.12 and C.5.6(7), printed pp.124,159–160.
-/
@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G W A : Type*} [Group G] [Group W] [Group A] {K : Subgroup G}
variable {τ : A →* MulAut W}

noncomputable def modelActor (m : BlockModuleModel K τ) : K →* A :=
  m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))

noncomputable def intrinsicEquiv (K : Subgroup G) : blockU K ≃* U K :=
  (blockU K).equivMapOfInjective K.subtype K.subtype_injective

noncomputable def modelProjection (m : BlockModuleModel K τ) : U K →* W :=
  m.moduleIso.toMonoidHom.comp ((QuotientGroup.mk' (blockFixed K)).comp
    (intrinsicEquiv K).symm.toMonoidHom)

theorem modelProjection_intrinsic (m : BlockModuleModel K τ) (v : blockU K) :
    modelProjection m (intrinsicEquiv K v) = m.moduleIso (QuotientGroup.mk' (blockFixed K) v) := by
  simp [modelProjection]

theorem modelProjection_surjective (m : BlockModuleModel K τ) : Function.Surjective (modelProjection m) :=
  m.moduleIso.surjective.comp ((QuotientGroup.mk'_surjective _).comp (intrinsicEquiv K).symm.surjective)

theorem modelProjection_kernel (m : BlockModuleModel K τ) (v : U K) :
    modelProjection m v = 1 ↔ (v : G) ∈ centralizer (K : Set G) := by
  obtain ⟨w,rfl⟩ := (intrinsicEquiv K).surjective v
  rw [modelProjection_intrinsic,m.moduleIso.map_eq_one_iff]
  change w ∈ (QuotientGroup.mk' (blockFixed K)).ker ↔ _
  rw [QuotientGroup.ker_mk']
  change (w : K) ∈ center K ↔ (∀ y ∈ K, y * ((w : K) : G) = ((w : K) : G) * y)
  rw [mem_center_iff]
  constructor
  · intro hh y hy
    exact congrArg Subtype.val (hh ⟨y,hy⟩)
  · intro hh y
    exact Subtype.ext (hh y y.property)

theorem modelProjection_conjugate (m : BlockModuleModel K τ) (k : K) (v : U K) :
    modelProjection m (normalizerConjugate (inclusion K.le_normalizer k) v) =
      τ (modelActor m k) (modelProjection m v) := by
  obtain ⟨w,rfl⟩ := (intrinsicEquiv K).surjective v
  have he : normalizerConjugate (inclusion K.le_normalizer k) (intrinsicEquiv K w) =
      intrinsicEquiv K (blockConjugate K k w) := by apply Subtype.ext; rfl
  rw [he,modelProjection_intrinsic,modelProjection_intrinsic]
  exact m.intertwining k w

variable [Finite G]

omit [Finite G] in
/-- The internal action kernel is the actual two-core, proved from the
specified faithful block-module action. -/
theorem modelProjection_internal_kernel (m : BlockModuleModel K τ) (hτ : Function.Injective τ)
    (k : K) (hk : ∀ u : U K,
      modelProjection m (normalizerConjugate (inclusion K.le_normalizer k) u) = modelProjection m u) :
    k ∈ pCore 2 K := by
  have he : τ (modelActor m k) = 1 := by
    ext w
    obtain ⟨u,rfl⟩ := modelProjection_surjective m w
    exact (modelProjection_conjugate m k u).symm.trans (hk u)
  have he' : modelActor m k = 1 := hτ (he.trans (map_one τ).symm)
  have hq : QuotientGroup.mk' (pCore 2 K) k = 1 := m.quotientIso.map_eq_one_iff.mp he'
  exact (QuotientGroup.eq_one_iff k).mp hq

/-- The whole block normalizer acts on the literal model quotient and has
the full U-centralizer as kernel; its original K-image is exactly τ(A). -/
theorem exists_full_model_action (hshort : IsShort K) (m : BlockModuleModel K τ)
    (hτ : Function.Injective τ) :
    ∃ ρ : normalizer (K : Set G) →* MulAut W,
      (∀ a u, ρ a (modelProjection m u) = modelProjection m (normalizerConjugate a u)) ∧
      ρ.ker = (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G)) ∧
      (K.subgroupOf (normalizer (K : Set G))).map ρ = τ.range := by
  obtain ⟨ρ,hρ⟩ := exists_normalizer_quotient_action (modelProjection m)
    (modelProjection_surjective m) (modelProjection_kernel m)
  refine ⟨ρ,hρ,normalizer_quotient_action_kernel hshort (modelProjection m)
    (modelProjection_surjective m) (modelProjection_kernel m) (modelProjection_internal_kernel m hτ) ρ hρ,?_⟩
  have hi (k : K) : ρ (inclusion K.le_normalizer k) = τ (modelActor m k) := by
    ext w
    obtain ⟨u,rfl⟩ := modelProjection_surjective m w
    rw [hρ,modelProjection_conjugate]
  apply le_antisymm
  · rintro _ ⟨k,hk,rfl⟩
    let k' : K := ⟨k,hk⟩
    have he : inclusion K.le_normalizer k' = k := Subtype.ext rfl
    rw [← he,hi]
    exact ⟨modelActor m k',rfl⟩
  · rintro _ ⟨a,rfl⟩
    obtain ⟨k,rfl⟩ := (m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)) a
    exact ⟨inclusion K.le_normalizer k,k.property,hi k⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
