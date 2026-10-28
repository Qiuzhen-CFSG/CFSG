module
public import Theory.GroupAction.FixedQuotientCentralizer
public import Theory.PGroupCore

/-!
# Quotient-action models under faithful ambient embeddings

An injective homomorphism identifies each subgroup with its literal image.
Transport both the acting subgroup K and the module subgroup U along these
identifications. Injectivity identifies the centralizer kernel, and conjugation
compatibility preserves the specified representation action. The new actor
is explicitly the old actor composed with the inverse subgroup-image map.

Surjectivity and an intrinsic two-core actor kernel are preserved. The source
application returns the MS model from K restricted to KT to the original K.
-/

public section
open Subgroup
namespace Representation.ConjugationQuotientModel
variable {G H A V : Type*} [Group G] [Group H] [Group A]
  [AddCommGroup V] [Module (ZMod 2) V]
  {K U : Subgroup G} {ρ : Representation (ZMod 2) A V}

private theorem map_normalizes (m : ConjugationQuotientModel K U ρ)
    (f : G →* H) : K.map f ≤ normalizer (U.map f : Set H) :=
  (map_mono m.normalizes).trans (le_normalizer_map f)

private theorem inverse_map_conjugate (m : ConjugationQuotientModel K U ρ)
    (f : G →* H) (hf : Function.Injective f) (k : K.map f) (u : U.map f) :
    (U.equivMapOfInjective f hf).symm
        ((U.map f).normalizerMonoidHom ⟨k, map_normalizes m f k.property⟩ u) =
      U.normalizerMonoidHom
        ⟨(K.equivMapOfInjective f hf).symm k,
          m.normalizes ((K.equivMapOfInjective f hf).symm k).property⟩
        ((U.equivMapOfInjective f hf).symm u) := by
  apply (U.equivMapOfInjective f hf).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  have hk := congrArg Subtype.val ((K.equivMapOfInjective f hf).apply_symm_apply k)
  have hu := congrArg Subtype.val ((U.equivMapOfInjective f hf).apply_symm_apply u)
  change f ((K.equivMapOfInjective f hf).symm k : G) = (k : H) at hk
  change f ((U.equivMapOfInjective f hf).symm u : G) = (u : H) at hu
  change (k : H) * (u : H) * (k : H)⁻¹ =
    f (((K.equivMapOfInjective f hf).symm k : G) *
      ((U.equivMapOfInjective f hf).symm u : G) *
        ((K.equivMapOfInjective f hf).symm k : G)⁻¹)
  rw [map_mul, map_mul, map_inv, hk, hu]

/-- An injective ambient homomorphism transports the literal quotient model. -/
noncomputable def mapInjective (m : ConjugationQuotientModel K U ρ)
    (f : G →* H) (hf : Function.Injective f) :
    ConjugationQuotientModel (K.map f) (U.map f) ρ where
  normalizes := by exact map_normalizes m f
  actor := m.actor.comp (K.equivMapOfInjective f hf).symm.toMonoidHom
  quotient := m.quotient.comp (U.equivMapOfInjective f hf).symm.toMonoidHom
  surjective := m.surjective.comp (U.equivMapOfInjective f hf).symm.surjective
  kernel := by
    ext u
    change m.quotient ((U.equivMapOfInjective f hf).symm u) = 1 ↔ _
    change (U.equivMapOfInjective f hf).symm u ∈ m.quotient.ker ↔ _
    rw [m.kernel]
    change (∀ k ∈ K, k * ((U.equivMapOfInjective f hf).symm u : G) =
      ((U.equivMapOfInjective f hf).symm u : G) * k) ↔
      ∀ k ∈ K.map f, k * (u : H) = (u : H) * k
    have hu := congrArg Subtype.val ((U.equivMapOfInjective f hf).apply_symm_apply u)
    change f ((U.equivMapOfInjective f hf).symm u : G) = (u : H) at hu
    constructor
    · intro hc k hk
      obtain ⟨a, ha, rfl⟩ := hk
      simpa only [map_mul, hu] using congrArg f (hc a ha)
    · intro hc k hk
      apply hf
      simpa only [map_mul, hu] using hc (f k) (mem_map_of_mem f hk)
  equivariant := by
    intro k u
    change m.quotient ((U.equivMapOfInjective f hf).symm
      ((U.map f).normalizerMonoidHom ⟨k, map_normalizes m f k.property⟩ u)) = _
    rw [inverse_map_conjugate m f hf k u]
    exact m.equivariant ((K.equivMapOfInjective f hf).symm k)
      ((U.equivMapOfInjective f hf).symm u)

/-- The actor retains the inverse of the literal subgroup-image equivalence. -/
theorem mapInjective_actor (m : ConjugationQuotientModel K U ρ)
    (f : G →* H) (hf : Function.Injective f) :
    (m.mapInjective f hf).actor =
      m.actor.comp (K.equivMapOfInjective f hf).symm.toMonoidHom := by rfl

theorem mapInjective_actor_surjective (m : ConjugationQuotientModel K U ρ)
    (f : G →* H) (hf : Function.Injective f) (ha : Function.Surjective m.actor) :
    Function.Surjective (m.mapInjective f hf).actor :=
  ha.comp (K.equivMapOfInjective f hf).symm.surjective

theorem mapInjective_actor_kernel (m : ConjugationQuotientModel K U ρ)
    (f : G →* H) (hf : Function.Injective f) :
    (m.mapInjective f hf).actor.ker = m.actor.ker.map (K.equivMapOfInjective f hf).toMonoidHom := by
  ext k
  rw [mem_map_equiv]
  rfl

theorem mapInjective_actor_kernel_pCore (m : ConjugationQuotientModel K U ρ)
    (f : G →* H) (hf : Function.Injective f) (hk : m.actor.ker = pCore 2 K) :
    (m.mapInjective f hf).actor.ker = pCore 2 (K.map f) := by
  rw [mapInjective_actor_kernel, hk, pCore_map_iso]
end Representation.ConjugationQuotientModel
