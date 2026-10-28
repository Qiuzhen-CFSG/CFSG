module

public import CFSG.Quasithin.ChapterK.Defs
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# The actual cubic actor in the exceptional-family reduction

An injective group map and an intertwining linear equivalence preserve the
third displacement, the actor rank and the fixed-space codimension. In
particular the original ambient group embeds in the linear normalizer of
its normal component's action. This transfers the cubic bound without any
SQTK assertion about that full normalizer.

Source: Aschbacher--Smith, Chapter K, printed pp.451--452 and 457;
Guralnick--Malle, Classification of 2F-modules II, Theorem 8.1/Table 17.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional
open Representation Representation.BinaryOffender

variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Transport the literal triple displacement, retaining the actor image. -/
theorem cubic_map_equivariant
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup G} (hA : IsCubic ρ A) : IsCubic σ (A.map f) := by
  have hd (g : G) (v : V) : E (displacement ρ g v) =
      displacement σ (f g) (E v) := by
    simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hE]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ w
  obtain ⟨v, rfl⟩ := E.surjective w
  rw [← hd, ← hd, ← hd, hA a ha b hb c hc v, map_zero]

/-- An injective equivariant map preserves a cubic actor of ratio at most n. -/
theorem cubic_actor_map_equivariant
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup G} {n : ℕ} (hA : IsElementaryTwo A)
    (hc : IsCubic ρ A) (hb : fixedCodim ρ A ≤ n * rank A) :
    IsElementaryTwo (A.map f) ∧ IsCubic σ (A.map f) ∧
      fixedCodim σ (A.map f) ≤ n * rank (A.map f) := by
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨⟨?_, IsElementaryAbelian.map f⟩,
    cubic_map_equivariant ρ σ f E hE hc, ?_⟩
  · intro hbot
    exact hA.1 (Subgroup.map_injective hf (by simpa using hbot))
  · rwa [← fixedCodim_map_equivariant ρ σ f E hE, rank_map_injective f hf]

/-- The cubic bound passes to an overgroup through its actual action map. -/
theorem cubicRatio_le_nat_of_equivariant [Finite G] [Finite D]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (n : ℕ) (h : cubicRatio ρ ≤ n) : cubicRatio σ ≤ n := by
  obtain ⟨A, hA, hc, hb⟩ := (cubicRatio_le_nat_iff ρ n).mp h
  exact (cubicRatio_le_nat_iff σ n).mpr
    ⟨A.map f, cubic_actor_map_equivariant ρ σ f hf E hE hA hc hb⟩

/-- Source application: the original cubic bound holds on the full linear
normalizer of the actual normal component action. Only the original group
is assumed faithful; no structural hypothesis is imposed on the normalizer. -/
theorem cubicRatio_normalizer_le_two [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2) :
    cubicRatio (normalizerRepresentation (ρ.comp L.subtype)) ≤ 2 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let f : G →* linearNormalizer (ρ.comp L.subtype) :=
    (Subgroup.inclusion (actionImage_le_linearNormalizer ρ L)).comp (actionHom ρ)
  have hinj : Function.Injective f := by
    intro x y h
    apply hf
    exact congrArg (fun z : linearNormalizer (ρ.comp L.subtype) => z.val.val) h
  exact cubicRatio_le_nat_of_equivariant ρ _ f hinj
    (LinearEquiv.refl _ _) (fun _ _ => rfl) 2 hc

/-- Replacing the component by its actual group model does not change the
normalizer. This is the literal model action consumed by GM04. -/
theorem cubicRatio_model_normalizer_le_two [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (e : D ≃* L) (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2) :
    cubicRatio (normalizerRepresentation ((ρ.comp L.subtype).comp e.toMonoidHom)) ≤ 2 := by
  have he : actionImage ((ρ.comp L.subtype).comp e.toMonoidHom) =
      actionImage (ρ.comp L.subtype) := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨e d, Units.ext rfl⟩
    · rintro ⟨l, rfl⟩
      refine ⟨e.symm l, Units.ext ?_⟩
      change ρ ((e (e.symm l) : L) : G) = ρ l
      rw [e.apply_symm_apply]
  have h := cubicRatio_normalizer_le_two ρ L hf hc
  unfold normalizerRepresentation linearNormalizer at h ⊢
  rwa [he]

end CFSG.Quasithin.ChapterK.Exceptional
