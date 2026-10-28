module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Models
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Applying the full linear normalizer to the original actor

The normalizer output records an actual group equivalence, an intertwining
linear equivalence, and the image of the marked normal three-group. Its
application embeds the original acting group in the full orthogonal carrier
and proves that its image contains the full orthogonal three-core.

This module proves the transport, not the existence of the normalizer model.
The latter is the elementary-nine normalizer calculation used in G.9.4 on
printed p.355 (PDF p.366).
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
universe u v
variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal image of the marked subgroup in the unit group of endomorphisms. -/
abbrev linearImage (ρ : Representation (ZMod 2) G V) (B : Subgroup G) :=
  B.map ρ.asGroupHom

/-- The full linear normalizer, not the normalizer inside the acting group. -/
abbrev linearNormalizer (ρ : Representation (ZMod 2) G V) (B : Subgroup G) :=
  Subgroup.normalizer (linearImage ρ B : Set (Module.End (ZMod 2) V)ˣ)

/-- The full normalizer calculation for an order-nine subgroup, retaining
both the natural action and the marked three-core. This is an output contract. -/
structure OrthogonalNormalizerModel (ρ : Representation (ZMod 2) G V)
    (B : Subgroup G) where
  groupEquiv : linearNormalizer ρ B ≃* OrthogonalFour
  coordinates : V ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 2 (ZMod 2)
  intertwines : ∀ g v, coordinates (g.val.val v) = (groupEquiv g).val (coordinates v)
  core_eq : ((linearImage ρ B).subgroupOf (linearNormalizer ρ B)).map
    groupEquiv.toMonoidHom = pCore 3 OrthogonalFour

/-- A normal subgroup's full linear normalizer contains the original action. -/
@[expose] def intoNormalizer (ρ : Representation (ZMod 2) G V) (B : Subgroup G) [B.Normal] :
    G →* linearNormalizer ρ B :=
  ρ.asGroupHom.codRestrict _ (fun g => by
    have h := B.le_normalizer_map ρ.asGroupHom
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : B.Normal)] at h
    exact h ⟨g, Subgroup.mem_top _, rfl⟩)

@[simp] theorem intoNormalizer_apply (ρ : Representation (ZMod 2) G V)
    (B : Subgroup G) [B.Normal] (g : G) (v : V) :
    (intoNormalizer ρ B g).val.val v = ρ g v := rfl

/-- Apply the normalizer identification to the actual subgroup acting on V.
The resulting subgroup contains the full orthogonal three-core. -/
theorem OrthogonalNormalizerModel.realization {ρ : Representation (ZMod 2) G V}
    {B : Subgroup G} [B.Normal] (d : OrthogonalNormalizerModel ρ B)
    (hfaithful : Function.Injective ρ) :
    ∃ H : Subgroup OrthogonalFour, pCore 3 OrthogonalFour ≤ H ∧
      OrthogonalRealization ρ H := by
  let j := intoNormalizer ρ B
  let f := d.groupEquiv.toMonoidHom.comp j
  have hj : Function.Injective j := by
    intro g k he
    apply hfaithful
    exact congrArg (fun x : linearNormalizer ρ B => x.val.val) he
  have hf : Function.Injective f := d.groupEquiv.injective.comp hj
  refine ⟨f.range, ?_, MonoidHom.ofInjective hf, d.coordinates, ?_⟩
  · rw [← d.core_eq]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨g, hg, he⟩ := hy
    refine ⟨g, ?_⟩
    exact congrArg d.groupEquiv (Subtype.ext he)
  · intro g v
    exact d.intertwines (j g) v
end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
