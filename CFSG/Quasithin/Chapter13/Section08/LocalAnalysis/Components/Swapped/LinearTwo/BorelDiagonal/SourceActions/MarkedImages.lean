module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions

/-!
# Marked quotient images and residual transport

A map with two-group kernel to an odd-order target kills exactly the
intrinsic two-core on every subgroup of its domain. Its marked image is
therefore isomorphic to the subgroup's two-core quotient; the subgroup
itself is not identified with that quotient. Actual normalizing conjugations
transport invariance, fixation and inversion through this comparison.
The embedded two-residual still covers an odd-order target equivariantly.

These are transport helpers for Aschbacher–Smith, proof of 13.8.16(1),
printed p.952/PDF p.969, with the markings of Notation 13.2.1, p.877.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions
namespace Markings
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G D : Type*} [Group G] [Group D]
variable (B X : Subgroup G) (hXB : X ≤ B) (f : B →* D)

/-- The image of the actual marked subgroup, in the target of the torus map. -/
def image : Subgroup D := (X.subgroupOf B).map f

def restriction : X →* D := f.comp (inclusion hXB)

theorem restriction_range : (restriction B X hXB f).range = image B X f := by
  rw [restriction, MonoidHom.range_comp, inclusion_range]
  rfl

private theorem two_subgroup_eq_bot (A : Subgroup D) (hp : IsPGroup 2 A)
    (ho : Odd (Nat.card D)) : A = ⊥ := by
  apply card_eq_one.mp
  exact hp.card_eq_or_dvd.resolve_right (fun h => ho.not_two_dvd_nat
    (h.trans A.card_subgroup_dvd_card))

/-- The restricted kernel is the intrinsic two-core, without normality of X in B. -/
theorem restriction_ker (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card D)) :
    (restriction B X hXB f).ker = pCore 2 X := by
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    change IsPGroup 2 (f.comp (inclusion hXB)).ker
    rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective _ (inclusion_injective hXB)
  · apply (Subgroup.map_eq_bot_iff _).mp
    exact two_subgroup_eq_bot _ (pCore_isPGroup.map _) ho

/-- The first isomorphism theorem identifies the image with X/O₂(X), not X. -/
noncomputable def quotientEquiv (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card D)) :
    (X ⧸ pCore 2 X) ≃* image B X f :=
  ((QuotientGroup.quotientMulEquivOfEq (restriction_ker B X hXB f hk ho).symm).trans
    (QuotientGroup.quotientKerEquivRange (restriction B X hXB f))).trans
      (MulEquiv.subgroupCongr (restriction_range B X hXB f))

theorem quotientEquiv_mk (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card D)) (x : X) :
    (quotientEquiv B X hXB f hk ho (QuotientGroup.mk' (pCore 2 X) x) : D) =
      f (inclusion hXB x) := rfl

include hXB in
theorem image_card (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card D)) :
    Nat.card (image B X f) = Nat.card (X ⧸ pCore 2 X) :=
  (Nat.card_congr (quotientEquiv B X hXB f hk ho).toEquiv).symm

/-- An ambient normalizing conjugation preserves the actual marked image. -/
theorem image_invariant (g : normalizer (B : Set G))
    (hgX : g.val ∈ normalizer (X : Set G)) (a : MulAut D)
    (heq : ∀ b : B, a (f b) = f (B.normalizerMonoidHom g b)) :
    (image B X f).map a.toMonoidHom = image B X f := by
  have hX : (X.subgroupOf B).map (B.normalizerMonoidHom g).toMonoidHom = X.subgroupOf B := by
    ext x
    rw [mem_map_equiv]
    have hinv : (B.normalizerMonoidHom g).symm = B.normalizerMonoidHom g⁻¹ :=
      (map_inv B.normalizerMonoidHom g).symm
    rw [hinv]
    change g.val⁻¹ * x.val * (g.val⁻¹)⁻¹ ∈ X ↔ x.val ∈ X
    exact
      (mem_normalizer_iff.mp ((normalizer (X : Set G)).inv_mem hgX) x.val).symm
  change ((X.subgroupOf B).map f).map a.toMonoidHom = _
  rw [map_map]
  have he : a.toMonoidHom.comp f = f.comp (B.normalizerMonoidHom g).toMonoidHom :=
    MonoidHom.ext heq
  rw [he, ← map_map, hX]
  rfl

include hXB in
/-- Fixation of the intrinsic two-core quotient gives pointwise fixation in the torus. -/
theorem image_fixed (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card D))
    (g : normalizer (B : Set G)) (hgX : g.val ∈ normalizer (X : Set G))
    (a : MulAut D) (heq : ∀ b : B, a (f b) = f (B.normalizerMonoidHom g b))
    (hfix : coreAction X ⟨g.val, hgX⟩ = 1) :
    ∀ z ∈ image B X f, a z = z := by
  rintro _ ⟨x, hx, rfl⟩
  let y : X := ⟨x.val, hx⟩
  have h := congrArg (fun u : MulAut (X ⧸ pCore 2 X) => u (QuotientGroup.mk' _ y)) hfix
  rw [coreAction_mk] at h
  change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom ⟨g.val, hgX⟩ y) =
    QuotientGroup.mk' (pCore 2 X) y at h
  have hh := congrArg (fun u => (quotientEquiv B X hXB f hk ho u : D)) h
  rw [quotientEquiv_mk, quotientEquiv_mk] at hh
  exact (heq x).trans hh

include hXB in
/-- Inversion of the intrinsic quotient gives pointwise inversion of its torus image. -/
theorem image_inverted (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card D))
    (g : normalizer (B : Set G)) (hgX : g.val ∈ normalizer (X : Set G))
    (a : MulAut D) (heq : ∀ b : B, a (f b) = f (B.normalizerMonoidHom g b))
    (hinv : ∀ u, coreAction X ⟨g.val, hgX⟩ u = u⁻¹) :
    ∀ z ∈ image B X f, a z = z⁻¹ := by
  rintro _ ⟨x, hx, rfl⟩
  let y : X := ⟨x.val, hx⟩
  have h := hinv (QuotientGroup.mk' _ y)
  rw [coreAction_mk] at h
  have hh := congrArg (fun u => (quotientEquiv B X hXB f hk ho u : D)) h
  simp only [map_inv, coe_inv, quotientEquiv_mk] at hh
  exact (heq x).trans hh

/-- An odd-order target is covered by the two-residual of a surjecting finite group. -/
theorem residual_surjective [Finite G] [Finite D] (hf : Function.Surjective f) (ho : Odd (Nat.card D)) :
    Function.Surjective (f.comp (inclusion (map_subtype_le (pResidual 2 B)))) := by
  have hR : pResidual 2 D = ⊤ := by
    apply index_eq_one.mp
    rw [index_eq_card]
    exact (isPGroup_quotient_pResidual (G := D) 2).card_eq_or_dvd.resolve_right
      (fun h => ho.not_two_dvd_nat (h.trans (card_quotient_dvd_card _)))
  have hm : (pResidual 2 B).map f = ⊤ := by
    rw [map_pResidual_of_surjective 2 f hf, hR]
  intro d
  obtain ⟨b, hb, hbd⟩ := (show d ∈ (pResidual 2 B).map f by rw [hm]; trivial)
  exact ⟨⟨b.val, ⟨b, hb, rfl⟩⟩, hbd⟩

/-- The residual restriction still intertwines the actual ambient conjugation. -/
theorem residual_equivariant (g : normalizer (B : Set G)) (a : MulAut D)
    (heq : ∀ b : B, a (f b) = f (B.normalizerMonoidHom g b))
    (b : residual B) :
    a ((f.comp (inclusion (residual_le B))) b) =
      (f.comp (inclusion (residual_le B)))
        ((residual B).normalizerMonoidHom
          ⟨g.val, normalizer_le_residual_normalizer B g.property⟩ b) :=
  heq (inclusion (residual_le B) b)

end Markings
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions

end
