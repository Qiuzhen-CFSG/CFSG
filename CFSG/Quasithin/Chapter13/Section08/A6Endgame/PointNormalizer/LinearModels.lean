module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer.Models
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.IntersectionBalance.Spaces

/-!
# Whole-module coordinates for the terminal point normalizer

The literal quotient U/Z is compared linearly with the full natural module
or its full five-dimensional cover. Nonfixedness is stated intrinsically
for the quotient action; it excludes the constant line only in the cover.
The point-normalizer model is constructed using the actual two-core lift.

These are conditional interfaces for the final paragraph of 13.8.1,
Aschbacher–Smith (1 March 2004), printed pp.968–969. The source application
must still prove movement by O₂(H) and nonfixedness of the critical point.
-/

public section

open Subgroup BinaryPermutation Theory.SpecificGroups.SymmetricSix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
open IntersectionBalance BinaryFlags.PointOrbits
variable {G : Type*} [Group G] {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

@[expose] def LinearCoordinates (a : SolvableExclusion.Five.StarAction H U Z)
    (e : Source.Hstar H →* S6) : Prop :=
  (∃ f : Additive (U ⧸ Z.subgroupOf U) ≃ₗ[ZMod 2] natural (Fin 6),
    ∀ g v, f (tildeRepresentation H U Z a g v) =
      naturalRepresentation (Fin 6) (e g) (f v)) ∨
  (∃ f : Additive (U ⧸ Z.subgroupOf U) ≃ₗ[ZMod 2] core (Fin 6),
    ∀ g v, f (tildeRepresentation H U Z a g v) =
      coreRepresentation (Fin 6) (e g) (f v))

private theorem image_ne_fixed {W : Type*}
    (a : SolvableExclusion.Five.StarAction H U Z) (u : U)
    (f : (U ⧸ Z.subgroupOf U) ≃ W) (ρ : Source.Hstar H → W → W)
    (he : ∀ g v, f (a.action g v) = ρ g (f v))
    (hnf : ∃ g, a.action g (QuotientGroup.mk' (Z.subgroupOf U) u) ≠
      QuotientGroup.mk' (Z.subgroupOf U) u)
    (w : W) (hw : ∀ g, ρ g w = w) :
    f (QuotientGroup.mk' (Z.subgroupOf U) u) ≠ w := by
  intro h
  obtain ⟨g, hg⟩ := hnf
  apply hg
  apply f.injective
  rw [he, h, hw]

theorem symmetric_model_of_linear_coordinates
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* S6) (hc : LinearCoordinates a e.toMonoidHom)
    (hnf : ∃ g, a.action g (QuotientGroup.mk' (Z.subgroupOf U) u) ≠
      QuotientGroup.mk' (Z.subgroupOf U) u) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* duadStabilizer) := by
  rcases hc with ⟨f, he⟩ | ⟨f, he⟩
  · let F : (U ⧸ Z.subgroupOf U) ≃ natural (Fin 6) := Additive.ofMul.trans f.toEquiv
    have hF : ∀ g v, F (a.action g v) = naturalRepresentation (Fin 6) (e g) (F v) :=
      fun g v => he g (Additive.ofMul v)
    exact symmetric_model_of_natural a A hA u hu hu1 hZ hcomm hm e F hF
      (image_ne_fixed a u F _ hF hnf 0 (fun g => map_zero _))
  · let F : (U ⧸ Z.subgroupOf U) ≃ core (Fin 6) := Additive.ofMul.trans f.toEquiv
    have hF : ∀ g v, F (a.action g v) = coreRepresentation (Fin 6) (e g) (F v) :=
      fun g v => he g (Additive.ofMul v)
    exact symmetric_model_of_cover a A hA u hu hu1 hZ hcomm hm e F hF
      (image_ne_fixed a u F _ hF hnf 0 (fun g => map_zero _))
      (image_ne_fixed a u F _ hF hnf coverOne (fun g => coverOne_map (e g)))

theorem alternating_model_of_linear_coordinates
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n)
    (e : Source.Hstar H ≃* A6) (hc : LinearCoordinates a (A6.subtype.comp e.toMonoidHom))
    (hnf : ∃ g, a.action g (QuotientGroup.mk' (Z.subgroupOf U) u) ≠
      QuotientGroup.mk' (Z.subgroupOf U) u) :
    Nonempty (Source.starImage H (normalizer (A : Set G)) ≃* a6DuadStabilizer) := by
  rcases hc with ⟨f, he⟩ | ⟨f, he⟩
  · let F : (U ⧸ Z.subgroupOf U) ≃ natural (Fin 6) := Additive.ofMul.trans f.toEquiv
    have hF : ∀ g v, F (a.action g v) = naturalRepresentation (Fin 6) (e g).val (F v) :=
      fun g v => he g (Additive.ofMul v)
    exact alternating_model_of_natural a A hA u hu hu1 hZ hcomm hm e F hF
      (image_ne_fixed a u F _ hF hnf 0 (fun g => map_zero _))
  · let F : (U ⧸ Z.subgroupOf U) ≃ core (Fin 6) := Additive.ofMul.trans f.toEquiv
    have hF : ∀ g v, F (a.action g v) = coreRepresentation (Fin 6) (e g).val (F v) :=
      fun g v => he g (Additive.ofMul v)
    exact alternating_model_of_cover a A hA u hu hu1 hZ hcomm hm e F hF
      (image_ne_fixed a u F _ hF hnf 0 (fun g => map_zero _))
      (image_ne_fixed a u F _ hF hnf coverOne (fun g => coverOne_map (e g).val))
end CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
