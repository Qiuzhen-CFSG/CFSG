module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.FixedCenter
public import Theory.Representation.BinaryConjugationSection.PairedSL2CubicFixed
public import Theory.GroupTheory.ConjugateOrbitFixedCenter
/-!
# Paired natural fixed points on the actual Sylow center

In the two-factor natural case, the Sylow exchanger identifies the two
coordinates of every central Sylow element. A cubic acts freely on one
coordinate, hence on both, even when it lies on a torus axis. The retained
kernel is the central fixed subgroup of the original orbit.

Together with the corresponding H* fixed-space identification, original
maximal two-local uniqueness removes both fixed centers. The paired section,
its literal coordinate swap, and the H* identification are earlier-source
inputs, not splitting assumptions on the original central covers.
Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance naturalGenerationPairedFieldFourAlgebra : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2
local notation "F" => Representation.OrthogonalFourMinus.FiniteModel.Field 1

omit [Finite G] in
/-- The actual Sylow center has the same fixed points for a cubic and the orbit. -/
theorem source_original_paired_natural_cubic_fixed_eq
    (q₁ q₂ : localOrbit T L →* SL(2,F)) (A : Subgroup G)
    (c : Representation.BinaryConjugationSection (localOrbit T L) A
      (A ⊓ centralizer (localOrbit T L : Set G))
      (Representation.prod (Representation.SL2.BinarySmall.natural.comp q₁)
        (Representation.SL2.BinarySmall.natural.comp q₂)))
    (hZA : omegaOneCenterAmbient (T : Subgroup G) ≤ A)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htA : t ∈ normalizer (A : Set G))
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hswap : ∀ a : A,
      ((c.coordinates ⟨t * a * t⁻¹,(mem_normalizer_iff.mp htA a).mp a.property⟩).toAdd).1 =
        f (c.coordinates a).toAdd.2)
    (b : localOrbit T L) (hb : orderOf (q₁ b) = 3 ∨ orderOf (q₂ b) = 3) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b : G)} : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) := by
  have hZt : omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer ({t} : Set G) := by
    intro z hz x hx
    have hxe : x = t := Set.mem_singleton_iff.mp hx
    rw [hxe]
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht
  have he := c.paired_natural_cubic_fixed_eq_kernel q₁ q₂ inf_le_right
    (omegaOneCenterAmbient (T : Subgroup G)) hZA t htA hZt f hswap b hb
  simpa only [←inf_assoc,inf_eq_left.mpr hZA] using he

omit [Finite G] in
/-- Passing to the original conjugate orbit does not alter Sylow-center fixed points. -/
theorem source_original_orbit_fixed_center_eq :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) := by
  apply fixed_center_componentOrbit_eq
  intro z hz t ht
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht

/-- The paired calculation supplies the original equality used to eliminate both
fixed centers, once E.2.3 supplies the actual H* fixed-space identification. -/
theorem source_hstar_paired_natural_fixed_centers_eq_bot {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (q₁ q₂ : localOrbit T L →* SL(2,F)) (A : Subgroup G)
    (c : Representation.BinaryConjugationSection (localOrbit T L) A
      (A ⊓ centralizer (localOrbit T L : Set G))
      (Representation.prod (Representation.SL2.BinarySmall.natural.comp q₁)
        (Representation.SL2.BinarySmall.natural.comp q₂)))
    (hZA : omegaOneCenterAmbient (T : Subgroup G) ≤ A)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htA : t ∈ normalizer (A : Set G))
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hswap : ∀ a : A,
      ((c.coordinates ⟨t * a * t⁻¹,(mem_normalizer_iff.mp htA a).mp a.property⟩).toAdd).1 =
        f (c.coordinates a).toAdd.2)
    (b : localOrbit T L) (hb : orderOf (q₁ b) = 3 ∨ orderOf (q₂ b) = 3)
    (hHZ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b : G)} : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ :=
  source_hstar_fixed_centers_eq_bot_of_eq D hH (hHZ.trans
    (source_original_paired_natural_cubic_fixed_eq q₁ q₂ A c hZA ht htA f hswap b hb))
end CFSG.Quasithin.Chapter10
