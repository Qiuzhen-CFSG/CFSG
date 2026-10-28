module
public import Theory.Representation.BinaryConjugationSection.PairedCentralSupplement
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.PairedFixed
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.PairedSource
/-!
# Original cubic fixed points before central alpha vanishes

The E.2.3 seed bound retains the central alpha summand. That summand is
T-invariant and centralizes the original orbit. The natural paired coordinate
calculation therefore applies to the original Sylow center even before it
has been placed wholly in the local module. Original maximal-local uniqueness
then removes both fixed centers when the HStar cubic fixed space agrees.

Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance fixedCenterSplitFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

omit [Finite G] in
private theorem sylow_normalizes_central_alpha :
    (T : Subgroup G) ≤ normalizer
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) : Set G) := by
  have hTa : (T : Subgroup G) ≤ normalizer (thompsonAlpha (T : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G))).map
      (MulAut.conj t).toMonoidHom = _
    have hT : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective,
      ←elementaryAbelianMaxJ_map_equiv,hT]
    rfl
  exact (le_inf hTa ((le_normalizer_componentOrbit L T).trans
    (normalizer_le_normalizer_centralizer (localOrbit T L)))).trans
      inf_normalizer_le_normalizer_inf

theorem source_original_paired_natural_cubic_fixed_eq_of_seed_split
    (q₁ q₂ : localOrbit T L →* SL(2,F))
    (c : Representation.BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
      (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
      (Representation.prod (Representation.SL2.BinarySmall.natural.comp q₁)
        (Representation.SL2.BinarySmall.natural.comp q₂)))
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤
      ⁅D.moduleSubgroup,localOrbit T L⁆ ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hswap : ∀ a : D.moduleSubgroup,
      ((c.coordinates ⟨t * a * t⁻¹,
        (mem_normalizer_iff.mp (D.sylow_normalizes_module ht) a).mp a.property⟩).toAdd).1 =
        f (c.coordinates a).toAdd.2)
    (b : localOrbit T L) (hb : orderOf (q₁ b) = 3 ∨ orderOf (q₂ b) = 3) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b : G)} : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) := by
  apply c.paired_natural_cubic_fixed_eq_of_central_supplement q₁ q₂ inf_le_right
    (omegaOneCenterAmbient (T : Subgroup G))
    (hZ.trans (sup_le_sup (le_normalizer_iff_commutator_le_left.mp D.orbit_normalizes_module) le_rfl))
    t (D.sylow_normalizes_module ht) (sylow_normalizes_central_alpha ht) ?_ f hswap b hb
  intro z hz y hy
  rw [Set.mem_singleton_iff.mp hy]
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht

theorem source_hstar_paired_natural_fixed_centers_eq_bot_of_seed_split {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (q₁ q₂ : localOrbit T L →* SL(2,F))
    (c : Representation.BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
      (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
      (Representation.prod (Representation.SL2.BinarySmall.natural.comp q₁)
        (Representation.SL2.BinarySmall.natural.comp q₂)))
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤
      ⁅D.moduleSubgroup,localOrbit T L⁆ ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hswap : ∀ a : D.moduleSubgroup,
      ((c.coordinates ⟨t * a * t⁻¹,
        (mem_normalizer_iff.mp (D.sylow_normalizes_module ht) a).mp a.property⟩).toAdd).1 =
        f (c.coordinates a).toAdd.2)
    (b : localOrbit T L) (hb : orderOf (q₁ b) = 3 ∨ orderOf (q₂ b) = 3)
    (hHZ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b : G)} : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ :=
  source_hstar_fixed_centers_eq_bot_of_eq D hH (hHZ.trans
    (source_original_paired_natural_cubic_fixed_eq_of_seed_split D q₁ q₂ c hZ ht f hswap b hb))
end CFSG.Quasithin.Chapter10
