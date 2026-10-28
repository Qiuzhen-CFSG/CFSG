module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaPlacement
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.FixedCenterSplit
/-!
# Original natural source at the fixed-center and alpha boundaries

The completed original paired selection supplies the seed decomposition.
Its central summand is retained through the cubic fixed-center comparison,
so that comparison does not assume the vanishing it is meant to prove.
After the fixed centers vanish, the same selected source places the entire
original Thompson alpha subgroup in the original moved module.

Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance originalAssemblyFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
include e hn hH hZH hF f n

theorem source_original_alpha_le_moved_of_hstar_natural_four
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    thompsonAlpha (T : Subgroup G) ≤ ⁅D.moduleSubgroup,localOrbit T L⁆ := by
  obtain ⟨d,K,⟨c⟩,hexchange⟩ :=
    source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  exact source_original_alpha_le_moved_of_paired_linear D e hn hz
    (source_hstar_local_thompson_moves_of_omega_commutator D hH hZH) d K c hexchange

theorem source_original_alpha_le_module_of_hstar_natural_four
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    thompsonAlpha (T : Subgroup G) ≤ D.moduleSubgroup :=
  (source_original_alpha_le_moved_of_hstar_natural_four D e hn hH hZH hF f n hz).trans
    (le_normalizer_iff_commutator_le_left.mp D.orbit_normalizes_module)

variable {K : Type*} [Field K] [CharP K 2]
local instance originalAssemblyPairAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

theorem source_hstar_natural_four_fixed_centers_eq_bot_of_paired_coordinates
    (q₁ q₂ : localOrbit T L →* SL(2,K))
    (c : BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
      (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
      (Representation.prod (SL2.BinarySmall.natural.comp q₁)
        (SL2.BinarySmall.natural.comp q₂)))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (s : (Fin 2 → K) ≃ₗ[ZMod 2] (Fin 2 → K))
    (hswap : ∀ a : D.moduleSubgroup,
      ((c.coordinates ⟨t * a * t⁻¹,
        (mem_normalizer_iff.mp (D.sylow_normalizes_module ht) a).mp a.property⟩).toAdd).1 =
        s (c.coordinates a).toAdd.2)
    (b : localOrbit T L) (hb : orderOf (q₁ b) = 3 ∨ orderOf (q₂ b) = 3)
    (hHZ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b : G)} : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ :=
  source_hstar_paired_natural_fixed_centers_eq_bot_of_seed_split D hH q₁ q₂ c
    (source_original_seed_le_moved_sup_central_alpha_of_hstar_natural_four
      D e hn hH hZH hF f n) ht s hswap b hb hHZ
end CFSG.Quasithin.Chapter10
