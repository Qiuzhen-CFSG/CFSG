module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.SymmetricCore
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.Classification
/-!
# Full-core recovery on the original H* group

The actual omega-center orbit and natural-four source supply reducedness,
Thompson movement and minimal-parabolic structure. Transport the vanishing
ambient omega-center fixed subgroup into H, and apply the single-or-paired
residual block theorem. Thus the entire O₂(H) is elementary and moved, while
the original seed, quotient marking and H* group remain unchanged.
Source: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC ChapterE Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance hstarFullCoreFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The actual H* block branch supplies full-core generation without choosing a paired row. -/
theorem source_hstar_block_full_core_moved
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (K : Subgroup H) (hb : IsBlock K)
    (hR : pResidual 2 H = K ∨
      ∃ t : H, pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    IsElementaryAbelian 2 (pCore 2 H) ∧ pCore 2 H = ⁅pCore 2 H,pResidual 2 H⁆ := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H
  have hzH : omegaCenterIn (S : Subgroup H) ⊓ center H = ⊥ := by
    apply bot_unique
    intro z hz'
    have hzm : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
      have hh := mem_map_of_mem H.subtype hz'.1
      change (z : G) ∈ (omegaOneCenterAmbient (S : Subgroup H)).map H.subtype at hh
      rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective] at hh
      have hSm : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
        map_subgroupOf_eq_of_le hH.1.1.2
      rwa [hSm] at hh
    have hzc : (z : G) ∈ centralizer (H : Set G) := by
      intro h hh
      exact congrArg H.subtype (mem_center_iff.mp hz'.2 ⟨h,hh⟩)
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hz ▸ ⟨hzm,hzc⟩)))
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (ChapterE.generationParameter_le_one_of_solvable (G := H))) hlarge
  exact source_block_residual_full_core_moved
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) S
    (source_a5_hstar_minimal_parabolic D e hn hH) U
    (source_hstar_omega_orbit_reduced D hH) hs
    (source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n)
    (source_hstar_fitting_eq_core D hH) Z
    (subgroupOf_mono H (le_conjugateSpanBy _ _)) hCZ hzH K hb hR
end CFSG.Quasithin.Chapter10
