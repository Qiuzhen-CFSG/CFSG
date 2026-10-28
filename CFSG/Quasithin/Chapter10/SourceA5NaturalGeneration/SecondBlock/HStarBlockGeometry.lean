module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.HStarBaumann
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.SymmetricGeometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.Classification
/-!
# Intrinsic core and Sylow data for the recovered H* block

Full-core movement and the zero Sylow-center fixed subgroup remove the
central cover of the selected block. The exact residual cover identifies
its core with its distinguished U-layer. Intersecting the common Baumann
Sylow with this subnormal component retains a full Sylow of the same K.
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
local instance hstarBlockGeometryFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

theorem source_hstar_block_core_and_sylow
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
    center K=⊥ ∧ pCore 2 K=blockU K ∧
      Chapter1.IsSylowIn 2 (baumann (T.subtype hH.1.1.2 : Subgroup H) ⊓ K) K := by
  let S := T.subtype hH.1.1.2
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
  have hm := (source_hstar_block_full_core_moved D e hn hH hZH hF f n
    hlarge hCZ hz K hb hR).2
  obtain ⟨hcenter,hcore⟩ := source_block_center_and_core_of_residual_cover
    (source_hstar_fitting_eq_core D hH) K hb hR
    (core_residual_fixed_eq_bot_of_omega_center S hzH) hm
  have hS := (source_hstar_baumann_in_residual_of_block D e hn hH hZH hF f n
    hlarge hCZ hz K hb hR).1
  have hKR : K ≤ pResidual 2 H := by
    rcases hR with he | ⟨t,he⟩
    · exact he.ge
    · exact he ▸ le_sup_left
  exact ⟨hcenter,hcore,
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hKR hb.subnormal.subgroupOf⟩
end CFSG.Quasithin.Chapter10
