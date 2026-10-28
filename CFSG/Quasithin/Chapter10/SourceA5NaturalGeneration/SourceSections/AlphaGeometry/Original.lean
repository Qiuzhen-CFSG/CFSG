module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedAlphaCard
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.Field
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaPlacement
public import Theory.ElementaryAbelian.PrimeRankCard
/-!
# Original Thompson alpha has order sixteen

The original HStar movement and natural-four section select a genuine paired
linear source. Its actual binary field has order four, by comparison of the
original A5 component image with the marked SL2 factor. Vanishing of the
original omega-center centralizer kills the source central summand and the
literal coordinate kernel. The paired Sylow fixed codimension then gives
alpha order sixteen and binary rank four, before any block alternative.

Source: Aschbacher--Smith 10.2.3(4), printed p.746, using E.2.3(2).
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem source_original_alpha_card_of_paired_linear
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      Nat.card (thompsonAlpha (T : Subgroup G)) = 16 := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F c hexchange
  have hfield := source_original_paired_field_card D e hn hJ d F c hexchange
  have hzS : (S : Subgroup X) ⊓ centralizer (pResidual 2 X : Set X) = ⊥ := by
    apply bot_unique
    rintro x ⟨hx,hxc⟩
    have hh : (x:G) ∈ (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) := by
      refine ⟨hx,?_⟩
      intro l hl
      obtain ⟨a,ha,rfl⟩ := (source_join_residual D).symm ▸ hl
      exact congrArg X.subtype (hxc a ha)
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp ((source_sylow_orbit_centralizer_eq_bot hz) ▸ hh)))
  have hcard := RankOneBaumann.PairedFactorOrbit.source_alpha_card_of_trivial_sylow_residual_centralizer
    S (source_a5_minimal_parabolic D e hn) U hU hJ q hq hk d F c hexchange hzS
  have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hα : (thompsonAlpha (S : Subgroup X)).map X.subtype = thompsonAlpha (T : Subgroup G) := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      hS]
  have hm := card_map_of_injective (K := thompsonAlpha (S : Subgroup X)) X.subtype_injective
  rw [hα] at hm
  rw [hfield] at hcard
  exact hm.trans hcard

variable {H : Subgroup G}
variable {F : Type*} [Field F] [CharP F 2]
local instance alphaGeometryFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
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

theorem source_original_alpha_card_of_hstar_natural_four
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card (thompsonAlpha (T : Subgroup G)) = 16 := by
  obtain ⟨d,K,⟨c⟩,hexchange⟩ :=
    source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  exact source_original_alpha_card_of_paired_linear D e hn hz
    (source_hstar_local_thompson_moves_of_omega_commutator D hH hZH) d K c hexchange

theorem source_original_alpha_rank_of_hstar_natural_four
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    primeRank 2 (thompsonAlpha (T : Subgroup G)) = 4 := by
  let : IsElementaryAbelian 2 (thompsonAlpha (T : Subgroup G)) := omegaOneCenterAmbient_elementaryAbelian _
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2),
    source_original_alpha_card_of_hstar_natural_four D e hn hH hZH hF f n hz]
  norm_num
end CFSG.Quasithin.Chapter10
