module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.FiveAxes
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.LocalRestriction
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.FiveNaturalObstruction
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.Coordinates
/-!
# The original natural module excludes the paired five-letter source

The original component lies on one of the two marked residual axes.
Restrict its given full natural section to the literal local moved layer;
the first-axis obstruction applies directly or after swapping the marking.
Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance originalFiveSourceFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
set_option backward.isDefEq.respectTransparency false in
theorem source_original_not_paired_five_of_natural_four
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)))
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    ¬ SourcePairedFiveAction D := by
  intro hp
  let X := localJoin T L
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set X) := QuotientGroup.ker_mk' C
  have ni := source_original_a5_internal_moved_natural_section D e f n
  obtain ⟨d,c,_,_,hi⟩ := source_original_paired_five_axes_of_source D e hn hJ hp
  rcases hi with hi | hi
  · exact not_first_five_residual_of_natural_four U q hq hk d c _ hi hF _ ni
  · exact not_first_five_residual_of_natural_four U q hq hk
      (sourceSwap d) (markedSwap c) _ hi hF _ ni
end CFSG.Quasithin.Chapter10
