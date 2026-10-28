module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.PairedSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.LocalAmbient

/-!
# The original Baumann source in the actual paired-source local class

Re-mark the proved original-component local class by the canonical Baumann
identification. The embedding's composite into G is exactly the original
Baumann subgroup inclusion. This is the source marking needed to apply one
universal characteristic pair across the two original local groups.

Source: Aschbacher–Smith C.1.26 and 10.2.3(4), pp.132,746.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual original paired source uses the same ambient Baumann group
as the other local-class applications, with its inclusion retained. -/
theorem source_original_common_baumann_embedding_of_paired_linear
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
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
      let N := L.subgroupOf X ⊔ baumann (S : Subgroup X)
      ∃ f : baumann (T : Subgroup G) →* N,
        ChapterC.GlaubermanNiles.InLocalClass f ∧
        (X.subtype.comp N.subtype).comp f = (baumann (T : Subgroup G)).subtype := by
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
  have hc := source_original_component_localClass_of_paired_linear D e hn hJ d F c hexchange
  exact ChapterC.GlaubermanNiles.original_baumann_embedding
    (T : Subgroup G) X le_sup_right (L.subgroupOf X ⊔ baumann (S : Subgroup X))
    le_sup_right hc.2.2.1
end CFSG.Quasithin.Chapter10
