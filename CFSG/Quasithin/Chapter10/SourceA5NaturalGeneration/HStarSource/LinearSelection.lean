module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.Classification
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FiveSeedObstruction
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ActionSource
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
/-!
# Selecting the natural H* source from its actual omega-center centralizer

A Sylow centralizer for the original omega-center seed excludes both
five-letter alternatives by cubic fixed-space enlargement. The surviving
natural single or exchanged pair retains the original centralizer quotient
and actual marked section. The seed-centralizer identity is the separate
Hall placement and original natural-torus boundary in 10.2.3(4).

Source: Aschbacher--Smith 10.2.3(4), printed pp.745--746.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

variable {F : Type*} [Field F] [CharP F 2]
local instance hstarLinearSelectionFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
include e hn hH hZH hF f n


set_option backward.isDefEq.respectTransparency false in
/-- The genuine natural source selection after the Hall seed-centralizer step. -/
theorem source_hstar_linear_alternatives_of_seed_centralizer
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    let σ := α.comp Y.subtype
    letI := offenderSubgroup_normal α
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        ∃ K : BinaryField, IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) K 2) ∨
      ∃ (d : SourceTwoFactorCase σ) (K : BinaryField),
        Nonempty (d.MarkedProduct (linearNatural K 2)) ∧
        ∃ t : S.mapSurjective hq,
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hZU : Z ≤ U := subgroupOf_mono H (le_conjugateSpanBy _ _)
  rcases source_hstar_marked_alternatives_of_natural_four D e hn hH hZH hF f n hlarge with
    ⟨hqs,c,hkind⟩ | ⟨d,hexchange,hkind⟩
  · rcases hkind with hlinear | hfive
    · exact Or.inl ⟨hqs,c,hlinear⟩
    · obtain ⟨a⟩ := hfive
      exfalso
      exact not_marked_five_movedSection_of_seed U Z q hq hk hZU S hCZ Y
        (generalizedFitting Y) c.sectionData a
  · rcases hkind with ⟨K,hlinear⟩ | hfive
    · exact Or.inr ⟨d,K,hlinear,hexchange⟩
    · obtain ⟨a⟩ := hfive
      exact (not_pairedFive_of_seed U Z q hq hk hZU S hCZ Y d a).elim
end CFSG.Quasithin.Chapter10
