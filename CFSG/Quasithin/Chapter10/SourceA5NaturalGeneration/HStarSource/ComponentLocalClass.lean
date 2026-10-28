module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.LinearSelection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.QuasisimpleLinearLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.LocalAmbient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FiveSeedObstruction
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ActionSource
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
/-!
# The actual H* component and its common Baumann embedding

The genuine natural source selector supplies a single natural residual or
an exchanged natural pair. The corresponding C.1.17 constructions select
an actual C-component K in H, normalized by the same Baumann subgroup,
and retain its exact localV image. Canonical subtype transport marks the
embedding by the original ambient Baum(T), for the common characteristic
pair comparison in 10.2.3(4).

Source: Aschbacher--Smith C.1.26, E.2.3 and 10.2.3(4), pp.132,216--217,746.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)


/-- The Hall seed-centralizer identity identifies the actual reduced-action kernel. -/
theorem source_hstar_action_kernel_eq_core_of_seed_centralizer
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) :
    centralizer ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H : Set H) =
      pCore 2 H := by
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance,?_⟩
    exact (T.subtype hH.1.1.2).isPGroup'.to_le
      ((centralizer_le (subgroupOf_mono H (le_conjugateSpanBy _ _))).trans hCZ.le)
  · exact le_centralizer_iff.mp hU.le_centralizer_pCore

variable {F : Type*} [Field F] [CharP F 2]
local instance hstarComponentLocalFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
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
theorem source_hstar_component_localClass_of_seed_centralizer
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let B := baumann (S : Subgroup H)
    ∃ K : Subgroup H, K.IsCComponent ∧
      U ≤ normalizer (K : Set H) ∧ B ≤ normalizer (K : Set H) ∧
      ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ K ⊔ B from le_sup_right)) ∧
      (ChapterC.GlaubermanNiles.localV (inclusion (show B ≤ K ⊔ B from le_sup_right))).map
        (K ⊔ B).subtype = (⁅U,K⁆ : Subgroup H) ⊔
          (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
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
  have hP := source_a5_hstar_minimal_parabolic D e hn hH
  have hJ := source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n
  have hfit := source_hstar_fitting_eq_core D hH
  have hsq := Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (generationParameter_le_one_of_solvable (G := H))) hlarge
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  rcases source_hstar_linear_alternatives_of_seed_centralizer D e hn hH hZH hF f n hlarge hCZ with
    ⟨hqs,c,K,hlinear⟩ | ⟨d,K,⟨c⟩,hexchange⟩
  · obtain ⟨hR,hlocal,hv⟩ := quasisimple_linear_component_localClass
      h36 hsq S hP U hU hJ q hq hk hqs c.sectionData K hlinear hs
      (source_hstar_omega_orbit_eq_normalClosure D hH) hfit
    exact ⟨pResidual 2 H,hR,by rw [normalizer_eq_top]; exact le_top,
      by rw [normalizer_eq_top]; exact le_top,hlocal,hv⟩
  · obtain ⟨K,hK,_,_,hUK,hBK,hlocal,hv⟩ :=
      first_component_localClass h36 hsq S hP U hU hJ q hq hk hs hfit d K c hexchange
    exact ⟨K,hK,hUK,hBK,hlocal,hv⟩

/-- The actual H* local class uses exactly the original ambient Baumann inclusion. -/
theorem source_hstar_common_baumann_embedding_of_seed_centralizer
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let B := baumann (S : Subgroup H)
    ∃ K : Subgroup H, K.IsCComponent ∧ U ≤ normalizer (K : Set H) ∧
      B ≤ normalizer (K : Set H) ∧
      ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ K ⊔ B from le_sup_right)) ∧
      (ChapterC.GlaubermanNiles.localV (inclusion (show B ≤ K ⊔ B from le_sup_right))).map
        (K ⊔ B).subtype = (⁅U,K⁆ : Subgroup H) ⊔
          (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
      ∃ b : baumann (T : Subgroup G) →* (K ⊔ B : Subgroup H),
        ChapterC.GlaubermanNiles.InLocalClass b ∧
        (H.subtype.comp (K ⊔ B).subtype).comp b = (baumann (T : Subgroup G)).subtype := by
  obtain ⟨K,hK,hUK,hBK,hlocal,hv⟩ :=
    source_hstar_component_localClass_of_seed_centralizer D e hn hH hZH hF f n hlarge hCZ
  exact ⟨K,hK,hUK,hBK,hlocal,hv,
    ChapterC.GlaubermanNiles.original_baumann_embedding (T : Subgroup G) H hH.1.1.2
      (K ⊔ baumann (T.subtype hH.1.1.2 : Subgroup H)) le_sup_right hlocal⟩
end CFSG.Quasithin.Chapter10
