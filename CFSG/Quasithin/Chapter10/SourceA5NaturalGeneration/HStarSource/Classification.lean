module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.Movement
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ActionSource
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
/-!
# E.2.3 on the actual H* omega orbit

The natural-four original source gives genuine Thompson movement on the
original omega-center orbit in H. The generation parameter greater than
one excludes the solvable branch. E.2.3 then supplies the original marked
single or exchanged pair, retaining the exact centralizer quotient. The
common alpha and residual-span identities require no choice of a row.

Source: Aschbacher--Smith 10.2.2(2), 10.2.3(4), pp.744--746, and E.2.3.
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

theorem source_hstar_fitting_eq_core
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generalizedFitting H = pCore 2 H :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (D.simpleQTKE.evenCharacteristic T) hH.1.1))

/-- The literal ambient orbit is the normal closure of the intrinsic Sylow omega-center. -/
theorem source_hstar_omega_orbit_eq_normalClosure
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H =
      normalClosure (omegaOneCenterAmbient (T.subtype hH.1.1.2 : Subgroup H) : Set H) := by
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hz : omegaOneCenterAmbient (T.subtype hH.1.1.2 : Subgroup H) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (hZT.trans hH.1.1.2)]
    congr 1
    exact map_subgroupOf_eq_of_le hH.1.1.2
  rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ H (hZT.trans hH.1.1.2)]

variable {F : Type*} [Field F] [CharP F 2]
local instance hstarClassificationFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
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
/-- The complete source alternatives retain their genuine factor and module markings. -/
theorem source_hstar_marked_alternatives_of_natural_four
    (hlarge : 1 < generationParameter H) :
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
        (∃ K : BinaryField, IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) K 2) ∨
        Nonempty (MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ d : SourceTwoFactorCase σ,
        (∃ t : S.mapSurjective hq,
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first) ∧
        ((∃ K : BinaryField, Nonempty (d.MarkedProduct (linearNatural K 2))) ∨
          Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))) := by
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
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (generationParameter_le_one_of_solvable (G := H))) hlarge
  rcases source_nonsolvable_natural_factors
      (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) S hP U hU hs hJ with hsingle | ⟨d,_,_⟩
  · exact Or.inl hsingle
  · have hcore : pCore 2 (H ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
    have hne : q.ker ≠ ⊤ := by
      rw [hk]
      exact source_hstar_omega_orbit_centralizer_proper D hH hZH
    have hp := (minimalParabolic_reduced_image S hP q hq hcore hne).2
    have hff : IsFFModule α := by
      obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk S
      · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
      · exact hf
    obtain ⟨t,ht₁,ht₂,hkind⟩ := source_offender_two_factor_shared_natural α
      (S.mapSurjective hq) hp hff hcore d
    exact Or.inr ⟨d,⟨t,ht₁,ht₂⟩,hkind⟩

/-- The actual H* alpha subgroup has the E.2.3 moved-plus-fixed decomposition. -/
theorem source_hstar_alpha_and_span_of_natural_four :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    thompsonAlpha (S : Subgroup H) =
      ((⁅U,pResidual 2 H⁆ : Subgroup H) ⊓
        centralizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)) ⊔
      (thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) ∧
    conjugateSpanBy (thompsonAlpha (S : Subgroup H)) (pResidual 2 H) =
      (⁅U,pResidual 2 H⁆ : Subgroup H) ⊔
        (thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) := by
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  exact (source_action_conclusions (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1)
    (T.subtype hH.1.1.2) (source_a5_hstar_minimal_parabolic D e hn hH) _ hU
    (source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n)).2.2.2
end CFSG.Quasithin.Chapter10
