module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarOvergroupAction
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneFactorSelection

/-!
# B.5.6 on the literal Thompson image of the H-star overgroup

The images of the maximum elementary subgroups generate exactly `J(X)*`.
Each image is still a best offender after restriction to this generated
subgroup. Thus the restricted action satisfies the generation hypothesis of
B.5.3 in its own right; no equality with the larger ambient offender subgroup
is asserted. Conjugacy of the maximum family gives normality, allowing the
trivial two-core to pass to the actual Thompson image. The original local
SQTK cover restricts along the literal subgroup inclusion.

This supplies B.5.6 for the source actor in 6.1.5. The construction of
`X = ⟨D_L,H⟩` and the subsequent source exclusions remain with their owners.
Source: Aschbacher--Smith B.2.7 and B.5.6, and 6.1.5, pp.667--668.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter6.Source.ThompsonImage

universe u v
variable {P : Type u} [Group P] [Finite P]
  {D : Type v} [Group D] [Finite D]
  (U : Subgroup P) [U.Normal] [IsElementaryAbelian 2 U]
  (q : P →* D) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (U : Set P))

include U hq hker in
/-- The literal image of the global Thompson subgroup is normal. -/
theorem normal : ((elementaryAbelianMaxJ (⊤ : Subgroup P)).map q).Normal := by
  rw [ChapterB.maxOffenderImages_generated (⊤ : Subgroup P) U q]
  exact generatedBy_normal_of_conj _ (ChapterB.lemma_B_2_5_closure U q hq hker).1

/-- Maximum elementary images generate the restricted actor by actual best
 offenders. This does not identify it with all ambient offenders. -/
theorem generated :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup P)).map q
    offenderSubgroup (ρ.comp J.subtype) = ⊤ := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup P)).map q
  have hgen : J = generatedBy (ChapterB.maxOffenderImages (⊤ : Subgroup P) U q) ⊤ :=
    ChapterB.maxOffenderImages_generated (⊤ : Subgroup P) U q
  have hle : J ≤ (offenderSubgroup (ρ.comp J.subtype)).map J.subtype := by
    apply hgen.le.trans
    refine iSup_le fun E => iSup_le fun hE => ?_
    obtain ⟨A, hA, rfl, hne⟩ := hE.1
    have hAJ : A.map q ≤ J := map_mono (le_sSup hA)
    have hbest : IsBestOffender ρ (A.map q) :=
      Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
        U q hq hker ⊤ A le_top hA hne
    exact (map_subgroupOf_eq_of_le hAJ).symm.le.trans
      (map_mono ((hbest.subgroupOf ρ hAJ).le_offenderSubgroup (ρ.comp J.subtype)))
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  exact (J.subtype_injective he) ▸ hy

/-- B.5.3 holds on the actual Thompson image using the pulled-back SQTK cover. -/
theorem hypothesis {κ : GroupClass.{v}}
    (hcore : pCore 2 D = ⊥) (c : ChapterB.SourceInduction.SQTKQuotient κ D) :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup P)).map q
    ChapterB.SourceInduction.FFHypothesis κ (ρ.comp J.subtype) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup P)).map q
  let : J.Normal := normal U q hq hker
  refine ⟨inferInstance,
    (NormalElementaryQuotient.representation_injective U q hq hker).comp
      J.subtype_injective, ?_, generated U q hq hker, ⟨c.subgroup J⟩⟩
  have hle : (pCore 2 J).map J.subtype ≤ pCore 2 D :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map J.subtype⟩
  rw [hcore] at hle
  exact (map_eq_bot_iff_of_injective _ J.subtype_injective).mp (bot_unique hle)

end CFSG.Quasithin.Chapter6.Source.ThompsonImage

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H X : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- B.2.7's exact image and its containment in the ambient offender subgroup. -/
theorem hstar_overgroup_maximum_image_generated
    (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q =
        generatedBy (ChapterB.maxOffenderImages (⊤ : Subgroup X) U q) ⊤ ∧
      generatedBy (ChapterB.maxOffenderImages (⊤ : Subgroup X) U q) ⊤ ≤
        offenderSubgroup ρ := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  exact ⟨ChapterB.maxOffenderImages_generated (⊤ : Subgroup X) U q,
    ChapterB.lemma_B_2_7_second_generated U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)⟩

/-- All B.5.3 hypotheses on `J(X)*`, rather than on the larger offender actor. -/
theorem overgroup_thompson_hypothesis
    (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple (ρ.comp J.subtype) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (X ⧸ C) := {
    Cover := X
    kernel := C
    sqtk := Chapter3.sqtk_of_mem_H h.simpleQTKE hX.1
    equiv := MulEquiv.refl _ }
  exact ThompsonImage.hypothesis U q (QuotientGroup.mk'_surjective C)
    (QuotientGroup.ker_mk' C) hU.quotient_pCore_eq_bot c

/-- The literal nontrivial Thompson image has the complete adequate B.5.6
 alternatives. Only the independently constructed local overgroup is required. -/
theorem hstar_overgroup_thompson_classification
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    ChapterB.SourceInduction.NontrivialAdequateAlternative (ρ.comp J.subtype) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
  have hne : J ≠ ⊥ := by
    intro hb
    apply h.hstar_overgroup_thompson_moves_omega hout hH hZH hHX
    have hJ : elementaryAbelianMaxJ (⊤ : Subgroup X) ≤ C := by
      rw [← QuotientGroup.ker_mk' C]
      exact (Subgroup.map_eq_bot_iff _).mp hb
    exact (elementaryAbelianMaxJ_sylow_le_top
      (T.subtype (hH.1.1.2.trans hHX))).trans hJ
  let : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hne
  exact ChapterB.SourceInduction.nontrivialAdequateAlternative_knownSimple _
    (h.overgroup_thompson_hypothesis hX)

/-- The literal residual image lies in `J(X)*`, using its normality and the
 source identity `O²(H) = [O²(H), J(T)]`. -/
theorem hstar_residual_image_le_overgroup_thompson
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    (pResidual 2 H).map (q.comp (inclusion hHX)) ≤
      (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
  let : J.Normal := ThompsonImage.normal U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let S := T.subtype (hH.1.1.2.trans hHX)
  let f := inclusion hHX
  have hs : ((T.subtype hH.1.1.2 : Subgroup H).map f) = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_map]
    have he : X.subtype.comp f = H.subtype := rfl
    rw [he]
    exact (map_subgroupOf_eq_of_le hH.1.1.2).trans
      (map_subgroupOf_eq_of_le (hH.1.1.2.trans hHX)).symm
  have hj : (elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)).map f =
      elementaryAbelianMaxJ (S : Subgroup X) := by
    rw [← elementaryAbelianMaxJ_map_injective f (inclusion_injective hHX), hs]
  have hJimage : (elementaryAbelianMaxJ (S : Subgroup X)).map q ≤ J :=
    map_mono (elementaryAbelianMaxJ_sylow_le_top S)
  have hres := h.hstar_residual_eq_thompson_commutator hout hH hZH
  change (pResidual 2 H).map (q.comp f) ≤ J
  rw [hres, map_commutator, ← map_map, ← map_map, hj]
  exact (commutator_mono le_rfl hJimage).trans (commutator_le_right _ _)

/-- Conjugation by the original quotient permutes the two factors whenever
 B.5.6 takes its two-factor alternative on the literal Thompson image. -/
theorem hstar_overgroup_factor_permutation
    (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    letI : J.Normal := ThompsonImage.normal U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ (d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp J.subtype)) (x : X ⧸ C),
      (d.first.map (MulAut.conjNormal x).toMonoidHom = d.first ∧
        d.second.map (MulAut.conjNormal x).toMonoidHom = d.second) ∨
      (d.first.map (MulAut.conjNormal x).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal x).toMonoidHom = d.first) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
  let : J.Normal := ThompsonImage.normal U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  exact fun d x => d.automorphism_permutation (h.overgroup_thompson_hypothesis hX).twoCore
    (MulAut.conjNormal x)

/-- The rank-one selection API applies to the same literal Thompson image. -/
theorem hstar_overgroup_rank_one_mem_factor
    (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    ∀ (d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp J.subtype)) (t : J),
      Module.finrank (ZMod 2) (LinearMap.range ((ρ.comp J.subtype) t - LinearMap.id)) ≤ 1 →
      t ∈ d.first ∨ t ∈ d.second := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  exact fun d t hr => d.rank_one_mem_factor t hr

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
