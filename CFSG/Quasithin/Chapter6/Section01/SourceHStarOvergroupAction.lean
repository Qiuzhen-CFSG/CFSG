module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The B.5.6 action on the enlarged H-star omega orbit

For an overgroup `X` of the original Sylow subgroup in `H(T)`, the actual
orbit `U = ⟨Ω₁(Z(T))ˣ⟩` is reduced. Its centralizer quotient acts faithfully
on `U`, and the original group `X` supplies the SQTK cover required by
B.5.3. Restriction to the offender subgroup therefore gives the complete
adequate B.5.6 alternatives.

If `X` contains an H-star subgroup moving the original omega-center,
Thompson movement transfers along the literal subgroup inclusion. The
quotient action is then FF and the classified actor is nontrivial. Finally
`O²(H) = [O²(H), J(T)]` puts its actual image in that actor.

In source 6.1.5 take `X = ⟨D_L,H⟩`. Membership of this join in `H(T)` is
the earlier 5.1.7(2)(iii) input; the factor/Hall-action and symmetric-seven
endgame remain separate source obligations. No minimal-parabolic condition
on `X` or generation of all of `X/C_X(U)` by offenders is asserted.

Source: Aschbacher--Smith, 6.1.5, printed pp.666--668, and B.2.7, B.5.3--6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H X : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- B.2.14 on the original omega orbit in the enlarged local overgroup. -/
theorem overgroup_omega_orbit_reduced
    (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    IsPReduced 2 ((conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X) := by
  let S := T.subtype hX.2
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hz : omegaOneCenterAmbient (S : Subgroup X) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [← omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le (hZT.trans hX.2)]
    congr 1
    exact map_subgroupOf_eq_of_le hX.2
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hX)
  have hr := omegaCenter_normalClosure_reduced S hc
  rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ X (hZT.trans hX.2)] at hr
  exact hr

/-- The same Sylow Thompson subgroup still moves the enlarged orbit. -/
theorem hstar_overgroup_thompson_moves_omega
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) :
    ¬ elementaryAbelianMaxJ (T.subtype (hH.1.1.2.trans hHX) : Subgroup X) ≤
      centralizer (((conjugateSpanBy
        (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X) : Set X) := by
  have hmove := (h.rankOneInput hout).hstar_thompson_moves_omega_orbit
    (h.maximal_eq_normalizer_L ▸ hH) hZH
  intro hc
  apply hmove
  let f := inclusion hHX
  have hf : Function.Injective f := inclusion_injective hHX
  have hs : ((T.subtype hH.1.1.2 : Subgroup H).map f) =
      (T.subtype (hH.1.1.2.trans hHX) : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_map]
    have he : X.subtype.comp f = H.subtype := rfl
    rw [he]
    exact (map_subgroupOf_eq_of_le hH.1.1.2).trans
      (map_subgroupOf_eq_of_le (hH.1.1.2.trans hHX)).symm
  have hj : (elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)).map f =
      elementaryAbelianMaxJ (T.subtype (hH.1.1.2.trans hHX) : Subgroup X) := by
    rw [← elementaryAbelianMaxJ_map_injective f hf, hs]
  intro j hjH u hu
  have hjX := mem_map_of_mem f hjH
  rw [hj] at hjX
  have huX : f u ∈ (conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X :=
    conjugateSpanBy_mono le_rfl hHX hu
  exact hf (hc hjX (f u) huX)

/-- Every B.5.3 premise is constructed on the actual offender subgroup. -/
theorem overgroup_offender_hypothesis
    (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple
      (ρ.comp (offenderSubgroup ρ).subtype) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (X ⧸ C) := {
    Cover := X
    kernel := C
    sqtk := Chapter3.sqtk_of_mem_H h.simpleQTKE hX.1
    equiv := MulEquiv.refl _ }
  exact ChapterB.SourceInduction.offenderSubgroup_hypothesis ρ
    (NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C))
    hU.quotient_pCore_eq_bot c

/-- The noncentral H-star branch supplies the genuine nontrivial B.5.6 action. -/
theorem hstar_overgroup_offender_classification
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
    IsFFModule ρ ∧ ChapterB.SourceInduction.NontrivialAdequateAlternative
      (ρ.comp (offenderSubgroup ρ).subtype) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let S := T.subtype (hH.1.1.2.trans hHX)
  have hmove := h.hstar_overgroup_thompson_moves_omega hout hH hZH hHX
  have hff : IsFFModule ρ := by
    obtain hf | ⟨_, hff, _, _, _⟩ := ChapterB.lemma_B_2_7 U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) S
    · exact (hmove ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
    · exact hff
  let : Nontrivial (offenderSubgroup ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (offenderSubgroup_ne_bot_of_ff ρ hff)
  exact ⟨hff, ChapterB.SourceInduction.nontrivialAdequateAlternative_knownSimple _
    (h.overgroup_offender_hypothesis hX)⟩
/-- The original residual image belongs to the classified actor, with the
literal inclusion and quotient map used in 6.1.5. -/
theorem hstar_residual_image_le_overgroup_offender
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
    (pResidual 2 H).map (q.comp (inclusion hHX)) ≤ offenderSubgroup ρ := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
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
  have hmove := h.hstar_overgroup_thompson_moves_omega hout hH hZH hHX
  have hJimage : (elementaryAbelianMaxJ (S : Subgroup X)).map q ≤ offenderSubgroup ρ := by
    obtain hc | ⟨_, _, _, he, hle⟩ := ChapterB.lemma_B_2_7 U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) S
    · exact (hmove ((elementaryAbelianMaxJ_sylow_le_top S).trans hc.1)).elim
    · exact (map_mono (elementaryAbelianMaxJ_sylow_le_top S)).trans (he ▸ hle)
  have hres := h.hstar_residual_eq_thompson_commutator hout hH hZH
  let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
  change (pResidual 2 H).map (q.comp f) ≤ offenderSubgroup ρ
  rw [hres, map_commutator, ← map_map, ← map_map, hj]
  exact (commutator_mono le_rfl hJimage).trans (commutator_le_right _ _)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
