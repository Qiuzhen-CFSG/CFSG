module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenWeakClosure
public import Theory.GroupTheory.ConjugateCoreIntersection
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations

/-!
# Hyperplane control from the partner core and plane uniqueness

Every hyperplane of the chosen four-space meets its distinguished plane.
Uniqueness 15.2.15 therefore places its centralizer in Mc. Applying this to
all M-conjugates places the same centralizer in every M-conjugate of Mc.
Once V ≤ O₂(Mc) is known, their two-cores have a nontrivial M-invariant
intersection. Its normalizer is M by maximal two-locality, proving `r > 1`.

This is an alternative order of the arguments in Aschbacher--Smith 15.2.26
and 15.2.27, printed pp.1118--1119. The proof of 15.2.27(2) does not use
15.2.26. Its core conclusion remains an explicit prerequisite here.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section02

open ChapterD ChapterE

variable {G : Type*} [Group G] [Finite G]

private theorem plane_inf_hyperplane_ne_bot
    (V Z U : Subgroup G) [IsElementaryAbelian 2 V]
    (hZV : Z ≤ V) (hZ : Nat.card Z = 4) (hU : subgroupCorank V U = 1) :
    Z ⊓ U ≠ ⊥ := by
  have hi : U.relIndex V = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank,
      hU, pow_one]
  have hb := relIndex_le_of_le_right (H := U) hZV (by omega : U.relIndex V ≠ 0)
  intro he
  rw [← inf_relIndex_left Z U, he, relIndex_bot_left, hZ, hi] at hb
  omega

/-- Plane uniqueness controls hyperplane centralizers inside Mc before
any claim about their normalization of V is made. -/
theorem source_chosen_hyperplane_centralizer_le_partner
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (U : Subgroup G) (hU : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ Mc := by
  let := h.prepared.elementary
  have hn := plane_inf_hyperplane_ne_bot V ZS U hgeo.plane_le hgeo.plane_card hU
  exact (centralizer_le (show ZS ⊓ U ≤ U from inf_le_right)).trans
    ((Subgroup.centralizer_le_normalizer _).trans
      (source_chosen_plane_subgroup_normalizer h hgeo hu inf_le_left hn))

/-- The source core containment discharges the entire hyperplane-centralizer
input, including the Sz(2) action, by the invariant intersection of cores. -/
theorem source_chosen_hyperplane_centralizer_of_core
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hcore : V ≤ twoCoreIn Mc)
    (U : Subgroup G) (hU : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  have hnQ : Mc ≤ normalizer (twoCoreIn Mc : Set G) := by
    simpa only [twoCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 Mc).le_normalizer_map Mc.subtype
  rw [h.normalizer_eq]
  apply le_trans _ (iInf_conjugates_le_of_invariant_two_subgroup M Mc
    (twoCoreIn Mc) V h.maximal.1.1 (isPGroup_pCoreIn 2 Mc) hnQ hcore
    h.prepared.nontrivial h.prepared.normalized)
  apply le_iInf
  intro m
  have hv : V.map (MulAut.conj (m : G)⁻¹).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (h.prepared.normalized (M.inv_mem m.property))
  have hcor : subgroupCorank V (U.map (MulAut.conj (m : G)⁻¹).toMonoidHom) = 1 := by
    rw [← hv, subgroupCorank, relIndex_map_map_of_injective _ _ (MulAut.conj (m : G)⁻¹).injective]
    exact hU
  have hc := map_mono (f := (MulAut.conj (m : G)).toMonoidHom)
    (source_chosen_hyperplane_centralizer_le_partner h hgeo hu
      (U.map (MulAut.conj (m : G)⁻¹).toMonoidHom) hcor)
  rw [offender_centralizer_map] at hc
  have hinv := offender_map_conj_inverse U (m : G)⁻¹
  rw [inv_inv] at hinv
  rwa [hinv] at hc

/-- The `r > 1` conclusion of 15.2.26 follows without an additional
hyperplane model calculation after the independent partner-core argument. -/
theorem source_chosen_globalR_gt_one_of_core
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hcore : V ≤ twoCoreIn Mc) : 1 < globalR V := by
  let := h.prepared.elementary
  exact one_lt_globalR_of_hyperplane_centralizers V
    (fun U _ hU => source_chosen_hyperplane_centralizer_of_core h hgeo hu hcore U hU)

end CFSG.Quasithin.Chapter15.Section02
