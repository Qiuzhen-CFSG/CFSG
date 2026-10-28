module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NormalCubic

/-!
# Cubic exclusion for the actual terminal action with a two-group kernel

The original cubic-index contradiction only requires the dotted action
kernel to be a two-group. This form applies to the degree-two branch once
the small-center action proves that kernel property, including when the
center is larger than the marked point.

Source: Aschbacher--Smith 14.3.13 and 14.3.15, printed pp.993--995.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual source cubic-index theorem excludes a normal cubic subgroup
in the dotted action, without classifying a linear normalizer. -/
theorem no_normal_cubic_of_two_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F)
    (hk2 : IsPGroup 2 F.terminalHatAction.ker)
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : Nat.card C = 3) : False := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let R := (T : Subgroup G).subgroupOf F.H
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hR : IsPGroup 2 R := T.isPGroup'.comap_subtype
  have hk : q.ker ≤ R := by
    rw [QuotientGroup.ker_mk']
    exact hk2.le_sylow_of_normal (T.subtype hTH)
  let J₀ := (C ⊔ R.map q).comap q
  let J := J₀.map F.H.subtype
  have hRJ : R ≤ J₀ := fun x hx => (show R.map q ≤ C ⊔ R.map q from le_sup_right)
    (mem_map_of_mem q hx)
  have hmapR : R.map F.H.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hTH
  have hTJ : (T : Subgroup G) ≤ J := hmapR ▸ map_mono hRJ
  have hJH : J ≤ F.H := map_subtype_le _
  have hJmem : J ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTJ hJH
      ⟨(h.pointNormalizer_mem_Hz F).1.1, F.invariant 1⟩
  have hindex : (T : Subgroup G).relIndex J = 3 := by
    rw [← hmapR]
    change (R.map F.H.subtype).relIndex (J₀.map F.H.subtype) = _
    rw [relIndex_map_map_of_injective _ _ F.H.subtype_injective]
    exact normal_cubic_preimage_relIndex q (QuotientGroup.mk'_surjective _) R hR hk C hC
  have hJM : J ≤ M := by
    by_contra hout
    exact hnot (SolvableAmalgam.source_theoremE_of_index_three hG T hempty hM hu hmany
      hcard e J hJmem hout hindex)
  have hline : finrank (ZMod 2) (hatSpace F (rankTwoSeed T M)) = 1 := by
    have hh := finrank_hatSpace_plane F (by decide) d.seed_center
    exact (congrArg (fun A : Subgroup G => finrank (ZMod 2) (hatSpace F A)) F.last).symm.trans hh
  let S := hatSpace F (rankTwoSeed T M)
  have hS : 0 < finrank (ZMod 2) S := by rw [hline]; decide
  let : Nontrivial S := Module.nontrivial_of_finrank_pos hS
  obtain ⟨v, hv⟩ := exists_ne (0 : S)
  have hv0 : (v : Additive F.Uhat) ≠ 0 := fun he => hv (Subtype.ext he)
  have hspan : S = Submodule.span (ZMod 2) {(v : Additive F.Uhat)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hline v.property hv0
  have hfix (c : C) : F.terminalRepresentation c (v : Additive F.Uhat) = v := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker (c : F.TerminalHdot)
    have haJ : a ∈ J₀ := by change q a ∈ C ⊔ R.map q; rw [ha]; exact (show C ≤ C ⊔ R.map q from le_sup_left) c.property
    have haM : (a : G) ∈ M := hJM (mem_map_of_mem _ haJ)
    have hastable : F.terminalRepresentation c (v : Additive F.Uhat) ∈ S := by
      change (F.terminalRepresentation c (v : Additive F.Uhat)).toMul ∈ hatImage F (rankTwoSeed T M)
      obtain ⟨u, hu, he⟩ := v.property
      rw [←ha, F.terminalRepresentation_apply_mk, ←he, F.terminalHatAction_apply_mk]
      refine ⟨_, ?_, rfl⟩
      exact (mem_normalizer_iff.mp (RankTwoHypothesis.M_normalizes_seed haM) (u : G)).mp hu
    have hanonzero : F.terminalRepresentation c (v : Additive F.Uhat) ≠ 0 := by
      intro he
      apply hv0
      have hh := congrArg (F.terminalRepresentation (c : F.TerminalHdot)⁻¹) he
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, map_zero] using hh
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp (hspan.le hastable)
    have hb0 : b ≠ 0 := by intro hh; exact hanonzero (by simpa [hh] using hb.symm)
    have hb1 : b = 1 := (by decide : ∀ b : ZMod 2, b ≠ 0 → b = 1) b hb0
    simpa [hb1] using hb.symm
  have horbit := terminal_orbit_span F (v : Additive F.Uhat)
    (hspan.symm.trans (congrArg (fun A : Subgroup G => hatSpace F A) F.last).symm)
  let D := Representation.fixedSubrepresentationOfNormal F.terminalRepresentation C
  have hvD : (v : Additive F.Uhat) ∈ D := hfix
  have htop : D.toSubmodule = ⊤ := by
    apply top_unique
    rw [← horbit]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact D.apply_mem_toSubmodule a hvD
  have hker : C ≤ F.terminalRepresentation.ker := by
    intro c hc
    apply LinearMap.ext
    intro w
    have hw : w ∈ D := by change w ∈ D.toSubmodule; rw [htop]; trivial
    exact hw ⟨c,hc⟩
  have hbot : C = ⊥ := bot_unique (hker.trans_eq
      ((MonoidHom.ker_eq_bot_iff _).mpr F.terminalRepresentation_injective))
  simp [hbot] at hC

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
