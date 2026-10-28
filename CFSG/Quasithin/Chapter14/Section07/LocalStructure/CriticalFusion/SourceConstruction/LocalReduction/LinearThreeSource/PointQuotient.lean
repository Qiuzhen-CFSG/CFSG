module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.Movement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Quotients

/-!
# The actual full point quotient in the remaining linear-three row

If the original point core centralizes the plane, the faithful-component
list gives only A₅ and SL₃(2) at the full point normalizer. The original
local SL₃(2) component embeds there with two-group kernel on the quotient,
so its order 168 excludes A₅. The original Sylow supplement and point
parabolic then recover the full point quotient, with the whole two-core.

This is a reduction under contrary centrality, not an exclusion of that
case. In particular no natural-module clause is inferred from the earlier
faithful quotient list, and no downstream Data record is used.
Source: Aschbacher--Smith 13.3.14(a),(e), 14.3.4(1--2), and 14.7.48--49,
printed pp.891--892,990,1064.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Source reduction (a) on the original natural flag and complete point
core. The span and point group are the literal original subgroups. -/
theorem original_point_span_le_omega_of_plane_centralized
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hc : ⁅F.Vi 2,F.H.pCoreIn 2⁆ = ⊥) :
    F.U ≤ omegaOneCenterAmbient (F.H.pCoreIn 2) := by
  let := h.chosen.elementary
  let := IsElementaryAbelian.of_le (p := 2) (F.le_seed 2)
  have hVH : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  let := IsElementaryAbelian.of_surjective (p := 2)
    (F.tildeMap V hVH) (F.tildeMap_surjective V hVH)
  have hp : F.Vi 1 ≠ ⊥ := by
    intro he
    have hh := F.card 1 (by decide)
    simp [he] at hh
  have htwo : IsTwoLocal F.H := ⟨F.Vi 1,hp,
    T.isPGroup'.to_le ((F.le_seed 1).trans h.chosen.le_sylow),rfl⟩
  have hHe : F.H ∈ Chapter1.He G := Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.source.simpleQTKE.toIsQTKE.evenCharacteristic T) htwo (F.invariant 1)
  have hgen : V = conjugateSpanBy (F.Vi 2) (F.Li L 1) :=
    (F.seed_eq_plane_span L (by decide) h.chosen.normalizes
      (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))).symm
  exact (Chapter13.Section03.Noncentrality.reduction_a (F.Vi 2) V (F.Li L 1) F.H
    ((F.le_seed 2).trans hVH) ((F.Li_le L 1).trans inf_le_right) hgen hHe hc).2

/-- Contrary plane centrality and an actual local linear-three component
determine the quotient of the full original point normalizer. -/
theorem full_point_quotient_of_linear_three_and_plane_centralized_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ⁅F.Vi 2,F.H.pCoreIn 2⁆ = ⊥) :
    Nonempty (HStar F.H ≃* Matrix.PSL3Two.PSL) := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨D,hD,_,_⟩ := GuardedSource.local_exists_quasisimple_component
    d h hab structural previous faithful earlier F.H hH
  have hCr := (local_component_eq_residual_at d h hab structural previous faithful
    earlier source47 I hI C hC).1
  obtain ⟨hDr,hgen,_⟩ := local_component_eq_residual_at d h hab structural previous
    faithful earlier source47 F.H hH D hD
  let i : I →* F.H := inclusion hI.2.1
  have hCD : C.map i ≤ D := by
    rw [←hCr,←hDr]
    exact map_pResidual_le 2 i
  let j : C →* D := (i.comp C.subtype).codRestrict D (fun c =>
    hCD (mem_map_of_mem i c.property))
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    apply inclusion_injective hI.2.1
    exact congrArg Subtype.val he
  let f := (QuotientGroup.mk' (pCore 2 D)).comp j
  have hk : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective j hj
  have hdiv := f.pCoreQuotient_card_dvd_of_isPGroup_ker 2 hk
  have hcard : Nat.card (C ⧸ pCore 2 C) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL
  have hmodel : Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) := by
    rcases component_small_of_plane_centralized_at h structural previous faithful hc D hD with
      ha | ha
    · obtain ⟨a⟩ := ha
      have hDa : Nat.card (D ⧸ pCore 2 D) = 60 := by
        rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
        norm_num
      rw [hcard,hDa] at hdiv
      norm_num at hdiv
    · exact ha
  obtain ⟨a⟩ := hmodel
  let b := D.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hn : ((D.map F.H.subtype).subgroupOf F.H).Normal := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using
      local_component_normal_at h structural source47 F.H hH D hD
  exact InnerLinearExclusion.linearThree_full_quotient_at h structural F.H
    (D.map F.H.subtype) hH (map_subtype_le _) hn hgen.symm (q.symm.trans a)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
