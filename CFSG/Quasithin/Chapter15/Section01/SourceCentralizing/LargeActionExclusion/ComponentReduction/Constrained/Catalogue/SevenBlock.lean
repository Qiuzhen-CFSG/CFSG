module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SmallAlternating
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.MovedAction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Restriction

/-!
# Whole A₇ block reconstruction from the original normalizer action

The actual image of K on the central-involution span in H = K N_S(K)
is A₇. Its generalized Fitting identification makes it self-centralizing,
so the full B.5 action theorem identifies the entire moved subgroup and
its fixed complement. C.1.24 reconstructs the ordinary or exceptional
block on K itself. The original Baumann characteristic-normalizer bound
and K not contained in M exclude its normal characteristic-subgroup
alternative. No block, whole-core, or ambient C-component premise is added.

Both reconstructed blocks have centerless two-core quotient. Consequently
the original FF comparison is bijective, and its A₇ marking agrees on
every element with the original map. This excludes a cubic covering
kernel without assuming its triviality. The selected-component exports
retain both original primes, and the exchanged export retains either
plane size. The actual-marker consumer retains its original selection.

Exceptional-block exclusion, A₇ weight-two and partition placement, the
other small rows, general-family Borel placement and catalogue exhaustion
remain with this owner. Original 15.1.14 retains its existing producer
and final assembly owner.

Source: Aschbacher--Smith 15.1.20(2b), printed pp.1094--1095;
B.5.1 and C.1.24(a), printed pp.99--103 and130--131.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterB
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter14.Section06.Seven.Reconstruction
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The full original A₇ action, including its entire moved module. -/
theorem NormalizerAction.seven_actionData
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hsq : IsSQTK KnownSimple.IsKnownSimple K)
    (e : d.normalizerImage K ≃* alternatingGroup (Fin 7)) :
    letI := a.reduced.elementary
    let H := K ⊔ d.normalizerSylow K
    let U := d.normalizerModule K
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    Nonempty (AlternatingModels.ActionData
      (NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _)) (d.normalizerImage K)) := by
  let := a.reduced.elementary
  let H := K ⊔ d.normalizerSylow K
  let U := d.normalizerModule K
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let B := K.subgroupOf H
  let C := d.normalizerImage K
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple C := a.quasisimple
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  have hz : center C = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : e x ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hh
    exact e.injective (by simpa using hh)
  have hc : centralizer (C : Set (H ⧸ centralizer (U : Set H))) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxC : x ∈ C := by
      rw [show C = generalizedFitting _ from a.fitting] at hx ⊢
      exact centralizer_generalizedFitting_le _ hx
    have hxz : (⟨x,hxC⟩ : C) ∈ center C := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hz] at hxz
    exact congrArg Subtype.val hxz
  have hsqC : IsSQTK KnownSimple.IsKnownSimple C :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) hsq
      (ChapterA.Section02.IsSectionOf.of_surjective (d.toNormalizerImage K)
        (d.toNormalizerImage_surjective K))
  exact AlternatingModels.nonempty_actionData _ _ e hc hsqC
    (NormalElementaryQuotient.representation_injective U q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (a.source_classification hsq).1

/-- Reconstruct the ordinary or exceptional A₇ block on the original local member. -/
theorem localFamily_seven_blocks (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : d.normalizerImage K ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock K 7 ∨ IsExceptionalA7Block K := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  have hn := d.localFamily_alternating_central_normalizes hG h hK hq (by decide)
    (a.alternating_coreCenterEquiv hq (by decide) e)
  let := h.elementary
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hsqK := (IsSQTK.equiv (subgroupOfEquivOfLe hK.1)).mp (hsq.subgroup (K.subgroupOf d.G1))
  let H := K ⊔ d.normalizerSylow K
  let B := K.subgroupOf H
  let U := d.normalizerModule K
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  let := a.reduced.elementary
  let : IsElementaryAbelian 2 (⁅U,B⁆ : Subgroup H) :=
    IsElementaryAbelian.of_le (commutator_le_left U B)
  have hB : B.IsCComponent := hK.2.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let b : B ≃* K := subgroupOfEquivOfLe le_sup_left
  let := hq
  let : IsQuasisimple (B ⧸ pCore 2 B) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm
  have hfB : generalizedFitting B = pCore 2 B := by
    apply map_injective (f := b.toMonoidHom) b.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hf]
  obtain ⟨P,hP,hfitH,hres,_,_⟩ :=
    d.localFamily_normalizer_seed_setup hG hempty hM hJ hu h hK hq hout hf
  have hgen : B ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hprod : ∀ g : H, ∃ k ∈ B, ∃ t ∈ (P : Subgroup H), k*t=g := by
    intro g
    exact mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
  have hcpu := d.localFamily_baumann_control hG hM hJ h (inf_le_left.trans hn) P hP
  have hno : ∀ D : Subgroup (baumann (P : Subgroup H)),
      D.Characteristic → D ≠ ⊥ → ¬ (D.map (baumann (P : Subgroup H)).subtype).Normal := by
    intro D hD hne hnormal
    let := hD
    let := hnormal
    have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
      calc
        ⊤ = normalizer (D.map (baumann (P : Subgroup H)).subtype : Set H) := by rw [normalizer_eq_top]
        _ ≤ (baumann (P : Subgroup H)).characteristicNormalizerClosure :=
          normalizer_le_characteristicNormalizerClosure _ D hne
        _ ≤ M.subgroupOf H := hcpu
    apply d.localFamily_not_le_M hG hempty hM hu hK hout
    intro k hk
    exact htop (show (⟨k,mem_sup_left hk⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)
  obtain ⟨m⟩ := a.seven_actionData hsqK e
  have hw := moved_wholeModule U B q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) m e
  have hm : ⁅⁅U,B⁆,B⁆ = ⁅U,B⁆ := by
    change pResidual 2 H = B at hres
    rw [←hres]
    exact commutator_isPPerfect_idempotent _ U (isPPerfect_pResidual 2)
      (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  have hb := block_types_of_wholeModule B ⁅U,B⁆ hB hfitH hfB P hprod hno hm hw.1 hw.2
  exact hb.imp (RankOne.Solvable.isAlternatingBlock_of_equiv b)
    (RankOne.ExceptionalSevenControl.exceptional_of_equiv b)


/-- Both reconstructed seven-letter blocks have centerless two-core quotient.
Thus the original FF comparison has no remaining central covering kernel. -/
private theorem seven_core_bijective
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hb : IsAlternatingBlock K 7 ∨ IsExceptionalA7Block K) :
    Function.Bijective a.coreToImage := by
  have he : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) := by
    rcases hb with hb | hb
    · obtain ⟨_,⟨m⟩,_⟩ := hb.2.2
      exact ⟨m.quotientIso⟩
    · exact hb.2.1
  obtain ⟨t⟩ := he
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : t x ∈ center (alternatingGroup (Fin 7)) := (centerCongr t ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hh
    exact t.injective (by simpa using hh)
  exact ⟨(MonoidHom.ker_eq_bot_iff _).mp
    (bot_unique ((a.coreToImage_ker_central hq).trans_eq hz)),a.coreToImage_surjective⟩

/-- Reconstruction also recovers the literal two-core quotient, compatibly
with the original FF map. A cubic covering kernel is thereby excluded. -/
theorem localFamily_seven_marked_blocks (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : d.normalizerImage K ≃* alternatingGroup (Fin 7)) :
    (IsAlternatingBlock K 7 ∨ IsExceptionalA7Block K) ∧
      ∃ t : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
        ∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = e (d.toNormalizerImage K k) := by
  have hb := d.localFamily_seven_blocks hG hempty hM hJ hu h hK hq hout hf e
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let t := (MulEquiv.ofBijective a.coreToImage (seven_core_bijective a hq hb)).trans e
  exact ⟨hb,t,fun _ => rfl⟩

/-- The original selected A₇ FF row now reconstructs the whole block and
its marked two-core quotient, for either source prime. -/
theorem PreExclusionSource.constrained_seven_blocks
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    (IsAlternatingBlock d.L 7 ∨ IsExceptionalA7Block d.L) ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k) :=
  d.localFamily_seven_marked_blocks hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf e

/-- The same whole-block recognition applies after exchanged selection,
preserving the original component and its actual FF marking. -/
theorem ExchangedSource.constrained_seven_blocks
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    (IsAlternatingBlock d.L 7 ∨ IsExceptionalA7Block d.L) ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k) :=
  d.localFamily_seven_marked_blocks hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf e

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Whole A₇ block recognition at the actual original marker, retaining
its prime, row and quotient marking. Original 15.1.14 remains explicit. -/
theorem PreparedChosenModule.source_preExclusion_constrained_seven_blocks
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7),
          (ChapterC.IsAlternatingBlock d.L 7 ∨ ChapterC.IsExceptionalA7Block d.L) ∧
            ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
              ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) =
                e (d.toNormalizerImage d.L k)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_seven_blocks (h := h) hG hempty hM hJ hu hf e⟩

end CFSG.Quasithin.Chapter15.Section01
