module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonParabolicEscape
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.Placement
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# The nonabelian core obstruction in the original residual escape

In the centralizing branch, an outside minimal parabolic has no noncentral
reduced normal elementary subgroup: source ordering and Baumann control would
place it in M. An abelian two-core is therefore impossible, since its first
omega subgroup detects its centralizer and is reduced.

More generally, B.6.8 makes every normal elementary subgroup centralized by
O₂ also centralized by O². Apply this to Ω₁Z(O₂), then to the actual parabolic
selected under failure of15.1.14(1). The same witness still moves the original
C_V(J₁(T)); its unresolved action is confined to the nonabelian-core case.
This is a necessary source reduction, not the residual containment itself.

Source: Aschbacher--Smith15.1.14(1), printed p.1091, using B.6.8(4),(6c),
source14.1.4 ordering, and15.1.9 Baumann control.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- An abelian two-core excludes an outside minimal parabolic in the actual source setup. -/
theorem source_abelian_core_minimalParabolic_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M P : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hP : P ∈ Chapter1.HOver G (T : Set G))
    (hpar : ChapterB.IsMinimalParabolicOver T P)
    [IsMulCommutative (pCore 2 P)] : P ≤ M := by
  let Q := pCore 2 P
  let U := (omega Q (p := 2) 1).map Q.subtype
  let : (omega Q (p := 2) 1).Characteristic := omega_characteristic Q 1
  let : U.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 (omega Q (p := 2) 1) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative Q
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map Q.subtype
  have hQ : centralizer (Q : Set P) ≤ Q :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hP)
  have hCU : centralizer (U : Set P) = Q := by
    apply le_antisymm (OmegaAction.centralizer_omegaOne_pCore_le hQ)
    exact Q.le_centralizer.trans (centralizer_le (map_subtype_le _))
  have hred : IsPReduced 2 U := by
    refine ⟨inferInstance,inferInstance,?_⟩
    let e := QuotientGroup.quotientMulEquivOfEq hCU
    rw [← pCore_map_iso 2 e.symm, pCore_quotient_pCore_eq_bot, Subgroup.map_bot]
  apply source_noncentral_reduced_minimalParabolic_le hG T hempty hM hJ hP hpar U hred
  intro htop
  have he : Q = ⊤ := hCU.symm.trans htop
  have htwo : IsPGroup 2 P := by
    have hh : IsPGroup 2 Q := pCore_isPGroup
    rw [he] at hh
    exact hh.of_equiv topEquiv
  have hTP : (T : Subgroup G) = P := by
    exact (T.is_maximal' htwo hP.2).symm
  exact hpar.2 (hTP ▸ P.le_normalizer)

/-- The outside residual fixes every normal elementary subgroup centralized by its two-core. -/
theorem source_outside_minimalParabolic_residual_centralizes_elementary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M P : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hP : P ∈ Chapter1.HOver G (T : Set G))
    (hpar : ChapterB.IsMinimalParabolicOver T P) (hPM : ¬ P ≤ M)
    (U : Subgroup P) [U.Normal] [IsElementaryAbelian 2 U]
    (hQU : pCore 2 P ≤ centralizer (U : Set P)) :
    pResidual 2 P ≤ centralizer (U : Set P) := by
  let S := T.subtype hP.2
  obtain ⟨B,hTB,hBH⟩ := hpar.1.2.exists
  have hi := (ChapterB.intrinsic_minimalParabolic T P B hpar hTB hBH).1
  rcases normal_le_core_or_sup_eq_top_of_uniqueMaximal (N := centralizer (U : Set P)) hi.1
    ⟨(ChapterB.minimalParabolicMax_spec S hi).2,
      (ChapterB.minimalParabolicMax_spec S hi).1⟩ with hc | hr
  · have hred : IsPReduced 2 U := ⟨inferInstance,inferInstance,
      ChapterB.minimalParabolic_quotient_twoCore_eq_bot_of_kernel S hi _
        (hc.trans (Subgroup.normalCore_le _)) hQU⟩
    have hcent : centralizer (U : Set P) = ⊤ := by
      by_contra hn
      exact hPM (source_noncentral_reduced_minimalParabolic_le
        hG T hempty hM hJ hP hpar U hred hn)
    exact hcent ▸ le_top
  · apply (pResidual_le_iff_isPGroup_quotient 2 _).mpr
    exact isPGroup_quotient_of_sup_eq_top _ S S.isPGroup' (by simpa only [sup_comm] using hr)

/-- In particular, the outside residual centralizes the first omega of its two-core center. -/
theorem source_outside_minimalParabolic_residual_centralizes_core_omega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M P : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hP : P ∈ Chapter1.HOver G (T : Set G))
    (hpar : ChapterB.IsMinimalParabolicOver T P) (hPM : ¬ P ≤ M) :
    pResidual 2 P ≤ centralizer (omegaCenterIn (pCore 2 P) : Set P) := by
  let U := omegaCenterIn (pCore 2 P)
  let : U.Normal := normalizer_eq_top_iff.mp (top_unique (by
    have hn := normalizer_le_normalizer_omegaCenterIn (pCore 2 P)
    rwa [normalizer_eq_top] at hn))
  apply source_outside_minimalParabolic_residual_centralizes_elementary
    hG T hempty hM hJ hP hpar hPM U
  apply le_centralizer_iff.mp
  intro u hu
  exact (mem_omegaCenterIn_iff _ _ |>.mp hu).2.1

/-- Failure of the original residual containment has a witness with nonabelian two-core
and trivial residual action on its central omega subgroup. The original moved fixed subgroup
and all ambient inclusions are retained. -/
theorem PreparedChosenModule.thompsonFixed_moving_nonabelian_parabolic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ P : Subgroup G, P ≤ centralizer (centralInvolutions T : Set G) ∧
      P ∈ Chapter1.HOver G (T : Set G) ∧ ChapterB.IsMinimalParabolicOver T P ∧
      IsSQTK KnownSimple.IsKnownSimple P ∧ generalizedFitting P = pCore 2 P ∧
      ¬ P ≤ M ∧ ¬ IsMulCommutative (pCore 2 P) ∧
      pResidual 2 P ≤ centralizer (omegaCenterIn (pCore 2 P) : Set P) ∧
      (∀ U : Subgroup P, IsPReduced 2 U → centralizer (U : Set P) = ⊤) ∧
      ¬ (pResidual 2 P).map P.subtype ≤ centralizer (thompsonFixed T V : Set G) := by
  obtain ⟨P,hPC,hPH,hP,hSQ,hF,hPM,hres,_⟩ :=
    h.thompsonFixed_moving_minimalParabolic hG T hM hJ hnot
  refine ⟨P,hPC,hPH,hP,hSQ,hF,hPM,?_,
    source_outside_minimalParabolic_residual_centralizes_core_omega hG T hempty hM hJ hPH hP hPM,
    ?_,hres⟩
  · intro hc
    let := hc
    exact hPM (source_abelian_core_minimalParabolic_le hG T hempty hM hJ hPH hP)
  · intro U hU
    by_contra hn
    exact hPM (source_noncentral_reduced_minimalParabolic_le hG T hempty hM hJ hPH hP U hU hn)
end CFSG.Quasithin.Chapter15.Section01
