module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Reduction
public import Theory.GroupTheory.SpecificGroups.DihedralEightFourCenter

/-!
# The marked four-center geometry in original 14.3.20

For the same marked point d, strict enlargement of the elementary factor's
centralizer makes D = O₂(H) ∩ C_G(U) dihedral of order eight. The kernel of
the action on U/Z(U) is O₂(H), so C_T(U) lies in D. Since U lies in C_T(d),
every central element of C_T(d) lies in C_D(d) = ⟨z,d⟩. Both generators
are central in C_T(d), and conjugation inside D fuses d with zd.

This proves `FourCenterSource` from the original hypotheses with terminal
solvability explicit. It applies to every compatible marking and retains
its actual element. The literal global Sylow application and the remaining
two-input self-centralization reduction are included below.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998. The proof uses the
established dihedral supplement and dotted kernel instead of computing the
larger local centralizer model; no further source geometry is assumed.
-/

public section
open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

theorem fourCenterSource_of_source_hypotheses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    FourCenterSource F (sourceResidual M Mc) := by
  intro A hfactor hlt P z hz
  let := hfactor.elementary
  let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
  obtain ⟨eD⟩ := source_factor_supplement_dihedral_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A
    hfactor.le_core hfactor.seed_le hfactor.card hfactor.intersection_card hfactor.normalized hlt
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg, _, _, _, _, _, _⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  have hZ := source_center_eq_point_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨a, ha, rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTH) ha
  have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy (rankTwoSeed T M) F.H)
  have hCU : (T : Subgroup G) ⊓ centralizer (F.U : Set G) ≤ D := by
    intro x hx
    refine ⟨?_,hx.2⟩
    let xH : F.H := ⟨x,hTH hx.1⟩
    have hk : xH ∈ F.terminalHatAction.ker := by
      apply (F.mem_uhatAction_ker_iff xH).mpr
      intro u hu
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu).symm]
      exact F.ZU.one_mem
    rw [terminal_kernel_of_center_point F dg hZ] at hk
    exact mem_map_of_mem F.H.subtype hk
  have hzmem : z ∈ F.Vi 1 := hz.symm ▸ mem_zpowers z
  have hzU : z ∈ F.ZU := hZ.symm ▸ hzmem
  have hzD : z ∈ D :=
    ⟨hUQ (map_subtype_le (center F.U) hzU),centerIn_le_centralizer F.U hzU⟩
  have hzT : z ∈ centralizer (T : Set G) := by
    intro t ht
    have htC : t ∈ centralizer ({z} : Set G) :=
      (F.H_eq_centralizer (by decide) z hz).le (hTH ht)
    exact mem_centralizer_singleton_iff.mp htC
  have hz2 : orderOf z = 2 := by
    rw [←Nat.card_zpowers,←hz]
    simpa using F.card 1 (by decide)
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  have hd1 : P.element ≠ 1 := by
    intro he
    apply P.outside_factor
    change P.element ∈ A
    rw [he]
    exact A.one_mem
  have hdz : P.element ≠ z := by
    intro he
    apply P.outside_factor
    change P.element ∈ A
    rw [he]
    exact hfactor.seed_le (F.le_seed 1 hzmem)
  have hd2 : P.element^2=1 := by rw [←P.point_order]; exact pow_orderOf_eq_one _
  obtain ⟨hc,hf⟩ := four_center_of_dihedral_supplement (T : Subgroup G) F.U D z P.element
    eD (hUQ.trans hQT) (inf_le_left.trans hQT) hCU P.mem_supplement P.mem_supplement.2
    hzD hzT hz1 hd2 hd1 hdz
  exact ⟨hc,hf⟩

/-- The original marked point has a global Sylow centralizer. The center and
fusion premises of `global_sylow_of_fourCenterGeometry` are discharged here. -/
theorem global_sylow_of_markedPoint
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A : Subgroup G) (hfactor : ElementaryFactor F (sourceResidual M Mc) A)
    (hlt : A < centralizer (A : Set G))
    (P : MarkedPoint F (sourceResidual M Mc) A) (z : G) (hz : F.Vi 1 = zpowers z) :
    normalizer (P.sylowCentralizer : Set G) ≤ F.H ∧
      Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer := by
  let := hfactor.elementary
  exact global_sylow_of_fourCenterGeometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A
    hfactor.le_core hfactor.seed_le hfactor.card hfactor.intersection_card hfactor.normalized
    hlt P z hz ((fourCenterSource_of_source_hypotheses
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs) A hfactor hlt P z hz)

/-- The source self-centralization reduction now retains only the independent
global core/component and model-exclusion inputs. -/
theorem factorSelfCentralizing_of_core_and_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hcore : CoreComponentSource F (sourceResidual M Mc))
    (hexclude : ModelExclusionSource F (sourceResidual M Mc)) :
    FactorSelfCentralizing F (sourceResidual M Mc) := by
  exact factorSelfCentralizing_of_source_inputs
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (fourCenterSource_of_source_hypotheses hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hs) hcore hexclude

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
