module
public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.CyclicSpan
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.SupplementOrder

/-!
# TI and conjugate-span geometry from cyclicity of the original supplement

The point normalizer normalizes D=O₂(H) intersect C_G(U), giving genuine
ambient TI once cyclicity is supplied. The order-four result and I.7.5 then
make the literal conjugate span X abelian. Transitivity of L on V minus the
identity puts V in X. The source action kernel places X in
the two-core of LT; weak closure gives normalization by LT. Uniqueness of
the maximal two-local overgroup of LT forces N_G(X) into M.

Cyclicity is an explicit remaining hypothesis. This module does not assert
its reflection exclusions or the subsequent three-conjugate fusion result.
Source: Aschbacher--Smith 14.3.22, printed p.998.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

/-- The literal supremum of the ambient conjugates of D contained in T. -/
abbrev supplementSpan (D T : Subgroup G) : Subgroup G :=
  conjugateSpanIn D T

/-- The TI, abelian-span, weak-closure and normalizer-containment clauses, conditional only on cyclicity. -/
theorem source_supplement_span_of_cyclic
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
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))
    (hcyclic : IsCyclic (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) : Subgroup G)) :
    let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
    let X := supplementSpan D (T : Subgroup G)
    Nat.card D = 4 ∧ IsTISubgroup D ∧ IsMulCommutative X ∧
      rankTwoSeed T M ≤ X ∧
      X ≤ (T : Subgroup G) ⊓ centralizer (rankTwoSeed T M : Set G) ∧
      (T : Subgroup G) ⊓ centralizer (rankTwoSeed T M : Set G) ≤
        (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (∀ a : G, conjSubgroup X a ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2 →
        conjSubgroup X a = X) ∧
      sourceResidual M Mc ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
      normalizer (X : Set G) ≤ M := by
  intro D X
  let := hcyclic
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let J := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hDc : Nat.card D = 4 := source_supplement_card_four
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper
  have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hHD : F.H ≤ normalizer (D : Set G) := by
    apply le_trans _ inf_normalizer_le_normalizer_inf
    apply le_inf
    · exact F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
    · exact (le_normalizer_conjugateSpanBy (rankTwoSeed T M) F.H).trans
        (normalizer_le_normalizer_centralizer F.U)
  have hTI : IsTISubgroup D := cyclic_two_TI_of_point_normalizer D (F.Vi 1)
    ((isPGroup_pCoreIn 2 F.H).to_le inf_le_left) hz hproper.le hHD
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hDT : D ≤ (T : Subgroup G) := inf_le_left.trans hQT
  have hDcV : D ≤ centralizer (rankTwoSeed T M : Set G) :=
    inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _))
  have hCV : (T : Subgroup G) ⊓ centralizer (rankTwoSeed T M : Set G) ≤ J.pCoreIn 2 := by
    rw [← h.centralizer]
    exact inf_le_inf_right _ le_sup_right
  have hDcore : D ≤ J.pCoreIn 2 := (le_inf hDT hDcV).trans hCV
  have hcoreT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
  have hcoreN : J ≤ normalizer (J.pCoreIn 2 : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hDX (l : G) (hl : l ∈ sourceResidual M Mc) : conjSubgroup D l ≤ X := by
    apply conjugate_le_conjugateSpanIn
    exact (conjSubgroup_mono hDcore l).trans
      ((mem_normalizer_iff_map_conj_eq.mp (hcoreN ((show sourceResidual M Mc ≤ J from le_sup_left) hl))).le.trans hcoreT)
  have hVX : rankTwoSeed T M ≤ X := by
    obtain ⟨z, hzne⟩ := ne_bot_iff_exists_ne_one.mp (show F.Vi 1 ≠ ⊥ by
      intro he; simp [he] at hz)
    intro x hx
    by_cases hx1 : x = 1
    · simpa only [hx1] using X.one_mem
    obtain ⟨l, hl, he⟩ := h.nonidentity_transitive z x (F.le_seed 1 z.property) hx
      (fun he => hzne (Subtype.ext he)) hx1
    apply hDX l hl
    exact ⟨z, hproper.le z.property, he⟩
  have hXT : X ≤ (T : Subgroup G) := conjugateSpanIn_le _ _
  have hXab : IsMulCommutative X :=
    conjugateSpanIn_abelian_of_cyclic_four hDc hTI T.isPGroup' hDT
  let := hXab
  have hXC : X ≤ (T : Subgroup G) ⊓ centralizer (rankTwoSeed T M : Set G) :=
    le_inf hXT ((le_centralizer X).trans (centralizer_le hVX))
  have hJN : J ≤ normalizer (X : Set G) := hcoreN.trans
    (normalizer_le_normalizer_conjugateSpanIn (hXC.trans hCV) hcoreT)
  refine ⟨hDc, hTI, hXab, hVX, hXC, hCV, ?_, hJN, ?_⟩
  · intro a ha
    exact conjugateSpanIn_weakly_closed a (ha.trans hcoreT)
  · apply normalizer_le_of_unique_maximalTwoLocal (J := J)
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp (h.unique ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ J ≤ N} from ⟨hN, hJN⟩)
    · exact T.isPGroup'.to_le hXT
    · intro he
      have hVB : rankTwoSeed T M = ⊥ := bot_unique (hVX.trans he.le)
      have hc := rankTwoSeed_card h
      simp [hVB] at hc
    · exact hJN

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
