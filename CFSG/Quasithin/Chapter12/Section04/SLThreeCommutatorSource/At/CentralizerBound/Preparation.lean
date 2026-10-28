module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Preparation
public import Theory.Representation.BinaryOffender.RankOneCentralizer
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.Setup
public import CFSG.Quasithin.ChapterE.Section06.Defs
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Cases


/-!
# The common L₃ subspace geometry in 12.4.8

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

Every nonidentity element of the marked four-dimensional L₃ action fixes
at most a plane: a larger fixed space would give rank-one displacement,
hence an involution, contrary to the proved B.4.8 involution calculation.
Thus a hyperplane, or a plane together with the fixed line it misses,
has trivial pointwise stabilizer in the actual normalizer action.

The original L-action kernel is a two-group. Since T normalizes L and
supplements it in LT, the kernel on LT is also a two-group. Normality
then identifies its Sylow intersection with C_T(V), so LT normalizes
C_T(V). Together with source 1.2.7 this establishes the genuine E.6.1
hypotheses. Every escaping hyperplane and each of its planes belongs to
Γ, and E.6.5 gives the same literal Sylow subgroup in both centralizers.

This is the common preparation for the three cases, not their exclusion.
Source: Aschbacher–Smith, Lemma 12.4.8, first two paragraphs, printed p.815.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

theorem escaping_subspaces
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    Nat.card U = 8 ∧ ¬ fixedSubgroup L V ≤ U ∧
      normalizer (V : Set G) ⊓ centralizer (U : Set G) = centralizer (V : Set G) ∧
      U ∈ Section06.obstructionFamily (normalizer (V : Set G)) V ∧
      ∀ U₀ ≤ U, subgroupCorank U U₀ = 1 →
        Nat.card U₀ = 4 ∧ ¬ fixedSubgroup L V ≤ U₀ ∧
        normalizer (V : Set G) ⊓ centralizer (U₀ : Set G) = centralizer (V : Set G) ∧
        U₀ ∈ Section06.obstructionFamily (normalizer (V : Set G)) V := by
  let _ := D.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUV
  have hU := hyperplane_card E hne hUV hcor
  obtain ⟨z, _, hz, hM, hMV, _⟩ :=
    fixed_involution_setup_of_card_two h D structural (E.fixed_card_eq_two hne)
  have hZC : centralizer (fixedSubgroup L V : Set G) ≤ normalizer (V : Set G) := by
    rw [← hMV, hM]
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact (hx z (by rw [hz]; exact mem_zpowers z)).symm
  have hout : ¬ fixedSubgroup L V ≤ U :=
    fun hin => hescape ((centralizer_le hin).trans hZC)
  have hCU := local_centralizer_of_card_gt_four E hne hN U hUV (by omega)
  have hCV : normalizer (V : Set G) ⊓ centralizer (V : Set G) = centralizer (V : Set G) :=
    inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)
  refine ⟨hU, hout, hCU, ⟨hUV, ?_, hescape,
    Section06.oddCentralizerCondition_of_eq (hCU.trans hCV.symm)⟩, ?_⟩
  · intro he
    rw [he, card_bot] at hU
    omega
  · intro U₀ hU₀U hcor₀
    have hc := plane_card hU hU₀U hcor₀
    have hout₀ : ¬ fixedSubgroup L V ≤ U₀ := fun hin => hout (hin.trans hU₀U)
    have hCU₀ := local_centralizer_of_plane E hne hN U₀ (hU₀U.trans hUV) hc hout₀
    refine ⟨hc, hout₀, hCU₀, hU₀U.trans hUV, ?_, ?_,
      Section06.oddCentralizerCondition_of_eq (hCU₀.trans hCV.symm)⟩
    · intro he
      rw [he, card_bot] at hc
      omega
    · exact fun hin => hescape ((centralizer_le hU₀U).trans hin)


theorem source_hypothesisE61
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) :
    HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (V : Set G)) V := by
  have hs := structural L h
  have hOrbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hs.1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  obtain ⟨z, hz, hfix, hM, hMV, _⟩ :=
    fixed_involution_setup_of_card_two h D structural (E.fixed_card_eq_two hne)
  have hmax : IsMaximalTwoLocal (normalizer (V : Set G)) := by
    simpa only [hOrbit, hMV] using hu.normalizer_maximal
  have hTV := (hs.2.2 V D).1
  refine ⟨h.simpleQTKE, hmax, hTV, D.ne_bot, D.elementary, D.le_sylow,
    (normal_subgroupOf_iff_le_normalizer D.le_sylow).mpr hTV, ?_, ?_⟩
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hg)
  · intro N hN hle
    have he : N = normalizer (L : Set G) := by
      simpa only [hOrbit] using hu.normalizer_unique N hN
        ((le_inf (le_inf (sup_le D.normalizes hTV) (sup_le D.normalizes hTV))
          (join_normalizes_sylow_centralizer E hs.1 hTV)).trans hle)
    exact he.trans hMV

/-- The actual E.6.5 application to U and every hyperplane U₀ of U.
Both Sylow subgroups have ambient image C_T(V); no conjugacy replacement
or alternative two-subgroup is introduced. -/
theorem Configuration.sylow_centralizers {U : Subgroup G}
    (c : Configuration T L V U) :
    Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
        (centralizer (U : Set G)) ∧
      ∀ U₀ ≤ U, subgroupCorank U U₀ = 1 →
        Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
          (centralizer (U₀ : Set G)) := by
  have hE := source_hypothesisE61 c.hypothesis c.structural
    c.extension c.fixed_nontrivial
  have hg := escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape
  exact ⟨hE.sylow_obstruction hg.2.2.2.1, fun U₀ hU₀ hcor =>
    hE.sylow_obstruction (hg.2.2.2.2 U₀ hU₀ hcor).2.2.2⟩

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
