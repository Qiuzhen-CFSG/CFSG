module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Geometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Preparation

/-!
# Original natural flags and parabolic actors from local earlier inputs

Naturality and structural normalization at G,T give the literal L action,
its two parabolics, their generation and the elementary overlap. Flag
uniqueness selects an omitted-point conjugator inside the original L.
These are the shared starting data for both HS source arguments, with
no universal earlier input. All actual actors and embeddings are retained.
Source: Aschbacher--Smith 12.8.2--4 and 14.3.23--32, pp.850--851,999--1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open CaseOneHS
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_natural_action_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    NaturalThreeAction L V T := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  refine ⟨?_, h.sylow_normalizes_at structural, chosen.normalizes, ?_, ?_⟩
  · rw [twoResidual, h.residual, ← MonoidHom.range_eq_map, range_subtype]
  · intro a
    obtain ⟨l, hl, he⟩ := h.full_L_action a
    refine ⟨⟨l, hl⟩, ?_⟩
    ext v
    rw [conjugation_apply]
    exact he v
  · rw [conjugation_ker]
    apply map_injective L.subtype_injective
    simpa only [subgroupOf_map_subtype, inf_comm, pCoreIn] using h.centralizer_L

theorem source_natural_flag_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (g : G) (hg : g ∈ L) :
    NaturalFlagData F.H T (F.Vi 1) (F.Vi 2) V (F.E g) L (F.Li L 1) (F.Li L 2) := by
  let := chosen.elementary
  exact NaturalFlags.naturalFlagData_of_invariant_flag
    (source_natural_action_at d earlier hq chosen structural) F g hg

theorem source_first_actor_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (g : G) (hg : g ∈ L) :
    F.Li L 1 ∈ YFamily F.H T (F.Vi 2) (F.E g) ∧
      movedSpace (F.Vi 2) (F.Li L 1) = V ∧ localJoin (F.Li L 2) (F.Li L 1) = L := by
  have h := source_natural_flag_at d earlier hq chosen structural F g hg
  refine ⟨⟨h.L₁_three, ?_, ?_⟩, h.moved_eq, ?_⟩
  · rw [h.moved_eq]; exact h.moved_card
  · rw [h.moved_eq]; exact h.moved_le_E
  · exact sup_comm (F.Li L 2) (F.Li L 1) |>.trans h.generated

theorem source_intersection_elementary_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgH : g ∉ F.H) : IsElementaryAbelian 2 (F.E g) := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  have hphi' : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [hphi]
    exact map_subgroupOf_eq_of_le (show F.Vi 1 ≤ F.U from
      (F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  exact F.E_elementary (by decide) g htwo hphi' (disjoint_iff.mpr
    (F.conjugate_point_inf_ZU (by decide) hc g (chosen.normalizes hg) hgH))

theorem exists_source_conjugator_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : ∃ g : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨_, F', huniq, z, hz, he, g, hgP, hgH⟩ := h.exists_flag_geometry_at structural
  have hcuts (i : ℕ) : F.Vi i = F'.Vi i := by
    by_cases hi : i ≤ 3
    · exact huniq i hi (F.Vi i) (F.le_seed i) (F.card i hi) (F.invariant i)
    · have hf : F.Vi i = V := le_antisymm (F.le_seed i)
        ((le_of_eq F.last.symm).trans (F.monotone (by omega : 3 ≤ i)))
      have hf' : F'.Vi i = V := le_antisymm (F'.le_seed i)
        ((le_of_eq F'.last.symm).trans (F'.monotone (by omega : 3 ≤ i)))
      exact hf.trans hf'.symm
  have hH : F.H = F'.H := by simp only [H, Gi, hcuts]
  have hP : F.P L = F'.P L := by simp only [P, Gi, hcuts]
  rw [← hP] at hgP
  rw [← hH] at hgH
  have hTP : (T : Subgroup G) ≤ F.P L := by
    refine le_inf le_sup_right (le_iInf fun i => le_iInf fun _ => F.invariant i)
  have hprod : g ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
      (h.sylow_normalizes_at structural)]
    exact hgP.1
  obtain ⟨l, hl, t, ht, rfl⟩ := hprod
  refine ⟨l, hl, ?_, ?_⟩
  · have hh := (F.P L).mul_mem hgP ((F.P L).inv_mem (hTP ht))
    simpa only [mul_inv_cancel_right] using hh
  · intro hlH
    exact hgH (F.H.mul_mem hlH (F.invariant 1 ht))

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
