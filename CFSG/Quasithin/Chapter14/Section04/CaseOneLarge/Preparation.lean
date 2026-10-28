module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Source

/-!
# Original natural flags and the nonzero point core

The chosen counterexample's natural coordinates give the literal conjugation
map and its two-core kernel. Apply the natural-flag calculation to obtain L₁
in Y and generation by L₁ and L₂. The two displaced Frattini lines make the
actual intersection E elementary abelian. Uniqueness of invariant cuts then
selects an omitted-point conjugator inside L for the caller's original flag.
Finally the original nonzero chosen module survives inside the point core
after restriction to any overgroup of LT.

Only the named earlier naturality, structural and escape implications remain
explicit. No marked large-model catalogue or recognition statement is assumed.
Source: Aschbacher--Smith, 12.8.3–4, 12.8.9(7), 12.8.11(2), pp.849–854;
14.4.8(1) and 14.4.13, pp.1009,1012.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_natural_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    NaturalThreeAction L V T := by
  let h := higherRankHypothesis d earlier hq chosen
  refine ⟨?_, h.sylow_normalizes structural, chosen.normalizes, ?_, ?_⟩
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

theorem source_natural_flag (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (g : G) (hg : g ∈ L) :
    NaturalFlagData F.H T (F.Vi 1) (F.Vi 2) V (F.E g) L (F.Li L 1) (F.Li L 2) := by
  let := chosen.elementary
  exact NaturalFlags.naturalFlagData_of_invariant_flag
    (source_natural_action d earlier hq chosen structural) F g hg

theorem source_first_actor (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (g : G) (hg : g ∈ L) :
    F.Li L 1 ∈ YFamily F.H T (F.Vi 2) (F.E g) ∧
      movedSpace (F.Vi 2) (F.Li L 1) = V ∧ localJoin (F.Li L 2) (F.Li L 1) = L := by
  have h := source_natural_flag d earlier hq chosen structural F g hg
  refine ⟨⟨h.L₁_three, ?_, ?_⟩, h.moved_eq, ?_⟩
  · rw [h.moved_eq]; exact h.moved_card
  · rw [h.moved_eq]; exact h.moved_le_E
  · exact sup_comm (F.Li L 2) (F.Li L 1) |>.trans h.generated

theorem source_intersection_elementary (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgH : g ∉ F.H) : IsElementaryAbelian 2 (F.E g) := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  have hphi' : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [hphi]
    exact map_subgroupOf_eq_of_le (show F.Vi 1 ≤ F.U from
      (F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  exact F.E_elementary (by decide) g htwo hphi' (disjoint_iff.mpr
    (F.conjugate_point_inf_ZU (by decide) hc g (chosen.normalizes hg) hgH))

/-- Choose the source right conjugator inside L, for the caller's original flag.
Uniqueness identifies its cuts with a constructed flag; the Sylow factor can
then be removed from a lift in LT. -/
theorem exists_source_conjugator (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) : ∃ g : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H := by
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨_, F', huniq, z, hz, he, g, hgP, hgH⟩ := h.exists_flag_geometry structural
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
      (h.sylow_normalizes structural)]
    exact hgP.1
  obtain ⟨l, hl, t, ht, rfl⟩ := hprod
  refine ⟨l, hl, ?_, ?_⟩
  · have hh := (F.P L).mul_mem hgP ((F.P L).inv_mem (hTP ht))
    simpa only [mul_inv_cancel_right] using hh
  · intro hlH
    exact hgH (F.H.mul_mem hlH (F.invariant 1 ht))

omit [Finite G] in
/-- The actual point vertex retains a nontrivial core in every overgroup of LT.
The nonzero chosen module lies in that core before restriction. -/
theorem source_point_core_nontrivial (chosen : ChosenModule T L V)
    (K : Subgroup G) (hK : L ⊔ (T : Subgroup G) ≤ K) :
    ((L ⊔ (T : Subgroup G)).subgroupOf K).pCoreIn 2 ≠ ⊥ := by
  intro he
  have hc : pCore 2 ((L ⊔ (T : Subgroup G)).subgroupOf K) = ⊥ := by
    apply map_injective ((L ⊔ (T : Subgroup G)).subgroupOf K).subtype_injective
    simpa only [pCoreIn, Subgroup.map_bot] using he
  have ht := pCore_map_iso 2 (subgroupOfEquivOfLe hK)
  rw [hc, Subgroup.map_bot] at ht
  apply chosen.ne_bot
  apply le_bot_iff.mp
  simpa only [pCoreIn, ← ht, Subgroup.map_bot] using chosen.le_core

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
