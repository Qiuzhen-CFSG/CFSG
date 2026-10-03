module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.CriticalPairCommutator
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionEight.EightTwoEdgeQuadraticAction

/-!
# Centrality of shifted critical-pair commutators

In the noncentral case of (8.2), take a critical pair (left,right) and a
middle vertex adjacent to left. If right is within critical distance of
middle, and a further center generates the middle stabilizer with its edge
intersection, the shifted commutator is central in that stabilizer whenever
the further vertex is within critical distance of right.

The critical-pair commutator lies in both endpoint centers. Critical
minimality puts its right endpoint center in the middle core and hence the
edge group. The proved quadratic edge action centralizes the commutator.
The further vertex center lies in the right core, so it also centralizes
this commutator. The generating equality completes the centrality argument.
This formulation keeps all four vertices in the original graph, and is
used twice for R1 and R2 in Stellmacher (8.2), printed pp.37–38.
Source: `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_shifted_commutator_central_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (left middle right next : ctx.Γ.Vertex)
    (hleft : left ∈ neighborhood ctx.Γ middle)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hmiddle : ctx.Γ.distance right middle < ctx.criticalPath.length)
    (hnext : ctx.Γ.distance next right < ctx.criticalPath.length)
    (hgen : (GAt ctx.Γ middle ⊓ GAt ctx.Γ left) ⊔ ZAt ctx.Γ next =
      GAt ctx.Γ middle) :
    ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ ≤ CenterAmbient (GAt ctx.Γ middle) := by
  have hquadratic := eight_two_edge_quadratic_action_local ctx hcenter left middle
    (ctx.Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mp hleft))
  let Γ := ctx.Γ
  let R := ⁅z Γ left, z Γ right⁆
  let E := stabilizer Γ middle ⊓ stabilizer Γ left
  have hbound := critical_pair_commutator_le_inf ctx.sectionSeven Γ
    ctx.criticalPath left right hcritical
  have hrightQ : z Γ right ≤ q Γ middle :=
    SevenSix.critical_minimality Γ ctx.criticalPath hmiddle
  have hQmiddle : q Γ middle ≤ stabilizer Γ middle := by
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  let T : Sylow 2 E := default
  have hQleft : q Γ middle ≤ stabilizer Γ left :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle left hleft T).2.2
  have hrightE : z Γ right ≤ E := hrightQ.trans (le_inf hQmiddle hQleft)
  have hRE : R ≤ ⁅z Γ left, E⁆ := Subgroup.commutator_mono le_rfl hrightE
  have hREcomm : ⁅R,E⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hmono := Subgroup.commutator_mono hRE (le_refl E)
    exact hmono.trans_eq (by simpa only [E, inf_comm] using hquadratic)
  have hRmid : R ≤ stabilizer Γ middle := hbound.trans inf_le_right |>.trans hrightQ |>.trans hQmiddle
  have hnextQ : z Γ next ≤ q Γ right :=
    SevenSix.critical_minimality Γ ctx.criticalPath hnext
  obtain ⟨actor, cp, _hcpLeft, hcpRight, _⟩ :=
    exists_criticalPath_of_critical_pair ctx.sectionSeven Γ ctx.criticalPath left right hcritical
  have hrightCenter : z Γ right ≤ Subgroup.centralizer (q Γ right : Set G) := by
    have hself : z Γ (Γ.act actor right) ≤
        Subgroup.centralizer (q Γ (Γ.act actor right) : Set G) := by
      rw [← hcpRight]
      have hp := cp.path_adj ⟨cp.length - 1, by have := cp.length_pos; omega⟩
      have hi : (⟨cp.length - 1, by have := cp.length_pos; omega⟩ : Fin cp.length).succ =
          ⟨cp.length, Nat.lt_succ_self _⟩ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        have := cp.length_pos
        omega
      rw [hi, cp.path_end] at hp
      have hn := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hp)
      exact ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a' _ hn).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
    have hcomm := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hself
    rw [z_act, SevenSix.q_act, ← Subgroup.map_commutator] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj actor⁻¹).injective).mp hcomm)
  have hRnext : R ≤ Subgroup.centralizer (z Γ next : Set G) :=
    (hbound.trans inf_le_right).trans (hrightCenter.trans (Subgroup.centralizer_le hnextQ))
  have hRcentral : R ≤ Subgroup.centralizer (stabilizer Γ middle : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    change E ⊔ z Γ next = stabilizer Γ middle at hgen
    rw [← hgen]
    exact sup_le
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hREcomm))
      (Subgroup.le_centralizer_iff.mp hRnext)
  intro element helement
  refine ⟨⟨element, hRmid helement⟩, ?_, rfl⟩
  change (⟨element, hRmid helement⟩ : stabilizer Γ middle) ∈
    Subgroup.center (stabilizer Γ middle)
  rw [Subgroup.mem_center_iff]
  intro other
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (hRcentral helement) other other.property

end Stellmacher.SectionEight
