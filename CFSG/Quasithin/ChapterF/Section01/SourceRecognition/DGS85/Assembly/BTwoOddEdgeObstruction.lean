module
public import Theory.GroupTheory.Hall.TwoCoreCentralizerLift
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoPathCartan

/-!
# Odd edge actors with trivial local quotient action

An odd solvable subgroup fixing an edge is trivial if it acts trivially on
both adjacent local groups modulo their two-cores. Coprime centralizer
lifting factors each full vertex stabilizer through its centralizer and the
edge stabilizer. Graph faithfulness then kills the common normalized subgroup.

Source: DGS, *Groups and Graphs* (1985), (3.2)(c), used in the escape step
of (10.8), printed pp.160--161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

theorem odd_edge_actor_eq_bot_of_core_displacement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex F} (hvw : (graph F).Adj v w)
    (H : Subgroup G) [Group.IsSolvable H]
    (hHE : H ≤ stabilizer F v ⊓ stabilizer F w) (ho : Odd (Nat.card H))
    (hv : ⁅graphLocalGroup F v,H⁆ ≤ Q F v)
    (hw : ⁅graphLocalGroup F w,H⁆ ≤ Q F w) : H = ⊥ := by
  let _ := finite_endpoints h
  let _ : Finite H := Finite.of_injective (inclusion (hHE.trans inf_le_left)) (inclusion_injective _)
  let C (x : Vertex F) := graphLocalGroup F x ⊓ centralizer (H : Set G)
  have hfactor {x y : Vertex F} (he : (graph F).Adj x y)
      (hHx : H ≤ stabilizer F x)
      (hm : ⁅graphLocalGroup F x,H⁆ ≤ Q F x) :
      ∀ a ∈ stabilizer F x, ∃ c ∈ C x,
        ∃ b ∈ stabilizer F x ⊓ stabilizer F y, a = c*b := by
    have hQE : Q F x ≤ stabilizer F x ⊓ stabilizer F y :=
      (graph_Q_le_edgeCore h he).trans (pCoreIn_le 2 _)
    have hQL : Q F x ≤ graphLocalGroup F x :=
      (graph_Q_le_edgeCore h he).trans (graph_intrinsic_edgeCore_le h)
    let _ : Finite (Q F x) := Finite.of_injective
      (inclusion (Q_le_stabilizer F x)) (inclusion_injective _)
    have hn : stabilizer F x ≤ normalizer (Q F x : Set G) :=
      CommutingNontrivial.stabilizer_normalizes_Q F x
    have hs := OddHall.centralizer_sup_of_two_displacement (graphLocalGroup F x)
      (Q F x) H hQL (isPGroup_pCoreIn 2 _) ho
      ((sylowGenerated_le _).trans hn) (hHx.trans hn) hm
    intro a ha
    obtain ⟨l,hl,b,hb,heq⟩ := graph_intrinsic_edge_factor h hB hS he a ha
    have hlprod : l ∈ (C x : Set G) * (Q F x : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right (C x) (Q F x)
        (inf_le_left.trans ((sylowGenerated_le _).trans hn)),show C x ⊔ Q F x = graphLocalGroup F x from hs]
      exact hl
    obtain ⟨c,hc,q,hq,hlq⟩ := hlprod
    exact ⟨c,hc,q*b,(stabilizer F x ⊓ stabilizer F y).mul_mem (hQE hq) hb,
      by rw [heq,←hlq,mul_assoc]⟩
  apply graph_local_common_normal_eq_bot h hvw (C v) (C w) H
    (hfactor hvw (hHE.trans inf_le_left) hv)
  · intro a ha
    obtain ⟨c,hc,b,hb,heq⟩ := hfactor hvw.symm (hHE.trans inf_le_right) hw a ha
    exact ⟨c,hc,b,⟨hb.2,hb.1⟩,heq⟩
  · exact hHE
  · exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  · exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
