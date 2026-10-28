module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanEscape

/-!
# Cardinality of a normalized residual two-subgroup

The normalized two-subgroup generation theorem identifies a nontrivial
residual complement with the full adjacent edge core. The local SL2 quotient
then computes its odd index as the coefficient-field order. These lemmas are
used by the terminal residual and regular-path source calculations.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem edge_core_complement_card
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A : Subgroup G)
    (hgen : A ⊔ Q (family P) v = (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hdis : Disjoint A (Q (family P) v)) : Nat.card A = Nat.card F := by
  let _ := finite_endpoints h
  let M := graphLocalGroup (family P) v
  let _ : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 M := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hAM : A ≤ M := (le_sup_left.trans hgen.le).trans (graph_intrinsic_edgeCore_le h)
  have hcoreM : (pCore 2 M).map M.subtype = Q (family P) v := by
    exact CommutingTrivial.graphLocalGroup_core h v
  obtain ⟨T,hT⟩ := CommutingTrivial.local_edge_sylow h hB hS hvw
  let Tq := T.mapSurjective hq
  have hAT : A.subgroupOf M ⊔ pCore 2 M = T := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAM,hcoreM,hT]
    exact hgen
  have hAQ : (A.subgroupOf M).map q = (Tq : Subgroup SL(2,F)) := by
    have hh := congrArg (Subgroup.map q) hAT
    rw [Subgroup.map_sup,←hk,map_ker_self,sup_bot_eq] at hh
    change (A.subgroupOf M).map q = (Tq : Subgroup SL(2,F))
    exact hh
  have hi := relIndex_ker (A.subgroupOf M) q
  rw [←relIndex_map_map_of_injective _ _ M.subtype_injective,hk,
    hcoreM,map_subgroupOf_eq_of_le hAM,hAQ] at hi
  have hi' : (Q (family P) v).relIndex A = Nat.card F :=
    hi.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 Tq).symm.toEquiv)
  rw [←inf_relIndex_right,inf_comm,hdis.eq_bot,relIndex_bot_left] at hi'
  exact hi'

theorem cartan_normalized_disjoint_two_subgroup_card
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (C A : Subgroup G)
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hc : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAS : A ≤ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hp : IsPGroup 2 A) (hn : C ≤ normalizer (A : Set G))
    (hne : A ≠ ⊥) (hdis : Disjoint A (Q (family P) v)) :
    A ⊔ Q (family P) v = (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ∧
      Nat.card A = Nat.card F := by
  have hnot : ¬ A ≤ Q (family P) v := by
    intro hh
    exact hne (eq_bot_iff.mpr (fun a ha =>
      (mem_bot.mp (disjoint_def.mp hdis ha (hh ha)))))
  have hgen := cartan_normalized_two_subgroup_core_product h hB hS hvw e C A
    hCE hc hg hAS hp hn hnot
  exact ⟨hgen,edge_core_complement_card h hB hS hvw e A hgen hdis⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
