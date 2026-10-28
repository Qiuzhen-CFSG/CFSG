module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.CosetGraph
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.Parameters

/-!
# Strong regularity of the source coset graph

The original (1,8,6) stabilizer suborbits act transitively on ordered adjacent and nonadjacent pairs. Actual group elements transport their common neighbors, giving strong regularity and the exact (15,6,1,3) parameters.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
section Transport
variable {A X:Type*} [Group A] [MulAction A X] (Γ:SimpleGraph X)
    (hinv:∀g:A,∀x y:X,Γ.Adj (g • x) (g • y)↔Γ.Adj x y)
private def neighborEquiv (g:A) (x:X):Γ.neighborSet x≃Γ.neighborSet (g • x) where
  toFun y:=⟨g • y.val,(hinv g x y.val).mpr y.property⟩
  invFun y:=⟨g⁻¹ • y.val,by
    have hh:Γ.Adj (g⁻¹ • (g • x)) (g⁻¹ • y.val):=(hinv g⁻¹ _ _).mpr y.property
    change Γ.Adj x (g⁻¹ • y.val)
    simpa only [inv_smul_smul] using hh⟩
  left_inv y:=Subtype.ext (inv_smul_smul g y.val)
  right_inv y:=Subtype.ext (smul_inv_smul g y.val)
private def commonEquiv (g:A) (x y:X):Γ.commonNeighbors x y≃Γ.commonNeighbors (g • x) (g • y) where
  toFun z:=⟨g • z.val,(hinv g x z.val).mpr z.property.1,(hinv g y z.val).mpr z.property.2⟩
  invFun z:=⟨g⁻¹ • z.val,by
    have hx:Γ.Adj (g⁻¹ • (g • x)) (g⁻¹ • z.val):=(hinv g⁻¹ _ _).mpr z.property.1
    have hy:Γ.Adj (g⁻¹ • (g • y)) (g⁻¹ • z.val):=(hinv g⁻¹ _ _).mpr z.property.2
    change Γ.Adj x (g⁻¹ • z.val) ∧ Γ.Adj y (g⁻¹ • z.val)
    simpa only [inv_smul_smul] using And.intro hx hy⟩
  left_inv z:=Subtype.ext (inv_smul_smul g z.val)
  right_inv z:=Subtype.ext (smul_inv_smul g z.val)
end Transport

variable {G:Type*} [Group G] (H:Subgroup G) (hH:Nat.card H=24)
    (b c:G⧸H) (hb:b≠((1:G):G⧸H)) (h8:Nat.card (MulAction.orbit H b)=8)
    (hcover:MulAction.orbit H c=(({((1:G):G⧸H)}:Set (G⧸H))∪MulAction.orbit H b)ᶜ)
    (h6:Nat.card (MulAction.orbit H c)=6)

include h8 hcover h6 in
private theorem adjacent_pair_actor {x y:G⧸H} (hadj:(cosetGraph H hH).Adj x y):
    ∃g:G,g • (((1:G):G⧸H))=x ∧ g • c=y := by
  obtain ⟨a,ha⟩:=MulAction.exists_smul_eq G (((1:G):G⧸H)) x
  have hh: (cosetGraph H hH).Adj ((1:G):G⧸H) (a⁻¹ • y) := by
    have ht:=(cosetGraph_invariant H hH a⁻¹ x y).mpr hadj
    rwa [←ha,inv_smul_smul] at ht
  obtain ⟨k,hk⟩:=(cosetGraph_base_adj_iff H hH b c h8 hcover h6 _).mp hh
  have hfix:k.val • (((1:G):G⧸H))=((1:G):G⧸H) := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [MulAction.stabilizer_quotient]
    exact k.property
  refine ⟨a*k.val,?_,?_⟩
  · rw [mul_smul,hfix,ha]
  · change k.val • c=a⁻¹ • y at hk
    rw [mul_smul,hk,smul_inv_smul]

include hb h8 hcover h6 in
private theorem nonadjacent_pair_actor {x y:G⧸H} (hne:x≠y)
    (hnadj:¬(cosetGraph H hH).Adj x y):
    ∃g:G,g • (((1:G):G⧸H))=x ∧ g • b=y := by
  obtain ⟨a,ha⟩:=MulAction.exists_smul_eq G (((1:G):G⧸H)) x
  have he:a⁻¹ • y≠((1:G):G⧸H) := by
    intro hh
    have ht:=congrArg (fun z:G⧸H=>a • z) hh
    rw [smul_inv_smul,ha] at ht
    exact hne ht.symm
  have hh:¬(cosetGraph H hH).Adj ((1:G):G⧸H) (a⁻¹ • y) := by
    intro ht
    have hu:=(cosetGraph_invariant H hH a _ _).mpr ht
    rw [ha,smul_inv_smul] at hu
    exact hnadj hu
  obtain ⟨k,hk⟩:=(cosetGraph_base_nonadj_iff H hH b c hb h8 hcover h6 _).mp ⟨he,hh⟩
  have hfix:k.val • (((1:G):G⧸H))=((1:G):G⧸H) := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [MulAction.stabilizer_quotient]
    exact k.property
  refine ⟨a*k.val,?_,?_⟩
  · rw [mul_smul,hfix,ha]
  · change k.val • b=a⁻¹ • y at hk
    rw [mul_smul,hk,smul_inv_smul]

include hb h8 hcover h6 in
theorem cosetGraph_strongly_regular [Fintype (G⧸H)] [DecidableRel (cosetGraph H hH).Adj]
    (hi:H.index=15):(cosetGraph H hH).IsSRGWith 15 6 1 3 := by
  classical
  let Γ:=cosetGraph H hH
  let o:G⧸H:=(1:G)
  let l:=Fintype.card (Γ.commonNeighbors o c)
  let m:=Fintype.card (Γ.commonNeighbors o b)
  have hinv:=cosetGraph_invariant H hH
  have hd0:Γ.degree o=6 := by
    rw [←Γ.card_neighborSet_eq_degree]
    rw [←Nat.card_eq_fintype_card]
    have he:Γ.neighborSet o=MulAction.orbit H c := Set.ext (cosetGraph_base_adj_iff H hH b c h8 hcover h6)
    rw [he,h6]
  have hd:Γ.IsRegularOfDegree 6 := by
    intro x
    obtain ⟨g,hg⟩:=MulAction.exists_smul_eq G o x
    have he:=Fintype.card_congr (neighborEquiv Γ hinv g o)
    rw [Γ.card_neighborSet_eq_degree,Γ.card_neighborSet_eq_degree] at he
    rw [hg] at he
    exact he.symm.trans hd0
  have hr:Γ.IsSRGWith 15 6 l m := by
    refine ⟨?_,hd,?_,?_⟩
    · rw [←Nat.card_eq_fintype_card,←Subgroup.index_eq_card]
      exact hi
    · intro x y hxy
      obtain ⟨g,hg,hc⟩:=adjacent_pair_actor H hH b c h8 hcover h6 hxy
      have he:=Fintype.card_congr (commonEquiv Γ hinv g o c)
      rw [hg,hc] at he
      exact he.symm
    · intro x y hne hxy
      obtain ⟨g,hg,hb⟩:=nonadjacent_pair_actor H hH b c hb h8 hcover h6 hne hxy
      have he:=Fintype.card_congr (commonEquiv Γ hinv g o b)
      rw [hg,hb] at he
      exact he.symm
  obtain ⟨hl,hm⟩:=exact_rank_three_parameters Γ hr hinv
  simpa only [hl,hm] using hr
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
