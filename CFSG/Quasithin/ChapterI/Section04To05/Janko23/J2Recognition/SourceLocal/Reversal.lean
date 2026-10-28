module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.System

/-!
# The source edge reversal centralizes the full edge fixer

Mark an A₄ edge inside the local A₅. Its reversing double transposition
lies in the A₄ itself. Transporting that element through the actual subgroup
embeddings gives a reversal in X ∨ Y. The full pointwise edge fixer is
C_G(X ∨ Y), so conjugation by this reversal is the identity on that fixer.

This is the source conjugation identity in Aschbacher, *Sporadic Groups*
(1994), 47.10, p.267. It concerns the actual ambient edge fixer, rather than
only its trivial intersection with the local A₅.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal

open alternatingGroup.FiveLocalGeometry.CubicEdges in
private theorem exists_reversal_in_join {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 5)) (P Q : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (eJ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4)) :
    ∃ t : H, t ∈ P ⊔ Q ∧ orderOf t = 2 ∧
      P.map (MulAut.conj t).toMonoidHom = Q ∧
      Q.map (MulAut.conj t).toMonoidHom = P := by
  obtain ⟨a, hp, hq⟩ := exists_marking e P Q hP hQ eJ
  refine ⟨a.symm reversal, ?_, ?_, ?_, ?_⟩
  · have hr : reversal ∈ (P ⊔ Q).map a.toMonoidHom := by
      rw [Subgroup.map_sup, hp, hq, join_model, mem_fourEmbedding]
      decide +kernel
    exact mem_map_equiv.mp hr
  · rw [MulEquiv.orderOf_eq, reversal_order]
  · apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_conj_equiv, a.apply_symm_apply, hp, hq, reversal_maps.1]
  · apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_conj_equiv, a.apply_symm_apply, hp, hq, reversal_maps.2]

namespace EdgeFrame
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
variable {D : Seed G} (F : EdgeFrame D)

/-- A reversing involution lies in the endpoint join and acts trivially on
the entire ambient pointwise edge fixer. All source premises are discharged. -/
theorem centralizing_reversal :
    ∃ t : F.K, (t : G) ∈ D.X ⊔ F.y.val ∧ orderOf t = 2 ∧
      (t : G) • D.base = F.y ∧ (t : G) • F.y = D.base ∧
      ∀ b : edgeFixer G D.base F.y, (t : G) * (b : G) * (t : G)⁻¹ = b := by
  have he := InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent
  have hX : D.X ≤ F.K := le_sup_left.trans (F.endpoints_le he)
  have hY : F.y.val ≤ F.K := le_sup_right.trans (F.endpoints_le he)
  have hc (A : D.Vertex) (hA : A.val ≤ F.K) :
      Nat.card (A.val.subgroupOf F.K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv, D.vertex_card]
  obtain ⟨eJ⟩ := (D.graph_adj_iff D.base F.y).mp F.adjacent
  obtain ⟨t, ht, ht₂, hx, hy⟩ := exists_reversal_in_join F.localEquiv
    (D.X.subgroupOf F.K) (F.y.val.subgroupOf F.K)
    (hc D.base hX) (hc F.y hY)
    ((AlternatingFiveGeometry.joinSubgroupOfEquiv F.K D.X F.y.val hX hY).trans eJ)
  have lift (A B : D.Vertex) (hA : A.val ≤ F.K) (hB : B.val ≤ F.K)
      (h : (A.val.subgroupOf F.K).map (MulAut.conj t).toMonoidHom =
        B.val.subgroupOf F.K) : (t : G) • A = B := by
    change MulAut.conj t • A.val.subgroupOf F.K = B.val.subgroupOf F.K at h
    rw [conj_smul_subgroupOf hA t] at h
    have hm := congrArg (fun U : Subgroup F.K => U.map F.K.subtype) h
    rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hA t),
      map_subgroupOf_eq_of_le hB] at hm
    exact Subtype.ext hm
  have htJ : (t : G) ∈ D.X ⊔ F.y.val := by
    have hm := mem_map_of_mem F.K.subtype ht
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hX,
      map_subgroupOf_eq_of_le hY, Subgroup.subtype_apply] using hm
  refine ⟨t, htJ, ht₂, lift D.base F.y hX hY hx, lift F.y D.base hY hX hy, ?_⟩
  intro b
  have hb := (edgeFixer_eq_centralizer_join_of_alternatingFive D D.base F.y he).le b.property
  rw [hb t htJ, mul_inv_cancel_right]

end EdgeFrame
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
