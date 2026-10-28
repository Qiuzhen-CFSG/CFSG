module

public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.PCoreFreeExtension

/-!
# Reducedness from a normal subgroup and its quotient

An elementary normal module is reduced in the whole group if it is reduced
in a normal subgroup containing its centralizer and the quotient by that
normal subgroup has trivial prime core. The faithful action is an extension
of the two literal core-free quotients.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ}

/-- Extend a reduced action through a normal subgroup containing its kernel. -/
theorem IsPReduced.of_normal_subgroup
    {W N : Subgroup G} [W.Normal] [N.Normal] [IsElementaryAbelian p W]
    (hW : IsPReduced p (W.subgroupOf N)) (hWN : W ≤ N)
    (hCN : centralizer (W : Set G) ≤ N) (hQ : pCore p (G ⧸ N) = ⊥) :
    IsPReduced p W := by
  refine ⟨inferInstance,inferInstance,?_⟩
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  let D := N.map q
  let : D.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  let f := q.subgroupMap N
  have hk : centralizer (W.subgroupOf N : Set N) = f.ker := by
    ext n
    constructor
    · intro hn
      apply Subtype.ext
      apply (QuotientGroup.eq_one_iff (n:G)).mpr
      intro w hw
      exact congrArg Subtype.val (hn ⟨w,hWN hw⟩ hw)
    · intro hn w hw
      have hc : (n:G) ∈ C := (QuotientGroup.eq_one_iff (n:G)).mp
        (congrArg Subtype.val hn)
      exact Subtype.ext (hc w hw)
  let e := QuotientGroup.liftEquiv (centralizer (W.subgroupOf N : Set N))
    (q.subgroupMap_surjective N) hk
  have hD : pCore p D = ⊥ := by
    rw [←pCore_map_iso p e,hW.quotient_pCore_eq_bot,Subgroup.map_bot]
  let eQ := QuotientGroup.quotientQuotientEquivQuotient C N hCN
  have hDQ : pCore p ((G ⧸ C) ⧸ D) = ⊥ := by
    apply (map_eq_bot_iff_of_injective (f := eQ.toMonoidHom) _ eQ.injective).mp
    exact (pCore_map_iso p eQ).trans hQ
  exact pCore_eq_bot_of_normal_and_quotient p D hD hDQ

end Theory.GroupTheory
