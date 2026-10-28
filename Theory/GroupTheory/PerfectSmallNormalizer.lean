module

public import Theory.GroupTheory.Commutator.PerfectSolvableSupplement
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Perfect subgroups with a small normalizer index

A perfect group has trivial image in the symmetric group on at most four
points. Applied to cosets of a normalizer, this places the perfect subgroup
inside its normal core, hence makes it subnormal. An invariant solvable
supplement then makes it normal in the join.

The relative-index forms keep normality inside the join, not in the original
ambient group. This is the small-index argument in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 13.6.17, printed p.930.
-/

@[expose] public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem perfect_le_normalCore_of_index_le_four (K N : Subgroup G)
    [Group.IsPerfect K] (hi : N.index ≤ 4) : K ≤ N.normalCore := by
  classical
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  change Nat.card (G ⧸ N) ≤ 4 at hi
  have hc : Fintype.card (G ⧸ N) ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hi
  let e : (G ⧸ N) ↪ Fin 4 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (G ⧸ N)) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let f := (MulAction.toPermHom G (G ⧸ N)).comp K.subtype
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro k hk
  rw [N.normalCore_eq_ker]
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict ⟨k, hk⟩) 1)

theorem isSubnormal_of_perfect_of_normalizer_index_le_four (K : Subgroup G)
    [Group.IsPerfect K] (hi : (normalizer (K : Set G)).index ≤ 4) : K.IsSubnormal := by
  let N := normalizer (K : Set G)
  have hKN : K ≤ N.normalCore := perfect_le_normalCore_of_index_le_four K N hi
  have hnormal : (K.subgroupOf N.normalCore).Normal :=
    normal_subgroupOf_of_le_normalizer N.normalCore_le
  exact hnormal.isSubnormal.trans hKN (inferInstance : N.normalCore.Normal).isSubnormal

theorem relIndex_sup_of_normal_left (Q N : Subgroup G) [Q.Normal] :
    N.relIndex (Q ⊔ N) = N.relIndex Q := by
  have hmul :
      Q.relIndex N * N.relIndex (Q ⊔ N) = Q.relIndex N * N.relIndex Q := by
    calc
      Q.relIndex N * N.relIndex (Q ⊔ N) =
          (N ⊓ Q).relIndex (Q ⊔ N) := by
        rw [← inf_relIndex_left (H := N) (K := Q)]
        exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (N ⊓ Q).relIndex Q * Q.relIndex (Q ⊔ N) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = Q.relIndex N * N.relIndex Q := by
        simp [inf_relIndex_right, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero index_ne_zero_of_finite) hmul

theorem relIndex_sup_of_normalizes_left (Q C : Subgroup G)
    (hCQ : C ≤ normalizer (Q : Set G)) : C.relIndex (Q ⊔ C) = C.relIndex Q := by
  let H := Q ⊔ C
  let : (Q.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Q.le_normalizer hCQ)
  have h := relIndex_sup_of_normal_left (Q.subgroupOf H) (C.subgroupOf H)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_left] at h
  exact h

theorem normal_of_perfect_of_solvable_supplement_of_small_normalizer
    (K Q : Subgroup G) [Group.IsPerfect K] [Q.Normal] [Group.IsSolvable Q]
    (hsup : K ⊔ Q = ⊤) (hi : (normalizer (K : Set G)).relIndex Q ≤ 4) : K.Normal := by
  let N := normalizer (K : Set G)
  have hNQ : Q ⊔ N = ⊤ := top_unique (by
    rw [← hsup]
    exact sup_le (K.le_normalizer.trans le_sup_right) le_sup_left)
  have hiN : N.index ≤ 4 := by
    rw [← relIndex_top_right, ← hNQ, relIndex_sup_of_normal_left]
    exact hi
  have hsub := isSubnormal_of_perfect_of_normalizer_index_le_four K hiN
  have he := hsub.eq_solvableResidual_of_sup_eq_top Q hsup
  rw [he]
  infer_instance

theorem normal_in_sup_of_perfect_of_solvable_of_small_normalizer
    (K Q : Subgroup G) [Group.IsPerfect K] [Group.IsSolvable Q]
    (hKQ : K ≤ normalizer (Q : Set G))
    (hi : (normalizer (K : Set G)).relIndex Q ≤ 4) :
    (K.subgroupOf (K ⊔ Q)).Normal := by
  let H := K ⊔ Q
  let K' := K.subgroupOf H
  let Q' := Q.subgroupOf H
  let : Group.IsPerfect K' := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm.surjective
  let : Group.IsSolvable Q' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show Q ≤ H from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show Q ≤ H from le_sup_right)).injective
  let : Q'.Normal := normal_subgroupOf_sup_of_le_normalizer hKQ
  apply normal_of_perfect_of_solvable_supplement_of_small_normalizer K' Q'
    (codisjoint_subgroupOf_sup K Q).eq_top
  dsimp only [K', Q']
  rw [← subgroupOf_normalizer_eq (show K ≤ H from le_sup_left),
    relIndex_subgroupOf (show Q ≤ H from le_sup_right)]
  exact hi
end Subgroup
