module

public import Theory.GroupTheory.PGroup.AbelianIndexThreeCount
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Index

/-!
# Normalizer orbits of abelian index-three subgroups

Let `Q` be a nonabelian finite three-group inside `G`, and let `A` be an
abelian index-three subgroup of `Q`. Conjugation by `N_G(Q)` preserves the
family of abelian index-three subgroups of `Q`. Its stabilizer at `A` is
`N_G(A) ∩ N_G(Q)`, with `A` mapped into `G`. The orbit-stabilizer formula
and the bound of four for this family give the required relative-index bound.

The argument includes the unique-subgroup case and uses no representation
theory or extraspecial classification.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.3.21(c),
printed pp.55–56 (`refs/quasithin.pdf`).
-/

open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem normalizer_relIndex_le_card_abelian_index_three
    (Q : Subgroup G) (A : Subgroup Q) (ha : IsMulCommutative A) (hi : A.index = 3) :
    (normalizer (A.map Q.subtype : Set G)).relIndex (normalizer (Q : Set G)) ≤
      Nat.card {B : Subgroup Q // IsMulCommutative B ∧ B.index = 3} := by
  let N := normalizer (Q : Set G)
  have hmap (g : N) : (g • A).map Q.subtype =
      (A.map Q.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
    change (A.map (Q.normalizerMonoidHom g).toMonoidHom).map Q.subtype = _
    rw [map_map, map_map]
    rfl
  have hstab : MulAction.stabilizer N A =
      (normalizer (A.map Q.subtype : Set G)).subgroupOf N := by
    ext g
    change g • A = A ↔ (g : G) ∈ normalizer (A.map Q.subtype : Set G)
    rw [mem_normalizer_iff_map_conj_eq]
    change g • A = A ↔
      (A.map Q.subtype).map (MulAut.conj (g : G)).toMonoidHom = A.map Q.subtype
    rw [← hmap]
    exact (map_injective Q.subtype_injective).eq_iff.symm
  rw [relIndex, ← hstab, MulAction.index_stabilizer]
  change Nat.card (MulAction.orbit N A) ≤ _
  let f : MulAction.orbit N A →
      {B : Subgroup Q // IsMulCommutative B ∧ B.index = 3} := fun B => ⟨B.val, by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp B.property
    rw [← hg]
    let : IsMulCommutative A := ha
    change IsMulCommutative (A.map (Q.normalizerMonoidHom g).toMonoidHom) ∧ _
    exact ⟨inferInstance, (A.index_map_equiv (Q.normalizerMonoidHom g)).trans hi⟩⟩
  apply Nat.card_le_card_of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun C : {B : Subgroup Q // IsMulCommutative B ∧ B.index = 3} => C.val) h

/-- The normalizer of a nonabelian three-group has an orbit of size at most four
on each of its abelian index-three subgroups, expressed as an ambient relative index. -/
public theorem normalizer_relIndex_le_four_of_abelian_index_three
    (Q : Subgroup G) (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (A : Subgroup Q) (hA : IsMulCommutative A) (hi : A.index = 3) :
    (normalizer ((A.map Q.subtype : Subgroup G) : Set G)).relIndex
      (normalizer (Q : Set G)) ≤ 4 :=
  (normalizer_relIndex_le_card_abelian_index_three Q A hA hi).trans
    (card_abelian_index_three_le_four hQ hn)

end Subgroup
