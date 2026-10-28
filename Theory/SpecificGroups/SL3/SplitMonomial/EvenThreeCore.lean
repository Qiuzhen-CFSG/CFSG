module

public import Theory.SpecificGroups.SL3.SplitMonomial.EvenThreeCore.Linear
public import Theory.GroupTheory.PGroup.AbelianIndexThreeCardinality
public import Theory.GroupAction.ThreeGroupCenterFixedInvolution

/-!
# Assembly of the even three-core invariant-subgroup argument

Let K = L⟨s⟩, where L has odd order and s is an involution normalizing L.
For a nonabelian normal three-subgroup Q of K, the representation-theoretic
inputs show that the abelian index-three family is nonempty and that
normalizer automorphisms fix Z(Q) pointwise. The family has one or exactly four
members, so an odd-action argument chooses an L-invariant member A.
Center-fixing involutions preserve every such member, so s also normalizes A.
Its ambient image is therefore normal in K; self-centralization
inside Q proves that this image is not contained in the full SL₃ center.

The final theorem discharges both abstract three-group premises of the
conditional assembly below, retaining the scalar kernel, subtype map and
normality relative to the actual join K.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603; degree-three structure from
Aschbacher–Smith A.3.21(c), printed pp.55–56 of `refs/quasithin.pdf`.
-/

open Subgroup
namespace Matrix.SL3.SplitMonomial

private theorem not_map_le_center_of_abelian_index_three
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G)
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (A : Subgroup Q) (ha : IsMulCommutative A) (hi : A.index = 3) :
    ¬ A.map Q.subtype ≤ center G := by
  intro hcentral
  have hc : centralizer (A : Set Q) = ⊤ := by
    apply centralizer_eq_top_iff_subset.mpr
    intro a ha
    apply Subgroup.mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact mem_center_iff.mp (hcentral (mem_map_of_mem Q.subtype ha)) q.val
  have he := centralizer_eq_of_abelian_index_three hQ hn A ha hi
  have ht : A = ⊤ := he.symm.trans hc
  simp [ht] at hi

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The two abstract three-group inputs produce the noncentral abelian normal
subgroup required in the actual characteristic-two SL₃ join. -/
public theorem hasNoncentralAbelianNormal_of_three_family_structure
    (L : Subgroup (SpecialLinearGroup (Fin 3) F)) (hodd : Odd (Nat.card L))
    (s : SpecialLinearGroup (Fin 3) F) (hs : orderOf s = 2)
    (_hsL : s ∈ normalizer L)
    (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQK : Q ≤ L ⊔ zpowers s) (hQn : (Q.subgroupOf (L ⊔ zpowers s)).Normal)
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (hcard : Nat.card (AbelianIndexThree Q) ≤ 1 ∨ Nat.card (AbelianIndexThree Q) = 4)
    (hinv : ∀ α : MulAut Q, Function.Involutive α →
      (∀ z ∈ center Q, α z = z) →
      ∀ A : Subgroup Q, IsMulCommutative A → A.index = 3 →
        A.map α.toMonoidHom = A) :
    HasNoncentralAbelianNormal (L ⊔ zpowers s) := by
  let : Nonempty (AbelianIndexThree Q) :=
    nonempty_abelianIndexThree_of_nonabelian_three Q hQ hn
  have hpos : 0 < Nat.card (AbelianIndexThree Q) := Nat.card_pos
  have hsize : Nat.card (AbelianIndexThree Q) = 1 ∨ Nat.card (AbelianIndexThree Q) = 4 := by
    omega
  have hKQ : L ⊔ zpowers s ≤ normalizer Q :=
    (normal_subgroupOf_iff_le_normalizer hQK).mp hQn
  obtain ⟨A, ha, hi, hLA⟩ := exists_abelian_index_three_normalized_by_odd
    L Q hodd (le_sup_left.trans hKQ) hsize
  let g : normalizer (Q : Set (SpecialLinearGroup (Fin 3) F)) :=
    ⟨s, hKQ ((show zpowers s ≤ L ⊔ zpowers s from le_sup_right) (mem_zpowers s))⟩
  let α := Q.normalizerMonoidHom g
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    change s ^ 2 = 1
    rw [← hs]
    exact pow_orderOf_eq_one s
  have hα2 : α ^ 2 = 1 := by
    change Q.normalizerMonoidHom g ^ 2 = 1
    rw [← map_pow, hg2, map_one]
  have hαi : Function.Involutive α := by
    intro x
    change (α ^ 2) x = x
    rw [hα2]
    rfl
  have hfix : ∀ z ∈ center Q, α z = z :=
    normalizerAut_fixes_center_of_nonabelian_three Q hQ hn g
  have he := congrArg (fun B : Subgroup Q => B.map Q.subtype) (hinv α hαi hfix A ha hi)
  have hsA : s ∈ normalizer (A.map Q.subtype : Set (SpecialLinearGroup (Fin 3) F)) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (A.map Q.subtype).map (MulAut.conj s).toMonoidHom = _
    rw [Subgroup.map_map]
    rw [Subgroup.map_map] at he
    exact he
  have hAK : A.map Q.subtype ≤ L ⊔ zpowers s := (map_subtype_le A).trans hQK
  let : IsMulCommutative A := ha
  exact ⟨A.map Q.subtype, hAK,
    (normal_subgroupOf_iff_le_normalizer hAK).mpr (sup_le hLA (zpowers_le.mpr hsA)),
    inferInstance, not_map_le_center_of_abelian_index_three Q hQ hn A ha hi⟩

/-- A nonabelian normal three-subgroup of an odd subgroup extended by a
normalizing involution yields an abelian subgroup normal in the join and not
contained in the full special-linear center. This discharges the primitive
three-core premise of the invariant-frame construction. -/
public theorem hasNoncentralAbelianNormal_of_odd_involution_normal_three
    (L : Subgroup (SpecialLinearGroup (Fin 3) F)) (hodd : Odd (Nat.card L))
    (s : SpecialLinearGroup (Fin 3) F) (hs : orderOf s = 2)
    (hsL : s ∈ normalizer L)
    (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQK : Q ≤ L ⊔ zpowers s) (hQn : (Q.subgroupOf (L ⊔ zpowers s)).Normal)
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q) :
    HasNoncentralAbelianNormal (L ⊔ zpowers s) := by
  exact hasNoncentralAbelianNormal_of_three_family_structure L hodd s hs hsL Q hQK hQn hQ hn
    (card_abelianIndexThree_le_one_or_eq_four hQ hn)
    (MulAut.map_eq_self_of_abelian_index_three_of_center_fixed_involution hQ hn)

end Matrix.SL3.SplitMonomial
