module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightResidual.Permutation
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The two-residual of the quaternion automorphism group

The literal subgroup `O²(Aut(Q₈))` is isomorphic to A₄. More precisely, for
any nonidentity automorphism `c` with `c³ = 1`, it is the join of the inner
automorphism subgroup and `⟨c⟩`.

The four-diagonal action identifies Aut(Q₈) with S₄. The inner subgroup is
normal of order four, so its join with the disjoint subgroup of order three
has index two. S₄ has a unique index-two subgroup, namely A₄. Finally A₄ is
the two-residual of S₄: the quotient has order two, and its generating
three-cycles vanish in every two-group quotient. The isomorphism below is
obtained by restricting the four-diagonal action to the actual residual.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.988.
-/

namespace QuaternionGroup.Residual
private abbrev Q := QuaternionGroup 2
private abbrev A := MulAut Q
private abbrev inner : Subgroup A := (MulAut.conj : Q →* A).range

private instance inner_normal : inner.Normal where
  conj_mem g hg f := by
    obtain ⟨q, rfl⟩ := hg
    refine ⟨f q, ?_⟩
    ext x
    simp [MulAut.conj_apply]

private theorem inner_card : Nat.card inner = 4 := by
  have h := inner.index_mul_card
  rw [QuaternionGroup.index_range_conj_two, QuaternionGroup.card_mulAut_two] at h
  omega

private theorem join_index (c : A) (hc : c^3 = 1) (hne : c ≠ 1) :
    (inner ⊔ Subgroup.zpowers c).index = 2 := by
  have ho : orderOf c = 3 := orderOf_eq_prime hc hne
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, ho]
  have hd : Disjoint inner (Subgroup.zpowers c) :=
    Subgroup.disjoint_of_coprime_natCard (by rw [inner_card, hcard]; decide)
  have hr : inner.relIndex (inner ⊔ Subgroup.zpowers c) = 3 := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right,
      hd.eq_bot, Subgroup.relIndex_bot_left, hcard]
  have h := Subgroup.relIndex_mul_index (show inner ≤ inner ⊔ Subgroup.zpowers c from le_sup_left)
  rw [hr, QuaternionGroup.index_range_conj_two] at h
  omega

private theorem symmetric_residual : pResidual 2 (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 4)).index = 2^1
    simp
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro x hx
    apply Subgroup.mem_pResidual_of_orderOf_coprime
    rw [Equiv.Perm.IsThreeCycle.orderOf hx]
    decide

/-- The four-diagonal action maps the literal two-residual onto A₄. -/
public theorem residual_map :
    (pResidual 2 (MulAut (QuaternionGroup 2))).map autEquivPerm.toMonoidHom =
      alternatingGroup (Fin 4) := by
  rw [Subgroup.map_pResidual, symmetric_residual]

/-- The isomorphism O²(Aut(Q₈)) ≃ A₄, retaining its inclusion in Aut(Q₈). -/
public noncomputable def residualEquivAlternating :
    pResidual 2 (MulAut (QuaternionGroup 2)) ≃* alternatingGroup (Fin 4) :=
  (autEquivPerm.subgroupMap _).trans (MulEquiv.subgroupCongr residual_map)

/-- Every nonidentity cubic automorphism, together with the inner automorphisms,
generates exactly the literal two-residual of Aut(Q₈). -/
public theorem residual_eq_join (c : MulAut (QuaternionGroup 2))
    (hc : c^3 = 1) (hne : c ≠ 1) :
    pResidual 2 (MulAut (QuaternionGroup 2)) =
      (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).range ⊔
        Subgroup.zpowers c := by
  apply Subgroup.map_injective (f := autEquivPerm.toMonoidHom) autEquivPerm.injective
  rw [residual_map]
  symm
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  rw [Subgroup.index_map_of_bijective (f := autEquivPerm.toMonoidHom) autEquivPerm.bijective]
  exact join_index c hc hne

/-- The residual isomorphism is the restriction of the four-diagonal action. -/
public theorem residualEquivAlternating_apply
    (x : pResidual 2 (MulAut (QuaternionGroup 2))) :
    (residualEquivAlternating x : Equiv.Perm (Fin 4)) = autEquivPerm x := by rfl

end QuaternionGroup.Residual
