module

public import Theory.GroupAction.Lemmas

/-!
# A moved support exhausting the displacement

If an actor moves a finite abelian support off itself, its difference map on
that support is injective. When the support and the full displacement have
the same order, this map is also onto the full displacement. Thus every
displacement has a representative in the one moved support.

This is the equality case of the support-counting argument in
Aschbacher--Smith, *The Classification of Quasithin Groups*, D.2.12(5),
printed p.184.
-/

open scoped IsMulCommutative

/-- Equality in the moved-support bound makes the difference map onto the
entire displacement subgroup. -/
public theorem commutatorAction_mem_iff_of_disjoint_moved_support_card_eq
    {A M : Type*} [Group A] [Group M] [Finite M]
    [IsMulCommutative M] [MulDistribMulAction A M]
    (S : Subgroup A) (U : Subgroup M) (c : A) (hc : c ∈ S)
    (hdisjoint : Disjoint U
      (U.map (MulDistribMulAction.toMulAut A M c).toMonoidHom))
    (hcard : Nat.card (commutatorAction S M) = Nat.card U) (v : M) :
    v ∈ commutatorAction S M ↔ ∃ u ∈ U, u⁻¹ * (c • u) = v := by
  let delta : U →* M :=
    { toFun := fun u => (u : M)⁻¹ * (c • (u : M))
      map_one' := by simp
      map_mul' := by
        intro u w
        simp only [Subgroup.coe_mul, smul_mul', mul_inv_rev]
        ac_rfl }
  have hinj : Function.Injective delta := by
    apply (injective_iff_map_eq_one delta).mpr
    intro u hu
    have hfixed : (u : M) = c • (u : M) := inv_mul_eq_one.mp hu
    have hmoved : (u : M) ∈
        U.map (MulDistribMulAction.toMulAut A M c).toMonoidHom := by
      rw [hfixed]
      exact Subgroup.mem_map_of_mem _ u.property
    exact Subtype.ext (hdisjoint.le_bot ⟨u.property, hmoved⟩)
  have hdeltaCard : Nat.card delta.range = Nat.card U := by
    exact (Nat.card_congr (Equiv.ofInjective delta hinj)).symm
  have hle : delta.range ≤ commutatorAction S M := by
    rintro w ⟨u, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨c, hc⟩, (u : M), rfl⟩
  have heq : delta.range = commutatorAction S M :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hdeltaCard, hcard])
  rw [← heq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, u.property, hu⟩
  · rintro ⟨u, hu, huv⟩
    exact ⟨⟨u, hu⟩, huv⟩
