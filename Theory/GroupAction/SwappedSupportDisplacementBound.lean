module

public import Theory.GroupAction.Lemmas

/-!
# Displacement of a moved support

If an actor moves a finite subgroup of an abelian module to a disjoint
subgroup, its difference map is injective on that subgroup. This is the
support-counting argument in Aschbacher--Smith, *The Classification of
Quasithin Groups*, D.2.12(4–5), printed p.184.
-/

open scoped IsMulCommutative

universe u v

/-- A support moved off itself contributes its entire order to displacement. -/
public theorem commutatorAction_card_ge_of_disjoint_moved_support
    {A : Type u} {M : Type v} [Group A] [Group M] [Finite M]
    [IsMulCommutative M] [MulDistribMulAction A M]
    (S : Subgroup A) (U : Subgroup M) (c : A) (hc : c ∈ S)
    (hdisjoint : Disjoint U
      (U.map (MulDistribMulAction.toMulAut A M c).toMonoidHom)) :
    Nat.card U ≤ Nat.card (commutatorAction S M) := by
  let delta : U →* M :=
    { toFun := fun point => (point : M)⁻¹ * (c • (point : M))
      map_one' := by simp
      map_mul' := by
        intro left right
        simp only [Subgroup.coe_mul, smul_mul', mul_inv_rev]
        ac_rfl }
  have hker (point : U) (hpoint : delta point = 1) : point = 1 := by
    have hfixed : (point : M) = c • (point : M) := by
      change (point : M)⁻¹ * (c • (point : M)) = 1 at hpoint
      exact inv_mul_eq_one.mp hpoint
    have hmoved : (point : M) ∈
        U.map (MulDistribMulAction.toMulAut A M c).toMonoidHom := by
      rw [hfixed]
      exact Subgroup.mem_map_of_mem _ point.property
    exact Subtype.ext (hdisjoint.le_bot ⟨point.property, hmoved⟩)
  have hinjective : Function.Injective delta :=
    (injective_iff_map_eq_one delta).mpr hker
  have hcard : Nat.card delta.range = Nat.card U := by
    change Nat.card (Set.range delta) = Nat.card U
    exact (Nat.card_congr (Equiv.ofInjective delta hinjective)).symm
  have hfull : delta.range ≤ commutatorAction S M := by
    rintro point ⟨preimage, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨c, hc⟩, (preimage : M), rfl⟩
  exact hcard ▸ Subgroup.card_le_of_le hfull
