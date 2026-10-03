module
public import Theory.GroupAction.Lemmas
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Displacement from a swapped support and an independent line

Let a group act by automorphisms on a finite commutative group. If a subgroup
of actors has a displacement line of order two in a support of order four,
and an actor in it moves that support to a disjoint subgroup,
then the full actor subgroup has displacement of cardinal at least eight.

On the support, the difference map of the moving actor is injective and its
image is disjoint from the support: a difference lying in the support would
put the moved point in both disjoint supports. The resulting order-four
image and the supplied displacement line form a disjoint product of order
eight inside the full displacement subgroup.

This elementary action calculation is used for the natural SL₂(2) wreath C₂
module in Stellmacher (9.10)(10),(12), printed pp.58–59.
-/
open scoped IsMulCommutative
universe u v

public theorem commutatorAction_card_ge_eight_of_swapped_support_line
    {A : Type u} {M : Type v} [Group A] [Group M] [Finite M]
    [IsMulCommutative M] [MulDistribMulAction A M]
    (S : Subgroup A) (U : Subgroup M)
    (R : Subgroup M) (c : A) (hc : c ∈ S)
    (hUcard : Nat.card U = 4)
    (hrank : Nat.card R = 2)
    (hline : R ≤ U) (hlineFull : R ≤ commutatorAction S M)
    (hdisjoint : Disjoint U
      (U.map (MulDistribMulAction.toMulAut A M c).toMonoidHom)) :
    8 ≤ Nat.card (commutatorAction S M) := by
  let delta : U →* M :=
    { toFun := fun point => (point : M)⁻¹ * (c • (point : M))
      map_one' := by simp
      map_mul' := by
        intro left right
        simp only [Subgroup.coe_mul, smul_mul', mul_inv_rev]
        ac_rfl }
  have hdeltaSupport (point : U) (hpoint : delta point ∈ U) : point = 1 := by
    have hmoved : c • (point : M) ∈ U := by
      have hh := U.mul_mem point.property hpoint
      simpa only [delta, MonoidHom.coe_mk, OneHom.coe_mk, mul_inv_cancel_left] using hh
    have hmap : c • (point : M) ∈ U.map (MulDistribMulAction.toMulAut A M c).toMonoidHom :=
      Subgroup.mem_map_of_mem _ point.property
    have hone : c • (point : M) = 1 := hdisjoint.le_bot ⟨hmoved, hmap⟩
    apply Subtype.ext
    exact (MulDistribMulAction.toMulAut A M c).injective (by simpa using hone)
  have hinjective : Function.Injective delta := (injective_iff_map_eq_one delta).mpr (by
    intro point hpoint
    apply hdeltaSupport
    rw [hpoint]
    exact U.one_mem)
  have hdeltaCard : Nat.card delta.range = 4 := by
    change Nat.card (Set.range delta) = 4
    exact (Nat.card_congr (Equiv.ofInjective delta hinjective)).symm.trans hUcard
  have hdeltaDisjoint : Disjoint delta.range U := by
    apply disjoint_iff_inf_le.mpr
    rintro point ⟨⟨preimage, rfl⟩, hpoint⟩
    have hone := hdeltaSupport preimage hpoint
    simp only [hone, map_one]
    exact Subgroup.one_mem _
  have hdeltaFull : delta.range ≤ commutatorAction S M := by
    rintro point ⟨preimage, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨c, hc⟩, (preimage : M), rfl⟩
  have hDR : Disjoint delta.range R := hdeltaDisjoint.mono_right hline
  have hnormal : R ≤ Subgroup.normalizer (delta.range : Set M) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcard := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint delta.range R hnormal hDR
  have hbound := Subgroup.card_le_of_le (sup_le hdeltaFull hlineFull)
  rw [hcard, hdeltaCard, hrank] at hbound
  exact hbound

/-- The cyclic-actor form supplies its own displacement line. -/
public theorem commutatorAction_card_ge_eight_of_swapped_support
    {A : Type u} {M : Type v} [Group A] [Group M] [Finite M]
    [IsMulCommutative M] [MulDistribMulAction A M]
    (S : Subgroup A) (U : Subgroup M)
    (a c : A) (ha : a ∈ S) (hc : c ∈ S)
    (hUcard : Nat.card U = 4)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers a) M) = 2)
    (hline : commutatorAction (Subgroup.zpowers a) M ≤ U)
    (hdisjoint : Disjoint U
      (U.map (MulDistribMulAction.toMulAut A M c).toMonoidHom)) :
    8 ≤ Nat.card (commutatorAction S M) := by
  have hlineFull : commutatorAction (Subgroup.zpowers a) M ≤ commutatorAction S M := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro point ⟨actor, vector, rfl⟩
    exact Subgroup.subset_closure ⟨⟨actor, (Subgroup.zpowers_le.mpr ha) actor.property⟩, vector, rfl⟩
  exact commutatorAction_card_ge_eight_of_swapped_support_line S U
    (commutatorAction (Subgroup.zpowers a) M) c hc hUcard hrank hline hlineFull hdisjoint
