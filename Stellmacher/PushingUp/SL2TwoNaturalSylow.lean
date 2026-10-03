module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Theory.GroupAction.Quadratic

/-!
# The Sylow fixed line in the natural SL₂(2) module

An action is recorded together with a specified identification of its acting
group with `SL₂(2)` and an additive coordinate equivalence intertwining that
action with matrix multiplication. On this natural two-dimensional module,
a Sylow 2-subgroup has a unique fixed line, and in characteristic two this is
also its action-commutator subgroup.

The proof chooses the nonidentity element of the order-two Sylow subgroup. A
kernel-checked calculation in the six-element matrix group identifies the
fixed space of its matrix with the range of `A - 1`; equivariance transports
that calculation to the module. The reverse inclusion is the elementary
quadraticity of every order-two action on an elementary abelian 2-group.

This is the natural-module line calculation used in Stellmacher, *Pushing up*,
Arch. Math. 46 (1986), Lemma (2.1), specialized to `p = 2`, `n = 1`.
-/
open scoped IsMulCommutative

namespace Stellmacher.PushingUp

universe u v

/-- A two-dimensional elementary abelian module carries the standard action
through the specified identification of its acting group with `SL₂(2)`. -/
@[expose] public def IsNaturalSL2TwoActionAlong
    {G : Type u} (W : Type v) [Group G] [Group W]
    [MulDistribMulAction G W]
    (eG : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Prop :=
  ∃ eW : Additive W ≃+ (Fin 2 → ZMod 2),
    ∀ (g : G) (w : W),
      eW (Additive.ofMul (g • w)) =
        Matrix.mulVec (eG g).1 (eW (Additive.ofMul w))

private theorem sylow_card_two_of_equiv_sl2Two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (eG : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    Nat.card S = 2 := by
  have hG : IsSL2Two G := ⟨eG⟩
  have hGcard : Nat.card G = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
  rw [S.card_eq_multiplicity, hGcard]
  have hf6 : Nat.factorization 6 2 = 1 := by
    change Nat.factorization (3 * 2) 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  simp [hf6]

private theorem sl2Two_nontrivial_involution_fixed_iff_range
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hA : A ≠ 1) (hA2 : A ^ 2 = 1) (y : Fin 2 → ZMod 2) :
    Matrix.mulVec A.1 y = y ↔
      ∃ x : Fin 2 → ZMod 2, y = -x + Matrix.mulVec A.1 x := by
  decide +revert +kernel

private theorem commutatorAction₂_eq_bot_of_le_fixedPoints'
    {A : Type u} {W : Type v} [Group A] [Group W]
    [MulDistribMulAction A W]
    (hle : commutatorAction A W ≤ FixedPoints.subgroup A W) :
    commutatorAction₂ A W = ⊥ := by
  apply le_antisymm
  · change Subgroup.closure
      {d : W | ∃ a : A, ∃ w : W, w ∈ commutatorAction A W ∧
        d = w⁻¹ * a • w} ≤ ⊥
    apply (Subgroup.closure_le (K := ⊥)).2
    rintro x ⟨a, w, hw, rfl⟩
    have hfix := (FixedPoints.mem_subgroup (M := A) (a := w)).mp
      (hle hw) a
    simp [hfix]
  · exact bot_le

private theorem commutatorAction₂_eq_bot_of_actor_card_two'
    {A : Type u} {W : Type v}
    [Group A] [Finite A] [Group W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction A W]
    (hAcard : Nat.card A = 2) :
    commutatorAction₂ A W = ⊥ := by
  have hfirst : commutatorAction A W ≤ FixedPoints.subgroup A W := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := FixedPoints.subgroup A W)).2 ?_
    rintro d ⟨a, w, rfl⟩
    change ∀ b : A, b • (w⁻¹ * a • w) = w⁻¹ * a • w
    intro b
    obtain ⟨t, ht_ne, ht⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
    have ha : a = 1 ∨ a = t := by
      by_cases ha : a = 1
      · exact Or.inl ha
      · exact Or.inr (ht a ha)
    have hb : b = 1 ∨ b = t := by
      by_cases hb : b = 1
      · exact Or.inl hb
      · exact Or.inr (ht b hb)
    have ht2 : t * t = 1 := by
      by_cases htt_one : t * t = 1
      · exact htt_one
      · have htt := ht (t * t) htt_one
        have ht_one : t = 1 := by
          have heq := congrArg (fun z : A => t⁻¹ * z) htt
          simpa [mul_assoc] using heq
        exact (ht_ne ht_one).elim
    have hw_inv : w⁻¹ = w := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 W) w)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simp
    · simp
    · simp
    · simp only [smul_mul', smul_smul, ht2, one_smul]
      rw [hw_inv]
      exact IsMulCommutative.is_comm.comm _ _
  exact commutatorAction₂_eq_bot_of_le_fixedPoints' hfirst

public theorem fixedPoints_eq_commutatorAction_of_naturalSL2Two_sylow
    {G : Type u} {W : Type v}
    [Group G] [Finite G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W]
    (S : Sylow 2 G)
    (eG : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat : IsNaturalSL2TwoActionAlong W eG) :
    FixedPoints.subgroup (S : Subgroup G) W =
      commutatorAction (S : Subgroup G) W := by
  have hScard : Nat.card S = 2 := sylow_card_two_of_equiv_sl2Two S eG
  have hquad : commutatorAction₂ (S : Subgroup G) W = ⊥ :=
    commutatorAction₂_eq_bot_of_actor_card_two' hScard
  apply le_antisymm
  · intro w hw
    obtain ⟨t, ht_ne, ht⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hScard
    have ht2 : t * t = 1 := by
      by_cases htt_one : t * t = 1
      · exact htt_one
      · have htt := ht (t * t) htt_one
        have ht_one : t = 1 := by
          have heq := congrArg (fun z : S => t⁻¹ * z) htt
          simpa [mul_assoc] using heq
        exact (ht_ne ht_one).elim
    have htG2 : (t : G) ^ 2 = 1 := by
      simpa [pow_two] using congrArg Subtype.val ht2
    have hAt_ne : eG (t : G) ≠ 1 := by
      intro hAt
      apply ht_ne
      apply Subtype.ext
      exact eG.injective (by simpa using hAt)
    have hAt2 : (eG (t : G)) ^ 2 = 1 := by
      rw [← map_pow, htG2, map_one]
    obtain ⟨eW, heW⟩ := hNat
    have htw' : t • w = w :=
      (FixedPoints.mem_subgroup (M := (S : Subgroup G)) (a := w)).mp hw t
    have htw : (t : G) • w = w := by
      exact (Subgroup.mk_smul (t : G) t.property w).symm.trans htw'
    have hfixedCoord : Matrix.mulVec (eG (t : G)).1
        (eW (Additive.ofMul w)) = eW (Additive.ofMul w) := by
      have hcoord := heW (t : G) w
      rw [htw] at hcoord
      exact hcoord.symm
    obtain ⟨x, hx⟩ :=
      (sl2Two_nontrivial_involution_fixed_iff_range
        (eG (t : G)) hAt_ne hAt2 (eW (Additive.ofMul w))).mp hfixedCoord
    let z : W := Additive.toMul (eW.symm x)
    have htzCoord : eW (Additive.ofMul ((t : G) • z)) =
        Matrix.mulVec (eG (t : G)).1 x := by
      simpa [z] using heW (t : G) z
    have hwEq : w = z⁻¹ * (t • z) := by
      apply Additive.ofMul.injective
      apply eW.injective
      change eW (Additive.ofMul w) =
        eW (-Additive.ofMul z + Additive.ofMul (t • z))
      rw [map_add, map_neg]
      have htzCoord' : eW (Additive.ofMul (t • z)) =
          Matrix.mulVec (eG (t : G)).1 x := by
        exact (congrArg (fun y : W => eW (Additive.ofMul y))
          (Subgroup.mk_smul (t : G) t.property z)).trans htzCoord
      rw [htzCoord']
      simpa [z] using hx
    rw [hwEq, commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨t, z, rfl⟩
  · exact commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad

end Stellmacher.PushingUp
