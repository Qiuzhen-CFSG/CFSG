module
public import Theory.Representation.NormalizedCThreeInvolution
public import Theory.GroupAction.Quadratic

/-!
# Elementary two-actions normalizing C₃ on a sixteen-element module

In the normalized order-three configuration of Stellmacher (1.6), let
U=[V,F] have order sixteen and let I≤S be the specified four-element
subgroup containing A of order two. Assume A centralizes F and has four
fixed points on U, while every element of I outside A inverts F through
the full-commutator condition.

The theorem assembles the exact action package: S=I C_S(U), each nontrivial
image involution has a four-element commutator subgroup, and the I-action
is nonquadratic. It also records the two common fixed points and the
four-element action image as an exact kernel cardinality.

The kernel theorem proves the join and common fixed-space assertions. The
normalized-involution theorem supplies all commutator ranks. For
nonquadraticity, the join shows C_U(I)=C_U(S), of order two. A quadratic
I-action would put [U,A] inside this subgroup, whereas involution
rank-nullity and |C_U(A)|=4 give |[U,A]|=4, a contradiction. Restricted
actions in the statement use the displayed canonical invariance proofs.

Source: `refs/latex/stellmacher-n-group.tex`, Stellmacher (1.6), journal
p. 18. This package has no minimal-m hypothesis or later exceptional
classification assumption.
-/

open scoped IsMulCommutative

namespace Representation

universe u

private theorem elementaryAbelian_subgroup
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
    (IsMulCommutative.is_comm.comm (x : V) (y : V))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)

public theorem normalizedCThree_cardSixteen_elementaryTwo_action
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F A I S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hAI : A ≤ I) (hIS : I ≤ S)
    (hSnorm : S ≤ Subgroup.normalizer (F : Set G))
    (hFcard : Nat.card F = 3) (hAcard : Nat.card A = 2) (hIcard : Nat.card I = 4)
    (hFA : ⁅F, A⁆ = ⊥)
    (hfull : ∀ b ∈ I, b ∉ A → ⁅F, Subgroup.zpowers b⁆ = F)
    (hUcard : Nat.card (commutatorAction F V) = 16)
    (hfixed : Nat.card (commutatorAction F V ⊓ FixedPoints.subgroup A V : Subgroup V) = 4) :
    let U := commutatorAction F V
    let K := S ⊓ fixingSubgroup G (U : Set V)
    S = I ⊔ K ∧
      (∀ x : S, (x : G) ∉ K →
        letI : IsInvariant (Subgroup.zpowers (x : G)) V U :=
          commutatorAction_isInvariant_of_normalizing_actor (Subgroup.zpowers (x : G)) F
            (Subgroup.zpowers_le.mpr (hSnorm x.property))
        Nat.card (commutatorAction (Subgroup.zpowers (x : G)) U) = 4) ∧
      (letI : IsInvariant I V U :=
        commutatorAction_isInvariant_of_normalizing_actor I F (hIS.trans hSnorm)
       commutatorAction₂ I U ≠ ⊥) ∧
      Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) = 2 ∧
      Nat.card S = 4 * Nat.card K := by
  let U := commutatorAction F V
  let K := S ⊓ fixingSubgroup G (U : Set V)
  let _ : IsElementaryAbelian 2 S := hS
  obtain ⟨hjoin, hfixS, hindex⟩ := normalizedCThree_cardSixteen_kernel_data
    F A I S hS hAI hIS hSnorm hFcard hAcard hIcard hFA hfull hUcard hfixed
  refine ⟨hjoin, ?_, ?_, hfixS, hindex⟩
  · intro x hx
    let _ : IsInvariant (Subgroup.zpowers (x : G)) V U :=
      commutatorAction_isInvariant_of_normalizing_actor (Subgroup.zpowers (x : G)) F
        (Subgroup.zpowers_le.mpr (hSnorm x.property))
    have hxne : (x : G) ≠ 1 := by
      intro h
      exact hx (h ▸ K.one_mem)
    have hx2 : (x : G) ^ 2 = 1 := by
      exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 S) x)
    have hne : ∃ v ∈ U, (x : G) • v ≠ v := by
      by_contra h
      push Not at h
      exact hx ⟨x.property, (mem_fixingSubgroup_iff (M := G) (s := (U : Set V))).mpr h⟩
    exact (normalizedCThree_involution_fixed_commutator_card_four F x hFcard
      ⟨hxne, hx2⟩ (hSnorm x.property) hUcard hne).2
  · let _ : IsInvariant I V U :=
      commutatorAction_isInvariant_of_normalizing_actor I F (hIS.trans hSnorm)
    let _ : IsInvariant A V U :=
      commutatorAction_isInvariant_of_normalizing_actor A F (hAI.trans (hIS.trans hSnorm))
    let _ : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
    let _ : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hUcard]; decide)
    have hfixedIS : U ⊓ FixedPoints.subgroup I V = U ⊓ FixedPoints.subgroup S V := by
      apply le_antisymm
      · rintro v ⟨hvU, hvI⟩
        refine ⟨hvU, ?_⟩
        have hSfix : S ≤ fixingSubgroup G ({v} : Set V) := by
          rw [hjoin]
          apply sup_le
          · intro i hi
            rw [mem_fixingSubgroup_iff]
            intro w hw
            have hwv := Set.mem_singleton_iff.mp hw
            subst w
            exact hvI ⟨i, hi⟩
          · rintro k ⟨_hkS, hkfix⟩
            rw [mem_fixingSubgroup_iff]
            intro w hw
            have hwv := Set.mem_singleton_iff.mp hw
            subst w
            exact (mem_fixingSubgroup_iff (M := G) (s := (U : Set V))).mp hkfix v hvU
        intro s
        exact (mem_fixingSubgroup_iff (M := G) (s := ({v} : Set V))).mp
          (hSfix s.property) v (Set.mem_singleton v)
      · rintro v ⟨hvU, hvS⟩
        exact ⟨hvU, fun i => hvS ⟨i, hIS i.property⟩⟩
    have hfixIcard : Nat.card (FixedPoints.subgroup I U) = 2 := by
      rw [← Subgroup.card_map_of_injective (K := FixedPoints.subgroup I U) U.subtype_injective,
        fixedPoints_subgroup_map_subtype_eq_inf, hfixedIS]
      exact hfixS
    have hfixAcard : Nat.card (FixedPoints.subgroup A U) = 4 := by
      rw [← Subgroup.card_map_of_injective (K := FixedPoints.subgroup A U) U.subtype_injective,
        fixedPoints_subgroup_map_subtype_eq_inf]
      exact hfixed
    obtain ⟨a, hane, _huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
    have ha2 : a ^ 2 = 1 := by rw [← hAcard]; exact pow_card_eq_one'
    have hprod := (involution_fixed_commutator_card_data (U := U) a ⟨hane, ha2⟩ hAcard).1
    have hcommAcard : Nat.card (commutatorAction A U) = 4 := by
      rw [hUcard, hfixAcard] at hprod
      omega
    have hmono : commutatorAction A U ≤ commutatorAction I U := by
      rw [commutatorAction_eq_closure]
      apply (Subgroup.closure_le (K := commutatorAction I U)).mpr
      rintro z ⟨a, v, rfl⟩
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨a, hAI a.property⟩, v, rfl⟩
    intro hquad
    have hle := hmono.trans (commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad)
    have hcard := Subgroup.card_le_of_le hle
    rw [hcommAcard, hfixIcard] at hcard
    omega

end Representation
