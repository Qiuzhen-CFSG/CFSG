module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets

/-!
# The two remaining families in the bounded actor comparison

The bounded B.5.1 catalogue separates into the intended small actors, binary
rank-one actors (including S₅), and the three actors with two-part at least 64.
The triple-six branch retains perfectness: it is obtained from the actual
generalized Fitting subgroup when B.5.1 says that subgroup fills the actor.
The center and quotient isomorphisms alone would not imply perfectness.

This is an exhaustive reduction, not an exclusion of either remaining family.
The full module conclusion stays on the original `BoundedBranch`.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1(1),
p.99, B.5.6(1), p.105, and F.6.18, pp.309–310, as used in 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison.ActorPruning
open FFAlternatives
universe u v

/-- The binary rank-one actors still requiring comparison with F.6.18. -/
inductive RankOneActorModel (A : Type*) [Group A] : Prop
  | linearTwo (F : BinaryField) (lower : 2 ≤ F.degree) (upper : F.degree ≤ 7)
      (equiv : A ≃* SL(2,F.Carrier))
  | symmetricFive (equiv : A ≃* Equiv.Perm (Fin 5))

/-- The three remaining actors whose orders are divisible by 64. -/
inductive LargeActorModel (A : Type*) [Group A] : Prop
  | linearThreeFour (F : BinaryField) (degree : F.degree = 2)
      (equiv : A ≃* SL(3,F.Carrier))
  | linearFourTwo (equiv : A ≃* SL(4,ZMod 2))
  | symmetricEight (equiv : A ≃* Equiv.Perm (Fin 8))

variable {A : Type u} [Group A]

private theorem component_split [Group.IsPerfect A] (h : BoundedQuasisimpleModel A) :
    SmallActorModel A ∨ RankOneActorModel A ∨ LargeActorModel A := by
  cases h with
  | linearTwo F hlo hhi e => exact Or.inr (Or.inl (.linearTwo F hlo hhi e))
  | linearThree F hhi e =>
    by_cases hd : F.degree = 1
    · let : Fintype F.Carrier := Fintype.ofFinite _
      let f : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, F.card_eq, hd]
        simp)
      exact Or.inl (.linearThree (e.trans (Atlas.fieldEquivSL 3 f)))
    · have htwo : F.degree = 2 := by have := F.degree_pos; omega
      exact Or.inr (Or.inr (.linearThreeFour F htwo e))
  | alternatingSix e => exact Or.inl (.alternatingSix e)
  | alternatingSeven e => exact Or.inl (.alternatingSeven e)
  | tripleSix e q => exact Or.inl (.tripleSix ⟨inferInstance, ⟨e⟩, ⟨q⟩⟩)
  | g2DerivedTwo e => exact Or.inl (.g2Derived e)
  | linearFourTwo e => exact Or.inr (Or.inr (.linearFourTwo e))

private theorem outer_split {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (h : OuterNaturalAction ρ) :
    SmallActorModel A ∨ RankOneActorModel A ∨ LargeActorModel A := by
  rcases h with h | h
  · obtain ⟨n, hlo, hhi, ⟨e⟩⟩ := h
    interval_cases n
    · exact Or.inr (Or.inl (.symmetricFive e.groupEquiv))
    · exact Or.inl (.symmetricSix e.groupEquiv)
    · exact Or.inl (.symmetricSeven e.groupEquiv)
    · exact Or.inr (Or.inr (.symmetricEight e.groupEquiv))
  · obtain ⟨e⟩ := h
    exact Or.inl (.g2 e.groupEquiv)

/-- Every bounded branch gives a genuine small actor or one of the two
remaining model families. No ambient/offender equality is used. -/
theorem actor_split {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) A V} (b : BoundedBranch ρ) :
    SmallActorModel A ∨ RankOneActorModel A ∨ LargeActorModel A := by
  have whole (h : generalizedFitting A = ⊤) :
      SmallActorModel A ∨ RankOneActorModel A ∨ LargeActorModel A := by
    let e : A ≃* generalizedFitting A :=
      topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)
    let : IsQuasisimple (generalizedFitting A) := b.quasisimple
    let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
      (f := e.symm.toMonoidHom) e.symm.surjective
    exact component_split (b.component.comap e)
  cases b.source.clause_one with
  | irreducible _ _ _ _ he =>
    rcases he with h | ⟨_, h⟩
    · exact whole h
    · exact outer_split _ h
  | doubleThree _ h _ _ _ => exact whole h
  | naturalDual _ _ h _ => exact whole h
  | repeatedNatural _ _ _ _ _ h _ => exact whole h

/-- The actual matrix and permutation models each have order divisible by 64.
The SL₄ calculation uses the order formula, not enumeration of its carrier. -/
theorem LargeActorModel.sixtyFour_dvd (h : LargeActorModel A) : 64 ∣ Nat.card A := by
  cases h with
  | linearThreeFour F hd e =>
    rw [Nat.card_congr e.toEquiv]
    have h := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
    norm_num [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, hd] at h
    exact h
  | linearFourTwo e =>
    rw [Nat.card_congr e.toEquiv]
    have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Fin.val_zero, Fin.val_succ, Nat.mul_one] at h
    have hd : 64 ∣ Nat.card PSL(4,ZMod 2) := by rw [h]; norm_num
    exact hd.trans (card_dvd_of_surjective
      (QuotientGroup.mk' (center SL(4,ZMod 2))) (QuotientGroup.mk'_surjective _))
  | symmetricEight e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- Neither rank-one actor has an odd prime cube dividing its order.
The field bound here is the one already obtained from the ambient Sylows. -/
theorem RankOneActorModel.not_odd_prime_cube (h : RankOneActorModel A)
    {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) : ¬ p ^ 3 ∣ Nat.card A := by
  cases h with
  | linearTwo F _ hhi e =>
    rw [Nat.card_congr e.toEquiv]
    exact Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.linearTwo_no_odd_prime_cube
      F hhi hp hne
  | symmetricFive e =>
    intro hd
    rw [Nat.card_congr e.toEquiv] at hd
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hd
    have hdiv : p ∣ 2 * 2 * 2 * 3 * 5 :=
      (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
    have he : p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 5 := by
      simpa only [hp.dvd_mul,
        Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
        Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
        Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5), or_assoc] using hdiv
    rcases he with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hne rfl | norm_num at hd

end QuasisimpleComparison.ActorPruning
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
