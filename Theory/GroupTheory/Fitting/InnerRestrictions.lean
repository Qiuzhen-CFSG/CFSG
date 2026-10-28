module

public import Theory.GroupTheory.Fitting.Core
public import Theory.PGroupCore
public import Theory.GroupTheory.CharacteristicRestrictionInnerSquares

/-!
# Assembling inner restrictions on the Fitting subgroup

If an ambient automorphism restricts to an inner automorphism of every prime
core, its action on the full Fitting subgroup is induced by one ambient element.
Induction on the finite prime support multiplies the prime-core conjugators;
distinct prime cores commute. The prime cores generate the Fitting subgroup,
so their equalities determine the full restriction.

This is the mixed-prime inner-kernel step for Aschbacher--Smith A.3.6(4),
pp.43--45, and the outer-group calculation in 11.4.3, p.778.
-/

public noncomputable section
open scoped IsMulCommutative
namespace Subgroup

/-- Independent prime-core inner restrictions assemble on the full Fitting subgroup. -/
theorem inner_on_fitting_of_inner_on_cores
    {B : Type*} [Group B] [Finite B] (α : MulAut B)
    (hα : ∀ p : ℕ, p.Prime → ∃ c : pCore p B,
      MulAut.characteristic (pCore p B) α = MulAut.conj c) :
    ∃ b : B, MulAut.characteristic (fittingSubgroup B) α =
      MulAut.conjNormal b := by
  classical
  let primes := (Nat.card B).primeFactors
  have hex (s : Finset ℕ) (hs : s ⊆ primes) : ∃ b : B,
      ∀ p : ℕ, p.Prime →
        (MulAut.conjNormal b : MulAut (pCore p B)) =
          if p ∈ s then MulAut.characteristic (pCore p B) α else 1 := by
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨1, fun p hp => by simp⟩
    | @insert q s hqs ih =>
        have hq : q.Prime := Nat.prime_of_mem_primeFactors (hs (Finset.mem_insert_self _ _))
        obtain ⟨c, hc⟩ := hα q hq
        obtain ⟨b, hb⟩ := ih (fun p hp => hs (Finset.mem_insert_of_mem hp))
        refine ⟨(c : B) * b, ?_⟩
        intro p hp
        rw [map_mul, hb p hp]
        by_cases he : q = p
        · subst p
          rw [if_neg hqs, mul_one, if_pos (Finset.mem_insert_self _ _)]
          exact MulAut.conjNormal_val.trans hc.symm
        · have ht : (MulAut.conjNormal (c : B) : MulAut (pCore p B)) = 1 := by
            let : Fact q.Prime := ⟨hq⟩
            let : Fact p.Prime := ⟨hp⟩
            ext x
            change (c : B) * (x : B) * (c : B)⁻¹ = (x : B)
            rw [pCore_commute_of_ne q p he (c : B) c.property (x : B) x.property,
              mul_inv_cancel_right]
          rw [ht, one_mul]
          simp only [Finset.mem_insert, Ne.symm he, false_or]
  obtain ⟨b, hb⟩ := hex primes (fun _ h => h)
  refine ⟨b, ?_⟩
  have hfit : fittingSubgroup B ≤ α.toMonoidHom.eqLocus (MulAut.conj b).toMonoidHom := by
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    let : Fact p.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.val.property⟩
    have he := hb p.val.val Fact.out
    rw [if_pos p.val.property] at he
    intro x hx
    exact (congrArg Subtype.val (DFunLike.congr_fun he (⟨x, hx⟩ : pCore p.val.val B))).symm
  ext x
  exact hfit x.property

end Subgroup
