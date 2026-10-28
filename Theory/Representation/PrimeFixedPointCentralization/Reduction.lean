module

public import Theory.Representation.PrimeFixedPointCentralization.Reduction.Constituent

/-!
# Removal of minimality and irreducibility in the prime fixed-vector theorem

Induct on the order of the q-group. If the actor moves a proper invariant
subgroup, restrict the faithful representation to its embedded semidirect
product and use induction. Otherwise the action is minimal. Maschke's theorem
then selects an irreducible constituent detecting a moved element, and its
faithful image satisfies the same minimality condition.

This is the reduction in Aschbacher, *Finite Group Theory*, second edition,
36.2, printed p.194, specialized to distinct odd primes and binary modules.
The minimal faithful irreducible statement remains an explicit premise; the
abelian and extraspecial structure argument discharging it is independent.
-/

universe u
namespace Representation.PrimeFixedPointCentralization

/-- The minimal faithful irreducible case implies the full fixed-vector
statement for distinct odd primes. No irreducibility or minimality hypothesis
is imposed on the representation in the conclusion. -/
public theorem prime_action_fixed_vectors_of_minimal
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (hqodd : Odd q) (hrodd : Odd r) (hqr : q ≠ r) :
    MinimalFixedVectorStatement.{u} q r → PrimeActionFixedVectorStatement.{u} q r := by
  intro hfixed
  have hmain : ∀ n : ℕ,
      ∀ (P A W : Type u) [Group P] [Finite P] [Group A] [Finite A]
        [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W],
      Nat.card P = n → IsPGroup q P → Nat.card A = r →
      ∀ φ : A →* MulAut P, Function.Injective φ →
      ∀ ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W,
      Function.Injective ρ →
      ∃ v : W, v ≠ 0 ∧ ∀ a : A, ρ (SemidirectProduct.inr a) v = v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P A W _ _ _ _ _ _ _ hn hP hA φ hφ ρ hfaith
      by_cases hmin : IsMinimalAction φ
      · exact fixed_vector_of_minimal_action hqodd hrodd hqr hfixed hP hA φ hφ hmin ρ hfaith
      · unfold IsMinimalAction at hmin
        push Not at hmin
        obtain ⟨Q, hQ, hproper, a, z, hz, hmove⟩ := hmin
        let ψ := invariantSubgroupAction φ Q hQ
        have hψ : Function.Injective ψ := by
          apply prime_action_injective_of_moving hA
          refine ⟨a, ⟨z, hz⟩, ?_⟩
          intro heq
          exact hmove (congrArg Subtype.val heq)
        let f := invariantSubgroupInclusion φ Q hQ
        have hf : Function.Injective f := invariantSubgroupInclusion_injective φ Q hQ
        have hlt : Nat.card Q < n := by
          rw [← hn]
          exact Nat.lt_of_not_ge (fun h => hproper (Q.eq_top_of_le_card h))
        obtain ⟨v, hv, hvA⟩ := ih (Nat.card Q) hlt Q A W rfl
          (hP.to_subgroup Q) hA ψ hψ (ρ.comp f) (hfaith.comp hf)
        refine ⟨v, hv, fun b => ?_⟩
        simpa [f, invariantSubgroupInclusion] using hvA b
  intro P A W _ _ _ _ _ _ _ hP hA φ hφ ρ hfaith
  exact hmain (Nat.card P) P A W rfl hP hA φ hφ ρ hfaith

end Representation.PrimeFixedPointCentralization
