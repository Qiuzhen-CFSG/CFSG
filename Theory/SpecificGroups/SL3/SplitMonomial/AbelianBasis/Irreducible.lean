module

public import Theory.Representation.RankThreePGroupIrreducible
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Absolute irreducibility of the overgroup

A nonabelian three-subgroup acts absolutely irreducibly in dimension three
away from characteristic three. Every invariant subspace of an overgroup is
invariant under this subgroup, giving absolute irreducibility of the overgroup.

Source: Aschbacher–Smith, Lemma A.3.21(c), printed pp.55–56, and the
irreducible reduction in GLS3, proof of Theorem 6.5.3.
-/

open Representation
open scoped TensorProduct
namespace Matrix.SL3.SplitMonomial

/-- A subgroup of SL₃ containing a nonabelian three-subgroup acts absolutely
irreducibly away from characteristic three. -/
public theorem natural_isAbsolutelyIrreducible_of_nonabelian_three_subgroup
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 3) (H : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hU : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    IsAbsolutelyIrreducible ((specialLinearNatural (k := F) 3).comp H.subtype) := by
  obtain ⟨U, hUH, hU, hn⟩ := hU
  let K := AlgebraicClosure F
  let ρ := (specialLinearNatural (k := F) 3).comp H.subtype
  let σ := extendScalars K ρ
  let τ := σ.comp (Subgroup.inclusion hUH)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Group.IsNilpotent U := hU.isNilpotent
  obtain ⟨n, hncard⟩ := hU.exists_card_eq
  have hchar : ringChar K = 0 ∨
      (Nat.Prime (ringChar K) ∧ Nat.Coprime (ringChar K) (Nat.card U)) := by
    right
    rw [ringChar.eq K p, hncard]
    exact ⟨Fact.out, ((Nat.coprime_primes Fact.out Fact.out).2 hp).pow_right n⟩
  have hf : Function.Injective σ := (extendScalars_faithful_iff K ρ).mp
    ((specialLinearNatural_injective 3).comp Subtype.val_injective)
  have hi : IsIrreducible τ :=
    isIrreducible_of_finrank_eq_three_of_odd_card τ
      (isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime τ hchar)
      (hf.comp (fun _ _ h => Subtype.ext (congrArg (fun x : H => x.val) h)))
      (by simp [K])
      (by rw [hncard]; exact (by decide : Odd 3).pow) hn
  refine ⟨?_⟩
  change IsIrreducible σ
  let : IsIrreducible τ := hi
  let : Nontrivial (K ⊗[F] (Fin 3 → F)) :=
    Subrepresentation.irreducible_module_nontrivial τ
  refine ⟨fun W => ?_⟩
  let W' : Subrepresentation τ :=
    ⟨W.toSubmodule, fun u _ hv => W.apply_mem_toSubmodule (Subgroup.inclusion hUH u) hv⟩
  rcases hi.eq_bot_or_eq_top W' with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun X : Subrepresentation τ => X.toSubmodule) h))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun X : Subrepresentation τ => X.toSubmodule) h))

end Matrix.SL3.SplitMonomial
