module

public import Theory.Character.Monomial
public import Theory.Character.InductionInflation
public import Theory.Character.NilpotentFaithfulInduction
public import Theory.Representation.Quotient
public import Mathlib.GroupTheory.Nilpotent

/-!
# Irreducible characters of finite nilpotent groups are monomial

Strong induction on group order reduces monomiality to two interfaces: faithful
nonlinear irreducibles are induced from a proper subgroup, and monomial
characters inflate to monomial characters. Nonfaithful representations descend
to their strictly smaller kernel quotient on the same vector space. The proper
subgroup case uses transitivity of induction; dimension one is the base case.

The reduction first exposes these interfaces as explicit hypotheses; the final
theorem discharges them using faithful proper induction and induction-inflation
compatibility. Source:
Serre, *Linear Representations of Finite Groups*, the proof of monomiality for
finite nilpotent groups.
-/

public section
noncomputable section
attribute [local instance] Fintype.ofFinite

universe u
namespace Theory.Character

/-- The group-order induction for nilpotent monomiality, with the faithful
proper-induction step and inflation transport exposed as separate hypotheses. -/
theorem nilpotent_irreducible_monomial_of_faithful_step
    (hfaithful : ∀ {H : Type u} [Group H] [Fintype H], Group.IsNilpotent H →
      ∀ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)),
      Representation.IsIrreducible ρ → Function.Injective ρ → n ≠ 1 →
      ∃ (K : Subgroup H), K ≠ ⊤ ∧ ∃ ψ : ClassFunction K,
        IsIrreducibleCharacter ψ ∧ ρ.character = inducedClassFunction K ψ)
    (hinflate : ∀ {H Q : Type u} [Group H] [Fintype H] [Group Q] [Fintype Q]
      (π : H →* Q), Function.Surjective π →
      ∀ (K : Subgroup Q) (linear : K →* ℂ),
      ∃ (L : Subgroup H) (μ : L →* ℂ),
        (fun h => inducedClassFunction K linear (π h)) = inducedClassFunction L μ)
    {G : Type u} [Group G] [Fintype G] (hG : Group.IsNilpotent G)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    ∃ (K : Subgroup G) (linear : K →* ℂ), χ = inducedClassFunction K linear := by
  classical
  suffices ∀ (m : ℕ) {H : Type u} [Group H] [Fintype H], Nat.card H = m →
      Group.IsNilpotent H → ∀ χ : ClassFunction H, IsIrreducibleCharacter χ →
      ∃ (K : Subgroup H) (linear : K →* ℂ), χ = inducedClassFunction K linear by
    exact this (Nat.card G) rfl hG χ hχ
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro H _ _ hcard hH χ hχ
    let := hH
    obtain ⟨n, ρ, hρ, rfl⟩ := hχ
    by_cases hn : n = 1
    · apply monomial_of_finrank_one ρ
      simpa using hn
    by_cases hf : Function.Injective ρ
    · obtain ⟨K, hK, ψ, hψ, heq⟩ := hfaithful hH n ρ hρ hf hn
      have hlt : Nat.card K < m := by
        rw [← hcard]
        exact lt_of_le_of_ne (Nat.card_le_card_of_injective K.subtype K.subtype_injective)
          (fun he => hK (K.eq_top_of_card_eq he))
      obtain ⟨L, linear, hlinear⟩ := ih (Nat.card K) hlt rfl (inferInstance) ψ hψ
      refine ⟨L.map K.subtype,
        linear.comp (L.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom, ?_⟩
      rw [heq, hlinear, inducedClassFunction_trans]
      rfl
    · let N := ρ.ker
      let σ := Representation.quotientOfLEKer ρ N le_rfl
      have hσ : Representation.IsIrreducible σ :=
        (Representation.quotientOfLEKer_irreducible_iff ρ N le_rfl).mpr hρ
      have hlt : Nat.card (H ⧸ N) < m := by
        rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        apply Fintype.card_lt_of_surjective_not_injective (QuotientGroup.mk' N)
          (QuotientGroup.mk'_surjective N)
        intro hinj
        apply hf
        apply ρ.ker_eq_bot_iff.mp
        have hker := (QuotientGroup.mk' N).ker_eq_bot hinj
        simpa [N] using hker
      obtain ⟨K, linear, hlinear⟩ := ih (Nat.card (H ⧸ N)) hlt rfl (inferInstance)
        σ.character ⟨n, σ, hσ, rfl⟩
      obtain ⟨L, μ, hμ⟩ := hinflate (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) K linear
      refine ⟨L, μ, ?_⟩
      rw [← hμ]
      funext g
      have heq := congrFun hlinear (QuotientGroup.mk' N g)
      exact heq

/-- Every irreducible complex character of a finite nilpotent group is induced
from a linear character of a subgroup. -/
theorem nilpotent_irreducible_monomial
    {G : Type u} [Group G] [Fintype G] (hG : Group.IsNilpotent G)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    ∃ (K : Subgroup G) (linear : K →* ℂ), χ = inducedClassFunction K linear :=
  nilpotent_irreducible_monomial_of_faithful_step
    nilpotent_faithful_proper_induction
    exists_inducedClassFunction_linear_comp_surjective hG hχ

end Theory.Character
