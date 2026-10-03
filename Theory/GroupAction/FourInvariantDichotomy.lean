module
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupAction.Invariant
public import Mathlib.Tactic

/-!
# Invariant subgroups of a faithful action on four elements

If a subgroup A of the automorphism group of a four-element group has order
greater than two, then every A-invariant subgroup is trivial or the whole
group. The literal inclusion into the automorphism group supplies faithfulness;
no elementary-abelian assumption is needed.

An intermediate subgroup would have order two. Its unique nonidentity element
would be fixed by all of A. The existing automorphism point-stabilizer bound
then gives |A|≤2, a contradiction. The remaining subgroup orders are one and
four, by Lagrange's theorem.

This elementary finite-action result supplies the invariant-subgroup step in
the actual Section Ten quotient action of Stellmacher (10.1), Journal of
Algebra 190 (1997). The consumer supplies the quotient and its action range.
-/

public theorem four_invariant_eq_bot_or_top
    {W : Type*} [Group W] [Finite W]
    (A : Subgroup (MulAut W)) (hW : Nat.card W = 4) (hA : 2 < Nat.card A)
    (D : Subgroup W) [IsInvariant A W D] : D = ⊥ ∨ D = ⊤ := by
  have hdvd : Nat.card D ∣ 2^2 := by simpa [hW] using D.card_subgroup_dvd_card
  obtain ⟨n, hn, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases n
  · exact Or.inl (Subgroup.card_eq_one.mp heq)
  · have hDcard : Nat.card D = 2 := heq
    obtain ⟨z, hzne, huniq⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hDcard
    have hz : (z : W) ≠ 1 := fun heq => hzne (Subtype.ext heq)
    have hfix : ∀ f ∈ A, f (z : W) = z := by
      intro f hf
      have hmem : f (z : W) ∈ D :=
        (IsInvariant.invariant (A := A) (G := W) (H := D) ⟨f,hf⟩ z).mp z.property
      have hne : (⟨f (z : W), hmem⟩ : D) ≠ 1 := by
        intro heq
        exact hz (f.injective ((congrArg Subtype.val heq).trans (map_one f).symm))
      exact congrArg Subtype.val (huniq _ hne)
    have hbound := card_mulAut_subgroup_le_two_of_fixed_point hW z hz A hfix
    omega
  · exact Or.inr (Subgroup.eq_top_of_card_eq D (heq.trans hW.symm))

