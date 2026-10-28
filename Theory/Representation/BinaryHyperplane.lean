module

public import Theory.Representation.SubrepresentationLattice
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

/-!
# Invariant sets meet binary hyperplanes

If an invariant set avoids a binary hyperplane, all its pairwise differences
lie in that hyperplane. Two distinct members supply a nonzero difference.
The span of these differences is invariant, contradicting irreducibility.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Lemma A.1.43, printed p.32.
-/

public section

namespace Representation.BinaryHyperplane
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]
  [IsIrreducible ρ]

/-- In an irreducible binary module, every hyperplane meets every invariant
set containing more than one vector. -/
theorem invariant_set_meets_hyperplane (S : Set V)
    (hS : ∀ g : G, ∀ s ∈ S, ρ g s ∈ S) (hcard : 1 < Nat.card S)
    (W : Submodule (ZMod 2) V) (hW : Module.finrank (ZMod 2) (V ⧸ W) = 1) :
    ∃ s ∈ S, s ∈ W := by
  classical
  by_contra hn
  push Not at hn
  have htwo : Nat.card (V ⧸ W) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hW]
    simp only [Nat.card_eq_fintype_card, ZMod.card, pow_one]
  obtain ⟨z, _, huniq⟩ := (Nat.card_eq_two_iff' (0 : V ⧸ W)).mp htwo
  have hdiff {s t : V} (hs : s ∈ S) (ht : t ∈ S) : s - t ∈ W := by
    have hs0 : W.mkQ s ≠ 0 := fun h => hn s hs ((Submodule.Quotient.mk_eq_zero W).mp h)
    have ht0 : W.mkQ t ≠ 0 := fun h => hn t ht ((Submodule.Quotient.mk_eq_zero W).mp h)
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change W.mkQ (s - t) = 0
    rw [map_sub, huniq _ hs0, huniq _ ht0, sub_self]
  let D : Submodule (ZMod 2) V := Submodule.span (ZMod 2)
    {v | ∃ s ∈ S, ∃ t ∈ S, v = s - t}
  have hDW : D ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, t, ht, rfl⟩
    exact hdiff hs ht
  let R : Subrepresentation ρ :=
    { toSubmodule := D
      apply_mem_toSubmodule := by
        intro g
        change D ≤ D.comap (ρ g)
        apply Submodule.span_le.mpr
        rintro _ ⟨s, hs, t, ht, rfl⟩
        change ρ g (s - t) ∈ D
        rw [map_sub]
        exact Submodule.subset_span ⟨ρ g s, hS g s hs, ρ g t, hS g t ht, rfl⟩ }
  have : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨s, t, hst⟩ := exists_pair_ne S
  have hd : (s : V) - t ∈ D := Submodule.subset_span ⟨s, s.property, t, t.property, rfl⟩
  have hR : R ≠ ⊥ := by
    intro he
    have hD : D = ⊥ := congrArg Subrepresentation.toSubmodule he
    rw [hD] at hd
    exact hst (Subtype.ext (sub_eq_zero.mp hd))
  have htop : R = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top R).resolve_left hR
  have hDtop : D = ⊤ := congrArg Subrepresentation.toSubmodule htop
  exact hn s s.property (hDW (hDtop.symm ▸ Submodule.mem_top))
end Representation.BinaryHyperplane
