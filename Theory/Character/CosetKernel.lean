module

public import Theory.Representation.CharacterFixedDimension

/-!
# A character criterion for a subgroup to act trivially

Suppose a finite subgroup P has no fixed vectors in a complex representation.
If the character is constant on every coset xH for x in P other than the
identity, then H acts trivially. Sum the character over P × H: the P-norm
operator makes the sum zero, while constancy on the nonidentity cosets makes
it the character sum over H minus |H| times the degree. The H-fixed space
therefore has the full dimension.

This proves, in a slightly more general form, Lemma 3.1 of Glauberman,
*A Characterization of the Suzuki Groups* (1968), p. 83. Normality and the
complement conditions in the source are unnecessary for this averaging proof.
The paper is saved under `refs/original/n-group-global/odd-core-rank-two-source/`.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- A zero character sum over a subgroup forces the fixed space to vanish. -/
public theorem invariants_eq_bot_of_sum_character_eq_zero
    (ρ : Representation ℂ G V) (P : Subgroup G) [Finite P]
    (hsum : ∑ x : P, ρ.character (x : G) = 0) :
    Representation.invariants (ρ.comp P.subtype) = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  apply Representation.finrank_invariants_eq_of_sum_character (ρ.comp P.subtype) 0
  simpa [Representation.character] using hsum

/-- Coset constancy off the identity, together with no P-fixed vectors,
forces H into the representation kernel. -/
public theorem le_ker_of_invariants_eq_bot_of_character_mul (ρ : Representation ℂ G V)
    (P H : Subgroup G) [Finite P] [Finite H]
    (hfix : Representation.invariants (ρ.comp P.subtype) = ⊥)
    (hchar : ∀ x : P, x ≠ 1 → ∀ y : H,
      ρ.character ((x : G) * y) = ρ.character x) : H ≤ ρ.ker := by
  classical
  have hnorm : Representation.norm (ρ.comp P.subtype) = 0 := by
    ext v
    have hv : Representation.norm (ρ.comp P.subtype) v ∈
        Representation.invariants (ρ.comp P.subtype) :=
      fun x => Representation.self_norm_apply (ρ.comp P.subtype) x v
    simpa [hfix] using hv
  have hsumP : ∑ x : P, ρ.character (x : G) = 0 := by
    have ht := congrArg (LinearMap.trace ℂ V) hnorm
    simpa [Representation.norm, Representation.character, map_sum] using ht
  have hdouble : ∑ x : P, ∑ y : H, ρ.character ((x : G) * y) = 0 := by
    have ht := congrArg (fun f : Module.End ℂ V =>
      LinearMap.trace ℂ V (f * Representation.norm (ρ.comp H.subtype))) hnorm
    rw [Finset.sum_comm]
    simpa [Representation.norm, Representation.character, Finset.sum_mul,
      Finset.mul_sum, map_sum, map_mul] using ht
  have hsumH : ∑ y : H, ρ.character (y : G) =
      (Nat.card H : ℂ) * (Module.finrank ℂ V : ℂ) := by
    have heach (x : P) : (∑ y : H, ρ.character ((x : G) * y)) =
        (Nat.card H : ℂ) * ρ.character x +
          if x = 1 then (∑ y : H, ρ.character (y : G)) -
            (Nat.card H : ℂ) * ρ.character 1 else 0 := by
      by_cases hx : x = 1
      · subst x
        simp
      · simp [hx, hchar x hx]
    simp_rw [heach] at hdouble
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumP] at hdouble
    exact sub_eq_zero.mp (by simpa [ρ.char_one] using hdouble)
  have htop : Representation.invariants (ρ.comp H.subtype) = ⊤ :=
    Submodule.eq_top_of_finrank_eq
      (Representation.finrank_invariants_eq_of_sum_character (ρ.comp H.subtype)
        (Module.finrank ℂ V) hsumH)
  intro y hy
  rw [MonoidHom.mem_ker]
  ext v
  have hv : v ∈ Representation.invariants (ρ.comp H.subtype) := by simp [htop]
  exact hv ⟨y, hy⟩

end Representation
