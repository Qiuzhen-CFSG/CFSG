module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Basic

/-!
# Fixed spaces of semilinear involutions in characteristic two

For a nonidentity involutory field automorphism σ, a scalar c with
σ(c)+c=1 is obtained by dividing a moved scalar by its trace. If an involution
acts σ-semilinearly, a fixed vector v is the displacement of c v. The reverse
inclusion follows from square one. Rank-nullity therefore gives a fixed space
of half the binary dimension, without a matrix cocycle-descent assumption.

This is the coefficient-field case of the outer-involution calculation in
Aschbacher–Smith H.7, printed pp.388–389 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace SymplecticConjugatePair.Ambient
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

lemma exists_trace_one (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl F) : ∃ c : F, σ c + c = 1 := by
  have hx : ∃ x : F, σ x ≠ x := by
    by_contra! h
    apply hne
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hx
  have hd : σ x + x ≠ 0 := by
    intro h
    apply hx
    have h' := congrArg (fun z : F => z + x) h
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using h'
  refine ⟨x / (σ x + x), ?_⟩
  rw [map_div₀, map_add, hσ, add_comm x (σ x), ← add_div, div_self hd]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module F V]
  [Module (ZMod 2) V]

lemma semilinear_involution_fixedSpace (ρ : Representation (ZMod 2) G V)
    (s : G) (hs : s^2 = 1) (σ : F ≃+* F)
    (hσ : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl F)
    (hsemi : ∀ c : F, ∀ v : V, ρ s (c • v) = σ c • ρ s v) :
    fixedSpace ρ (Subgroup.zpowers s) = LinearMap.range (ρ s - LinearMap.id) := by
  have hneg (v : V) : -v = v := by
    simpa only [CharTwo.neg_eq, one_smul] using (neg_smul (1 : ZMod 2) v).symm
  have hss (v : V) : ρ s (ρ s v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hs, map_one]
    rfl
  obtain ⟨c, hc⟩ := exists_trace_one σ hσ hne
  ext v
  rw [mem_fixedSpace_zpowers_iff]
  constructor
  · intro hv
    refine ⟨c • v, ?_⟩
    change ρ s (c • v) - c • v = v
    rw [hsemi, hv, sub_eq_add_neg, hneg, ← add_smul, hc, one_smul]
  · rintro ⟨w, rfl⟩
    change ρ s (ρ s w - w) = ρ s w - w
    rw [map_sub, hss, sub_eq_add_neg, sub_eq_add_neg, hneg, hneg,
      add_comm]

lemma semilinear_involution_twice_codim [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (s : G) (hs : s^2 = 1) (σ : F ≃+* F)
    (hσ : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl F)
    (hsemi : ∀ c : F, ∀ v : V, ρ s (c • v) = σ c • ρ s v) :
    2 * fixedCodim ρ (Subgroup.zpowers s) = Module.finrank (ZMod 2) V := by
  have hd := fixedCodim_add_finrank ρ (Subgroup.zpowers s)
  rw [semilinear_involution_fixedSpace ρ s hs σ hσ hne hsemi,
    ← fixedCodim_zpowers_eq_displacement_rank] at hd
  omega

lemma semilinear_pair_involution_codim [Finite F] [Algebra (ZMod 2) F]
    (ρ : Representation (ZMod 2) G (Space F)) {n : ℕ} (hF : Nat.card F = 2^n)
    (s : G) (hs : s^2 = 1) (σ : F ≃+* F)
    (hσ : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl F)
    (hsemi : ∀ c : F, ∀ v : Space F, ρ s (c • v) = σ c • ρ s v) :
    fixedCodim ρ (Subgroup.zpowers s) = 4*n := by
  have hd := semilinear_involution_twice_codim ρ s hs σ hσ hne hsemi
  rw [finrank_space hF] at hd
  omega
end SymplecticConjugatePair.Ambient
