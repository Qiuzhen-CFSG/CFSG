module

public import Theory.Character.ModularBlock.Congruence
public import Theory.Character.GaloisAction

/-!
# Galois stability of the principal congruence block

Every complex automorphism acts on the roots of unity of order `|G|` by a
single exponent coprime to `|G|`. The character Galois formula then identifies
the transformed character with substitution of that power in its argument.
Coprime powering preserves conjugacy-class sizes, so its central-character
values are the original central-character values on the powered classes.
The principal character is constant one, and its central-character values
are unchanged by this substitution. Thus all principal-block congruences
remain valid for the original chosen ideal.

This combines the central-character congruence criterion in `Congruence`
with the character Galois formula of Peterfalvi (1.9), formalized in
`GaloisAction`. The argument requires neither invariance nor transport of
the prime ideal.
-/

noncomputable section
open ModularBlock PrincipalBlockConstruction BlockPreliminaries

private theorem class_card_pow {G : Type*} [Group G] [Finite G]
    {e : ℕ} (he : e.Coprime (Nat.card G)) (g : G) :
    Nat.card (ConjClasses.mk (g ^ e)).carrier = Nat.card (ConjClasses.mk g).carrier := by
  let f : (ConjClasses.mk g).carrier → (ConjClasses.mk (g ^ e)).carrier :=
    fun x => ⟨x.1 ^ e, ConjClasses.mem_carrier_iff_mk_eq.mpr
      (ConjClasses.mk_eq_mk_iff_isConj.mpr
        ((ConjClasses.mk_eq_mk_iff_isConj.mp
          (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)).pow e))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact he.symm.pow_left_bijective.injective (congrArg Subtype.val h)
    · intro y
      have hy := ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp y.2)
      obtain ⟨c, hc⟩ := isConj_iff.mp hy.symm
      refine ⟨⟨c * g * c⁻¹, ConjClasses.mem_carrier_iff_mk_eq.mpr
        (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨c, rfl⟩).symm)⟩, ?_⟩
      apply Subtype.ext
      exact (conj_pow).trans hc
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem roots_power {n : ℕ} (hn : n ≠ 0) {η : ℂ}
    (hη : IsPrimitiveRoot η n) (σ : ℂ ≃+* ℂ) :
    ∃ e : ℕ, e.Coprime n ∧ ∀ z : ℂ, z ^ n = 1 → σ z = z ^ e := by
  let : NeZero n := ⟨hn⟩
  obtain ⟨e, _, he, hpow⟩ := hη.isPrimitiveRoot_iff.mp
    (hη.map_of_injective σ.injective)
  refine ⟨e, he, ?_⟩
  intro z hz
  obtain ⟨k, _, rfl⟩ := hη.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← hpow, ← pow_mul, ← pow_mul, Nat.mul_comm]

namespace ModularBlock.PrincipalBlockConstruction.PrincipalCongruenceBlockData
variable {G : Type*} [Group G] [Finite G]

/-- Coprime power substitution preserves membership in the principal congruence
block. -/
public theorem mem_block_of_argumentPow (b : PrincipalCongruenceBlockData G)
    {e : ℕ} (he : e.Coprime (Nat.card G)) (i j : b.I)
    (htransport : ∀ g, b.chi j (ConjClasses.mk g) = b.chi i (ConjClasses.mk (g ^ e)))
    (hi : i ∈ b.block) : j ∈ b.block := by
  have hcentral (g : G) :
      centralCharacterInCyclotomicOrder b.eta_spec (b.chi j) (b.complete.1 j)
          (ConjClasses.mk g) =
        centralCharacterInCyclotomicOrder b.eta_spec (b.chi i) (b.complete.1 i)
          (ConjClasses.mk (g ^ e)) := by
    apply Subtype.ext
    change ordinaryCentralCharacterValue _ _ = ordinaryCentralCharacterValue _ _
    simp only [ordinaryCentralCharacterValue, htransport, one_pow, class_card_pow he]
  have hprincipal (g : G) :
      centralCharacterInCyclotomicOrder b.eta_spec (b.chi b.principal)
          (b.complete.1 b.principal) (ConjClasses.mk (g ^ e)) =
        centralCharacterInCyclotomicOrder b.eta_spec (b.chi b.principal)
          (b.complete.1 b.principal) (ConjClasses.mk g) := by
    apply Subtype.ext
    change ordinaryCentralCharacterValue _ _ = ordinaryCentralCharacterValue _ _
    simp only [ordinaryCentralCharacterValue, b.principal_eq,
      ordinaryPrincipalCharacter_apply, class_card_pow he]
  rw [b.mem_block_iff] at hi ⊢
  apply (sameTwoBlock_iff _ _ _ _ _ _).mpr
  intro c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  rw [hcentral, ← hprincipal]
  exact (sameTwoBlock_iff _ _ _ _ _ _).mp hi (ConjClasses.mk (g ^ e))

/-- An irreducible row obtained by a complex automorphism from a row in the
principal congruence block also belongs to that block. -/
public theorem mem_block_of_galois (b : PrincipalCongruenceBlockData G)
    (σ : ℂ ≃+* ℂ) (i j : b.I)
    (htransport : ∀ g, b.chi j (ConjClasses.mk g) = σ (b.chi i (ConjClasses.mk g)))
    (hi : i ∈ b.block) : j ∈ b.block := by
  obtain ⟨e, he, hroot⟩ := roots_power (Nat.card_pos (α := G)).ne' b.eta_spec σ
  apply b.mem_block_of_argumentPow he i j _ hi
  intro g
  rw [htransport]
  obtain ⟨n, ρ, hρ⟩ := (b.complete.1 i).1
  rw [hρ]
  exact Section1.representation_character_apply_galois_eq_argumentPow
    (τ := σ.toRatAlgEquiv) hroot ρ dvd_rfl g

/-- Arbitrary complex automorphisms preserve the actual principal congruence
block, with no invariance hypothesis on the chosen prime ideal. -/
public theorem mem_block_iff_of_galois (b : PrincipalCongruenceBlockData G)
    (σ : ℂ ≃+* ℂ) (i j : b.I)
    (htransport : ∀ g, b.chi j (ConjClasses.mk g) = σ (b.chi i (ConjClasses.mk g))) :
    i ∈ b.block ↔ j ∈ b.block := by
  constructor
  · exact b.mem_block_of_galois σ i j htransport
  · apply b.mem_block_of_galois σ.symm j i
    intro g
    rw [htransport, σ.symm_apply_apply]

end ModularBlock.PrincipalBlockConstruction.PrincipalCongruenceBlockData
