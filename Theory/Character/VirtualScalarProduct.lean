module

public import Theory.Character.CharacterValues
public import Theory.Character.ScalarProductMultiplicity

/-!
# Integral scalar products of virtual characters

Expand both virtual characters as finite integer combinations of ordinary
characters. Each ordinary scalar product is the dimension of an intertwiner
space, so the expanded scalar product is an integer.

Extracted from Peterfalvi Section 1 infrastructure in
`FeitThompson/PFsection1/PFsection1_5.lean` and `PFsection1_7_Core.lean`.
The multiplicity calculation is Mathlib's
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`, through
`IsCharacter.scalarProduct_nat`.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

private lemma scalarProduct_fintype_sum_left
    {G ι : Type*} [Finite G] [Fintype ι]
    (Phi : ι → ClassFunction G) (psi : ClassFunction G) :
    scalarProduct G (fun g => ∑ i, Phi i g) psi =
      ∑ i, scalarProduct G (Phi i) psi := by
  unfold scalarProduct
  calc
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, (∑ i : ι, Phi i g) * star (psi g)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ∑ i : ι, Phi i g * star (psi g) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            rw [Finset.sum_mul]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ i : ι, ∑ g : G, Phi i g * star (psi g) := by
          congr 1
          rw [Finset.sum_comm]
    _ = ∑ i : ι, (Nat.card G : ℂ)⁻¹ * ∑ g : G, Phi i g * star (psi g) := by
          rw [Finset.mul_sum]
    _ = ∑ i : ι, scalarProduct G (Phi i) psi := by
          rfl

private lemma scalarProduct_fintype_sum_right
    {G ι : Type*} [Finite G] [Fintype ι]
    (phi : ClassFunction G) (Psi : ι → ClassFunction G) :
    scalarProduct G phi (fun g => ∑ i, Psi i g) =
      ∑ i, scalarProduct G phi (Psi i) := by
  unfold scalarProduct
  calc
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, phi g * star (∑ i : ι, Psi i g)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ∑ i : ι, phi g * star (Psi i g) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            calc
              phi g * star (∑ i : ι, Psi i g) = phi g * ∑ i : ι, star (Psi i g) := by
                simp
              _ = ∑ i : ι, phi g * star (Psi i g) := by
                rw [Finset.mul_sum]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ i : ι, ∑ g : G, phi g * star (Psi i g) := by
          congr 1
          rw [Finset.sum_comm]
    _ = ∑ i : ι, (Nat.card G : ℂ)⁻¹ * ∑ g : G, phi g * star (Psi i g) := by
          rw [Finset.mul_sum]
    _ = ∑ i : ι, scalarProduct G phi (Psi i) := by
          rfl

/-- The scalar product of two virtual characters is integral. -/
public theorem IsVirtualCharacter.scalarProduct_int
    {G : Type*} [Group G] [Finite G]
    {χ ψ : ClassFunction G}
    (hχ : IsVirtualCharacter χ)
    (hψ : IsVirtualCharacter ψ) :
    ∃ z : ℤ, scalarProduct G χ ψ = (z : ℂ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  rcases hψ with ⟨s, m', n', σ, rfl⟩
  have hpair :
      ∀ i : Fin r, ∀ j : Fin s,
        ∃ k : ℕ, scalarProduct G ((ρ i).character) ((σ j).character) = (k : ℂ) := by
    intro i j
    exact IsCharacter.scalarProduct_nat
      ⟨n i, ρ i, rfl⟩ ⟨n' j, σ j, rfl⟩
  choose k hk using hpair
  refine ⟨∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j, ?_⟩
  have hcalc :
      scalarProduct G
          (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
          (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) =
        ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := by
    rw [scalarProduct_fintype_sum_left]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [scalarProduct_fintype_sum_right]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    change
      scalarProduct G
          ((m i : ℂ) • (ρ i).character)
          ((m' j : ℂ) • (σ j).character) =
        (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ)
    rw [scalarProduct_smul_left, scalarProduct_smul_right, hk i j]
    simp
    ring
  calc
    scalarProduct G
        (virtualCharacterOfRepresentations r m n ρ)
        (virtualCharacterOfRepresentations s m' n' σ)
        =
          scalarProduct G
            (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
            (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) := by
          rfl
    _ = ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := hcalc
    _ = ((∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j : ℤ) : ℂ) := by
          simp [Int.cast_sum, Int.cast_mul, mul_assoc]


