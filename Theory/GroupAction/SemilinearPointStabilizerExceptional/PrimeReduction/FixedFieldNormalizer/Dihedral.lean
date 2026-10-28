module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.FixedFieldNormalizer.FixedPoints
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.GroupTheory.PrimeSubgroupInvolution

/-!
# The actual coefficient normalizer is dihedral

The fixed-field argument gives normalizer order 2p and centralizer Γ.
Cauchy's theorem supplies an involution in this normalizer. Its order keeps
it outside Γ and therefore outside the centralizer. Nontrivial involutory
conjugation on the prime-order subgroup inverts it. The subgroup and this
involution generate the entire normalizer by their orders; the explicit
cyclic-inverted presentation produces the genuine dihedral equivalence.

Source: GLS, Volume 4, Chapter 1, Lemma 3.9,
`refs/KGroup/GLS4/Chapter1.tex`, lines 449–451. This argument includes p = 3.
-/

public section

open Subgroup
namespace MulAction.SemilinearPointStabilizer.Coordinates
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
variable [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)
include c

/-- The literal coefficient normalizer is dihedral: Cauchy's involution
lies outside Γ, acts nontrivially, and therefore inverts this prime-order group. -/
theorem twoPoint_normalizer_dihedral_of_prime_card {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card (twoPoint (X := X) (F := F)) = p)
    (hNC : ¬ normalizer (twoPoint (X := X) (F := F) : Set X) ≤
      centralizer (twoPoint (X := X) (F := F) : Set X)) :
    Nonempty (normalizer (twoPoint (X := X) (F := F) : Set X) ≃* DihedralGroup p) := by
  let Γ := twoPoint (X := X) (F := F)
  let N := normalizer (Γ : Set X)
  have hNcard : Nat.card N = 2 * p := by rw [c.card_twoPoint_normalizer hNC, hcard]
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (hNcard ▸ dvd_mul_right 2 p)
  have hsX : orderOf (s : X) = 2 := (Subgroup.orderOf_coe s).trans hs
  have hs2 : (s : X) ^ 2 = 1 := hsX ▸ pow_orderOf_eq_one (s : X)
  have hsnot : (s : X) ∉ Γ := by
    intro h
    have hd := orderOf_dvd_natCard (⟨(s : X), h⟩ : Γ)
    rw [Subgroup.orderOf_mk, hsX, hcard] at hd
    exact hodd.not_two_dvd_nat hd
  have hinv : ∀ x ∈ Γ, (s : X) * x * (s : X)⁻¹ = x⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one Γ (hcard ▸ hp)
      (s : X) hs2 s.property with hcomm | hinv
    · exfalso
      apply hsnot
      change (s : X) ∈ twoPoint (X := X) (F := F)
      rw [← c.twoPoint_centralizer_eq hNC]
      exact fun x hx => (hcomm x hx).symm
    · exact hinv
  let J := Γ ⊔ zpowers (s : X)
  have hJN : J ≤ N := sup_le Subgroup.le_normalizer (zpowers_le.mpr s.property)
  have hJcard : Nat.card J = 2 * p := by
    apply Nat.dvd_antisymm
    · exact hNcard ▸ Subgroup.card_dvd_of_le hJN
    · apply hodd.coprime_two_left.mul_dvd_of_dvd_of_dvd
      · have h := orderOf_dvd_natCard (⟨(s : X),
          (le_sup_right : zpowers (s : X) ≤ J) (mem_zpowers (s : X))⟩ : J)
        simpa only [Subgroup.orderOf_mk, hsX] using h
      · exact hcard ▸ Subgroup.card_dvd_of_le (le_sup_left : Γ ≤ J)
  have hJ : J = N := Subgroup.eq_of_le_of_card_ge hJN (hJcard ▸ hNcard.le)
  obtain ⟨e⟩ := Subgroup.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted
    Γ (s : X) c.twoPoint_isCyclic hs2 hsnot hinv
  have e' : Nonempty (N ≃* DihedralGroup (Nat.card Γ)) :=
    ⟨(MulEquiv.subgroupCongr hJ.symm).trans e⟩
  exact hcard ▸ e'

end MulAction.SemilinearPointStabilizer.Coordinates
