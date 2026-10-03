module

public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.Representation.NonsplitFourCyclicity

/-!
# Nonsplit subgroups of the Suzuki matrix group

For `q = 2^(2*m+1)`, every subgroup of the Suzuki matrix group whose order
divides `q² + 1` is cyclic. Every normalizer element of a nontrivial such
subgroup acts on all its elements by one common power of the `q`-Frobenius,
with exponent index less than four.

We map the subgroup into `GL(4,q)`, apply the general nonsplit cyclicity and
Singer normalizer theorems, and transport the conclusions through the faithful
matrix inclusion. No Suzuki subgroup classification is used.

Conjugation is **right conjugation**, `u ↦ g⁻¹ * u * g`.
Source: Huppert--Blackburn, *Finite Groups III*, XI.3.10(a), printed
pp. 190–191, using the Singer-cycle argument of II.7.3.
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII

private theorem field_card (m : ℕ) [Fintype (BinaryGaloisField (2 * m + 1))] :
    Fintype.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 (2 * m + 1) (by omega)

/-- A Suzuki subgroup whose order divides `q²+1` is cyclic. -/
public theorem suzukiMatrixGroup_isCyclic_of_card_dvd_sq_add_one
    (m : ℕ) (_hm : 0 < m) (U : Subgroup (SuzukiMatrixGroup m))
    (hcard : Nat.card U ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) : IsCyclic U := by
  let : Fintype (BinaryGaloisField (2 * m + 1)) := Fintype.ofFinite _
  let f := (SuzukiMatrixSubgroup m).subtype
  have hmap : Nat.card (U.map f) ∣
      Fintype.card (BinaryGaloisField (2 * m + 1)) ^ 2 + 1 := by
    rw [Subgroup.card_map_of_injective (SuzukiMatrixSubgroup m).subtype_injective,
      field_card]
    exact hcard
  let := Representation.isCyclic_of_card_dvd_sq_add_one (U.map f) hmap
  exact (U.equivMapOfInjective f (SuzukiMatrixSubgroup m).subtype_injective).isCyclic.mpr
    inferInstance

/-- Right conjugation by a normalizer element is one common `q`-power on the
whole nontrivial nonsplit subgroup: the index `i < 4` is independent of `u`. -/
public theorem suzukiMatrixGroup_normalizer_eq_frobenius_pow_of_card_dvd_sq_add_one
    (m : ℕ) (hm : 0 < m) (U : Subgroup (SuzukiMatrixGroup m)) (hU : U ≠ ⊥)
    (hcard : Nat.card U ∣ (2 ^ (2 * m + 1)) ^ 2 + 1)
    (g : SuzukiMatrixGroup m) (hg : g ∈ Subgroup.normalizer U) :
    ∃ i : ℕ, i < 4 ∧ ∀ u ∈ U, g⁻¹ * u * g = u ^ ((2 ^ (2 * m + 1)) ^ i) := by
  let : Fintype (BinaryGaloisField (2 * m + 1)) := Fintype.ofFinite _
  let f := (SuzukiMatrixSubgroup m).subtype
  have hf : Function.Injective f := (SuzukiMatrixSubgroup m).subtype_injective
  have hmap : Nat.card (U.map f) ∣
      Fintype.card (BinaryGaloisField (2 * m + 1)) ^ 2 + 1 := by
    rw [Subgroup.card_map_of_injective hf, field_card]
    exact hcard
  have hne : U.map f ≠ ⊥ := fun h => hU ((U.map_eq_bot_iff_of_injective hf).mp h)
  let := suzukiMatrixGroup_isCyclic_of_card_dvd_sq_add_one m hm U hcard
  let : IsCyclic (U.map f) :=
    (U.equivMapOfInjective f hf).isCyclic.mp inferInstance
  have hnorm : f g ∈ Subgroup.normalizer (U.map f) :=
    U.le_normalizer_map f (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  obtain ⟨i, hi, hpow⟩ :=
    Representation.normalizer_eq_frobenius_pow_of_card_dvd_sq_add_one
      (U.map f) hne hmap (f g) hnorm
  refine ⟨i, hi, fun u hu => hf ?_⟩
  simpa only [map_mul, map_inv, map_pow, field_card] using
    hpow (f u) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)

end BenderSuzuki.MatrixGroups
