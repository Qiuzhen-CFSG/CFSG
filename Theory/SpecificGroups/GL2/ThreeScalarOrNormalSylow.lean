module

public import Theory.SpecificGroups.GL2.ThreeFourCentralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# Subgroups of GL₂(3) avoiding the scalar involution

Every subgroup of order four contains the scalar involution: an element
of order four squares to that scalar, while an elementary four-group is
self-centralizing. Consequently a subgroup avoiding the scalar has order
dividing six and has a normal Sylow three-subgroup.
-/

open Matrix
namespace Matrix.GeneralLinearGroup

private abbrev G := GL (Fin 2) (ZMod 3)

private theorem scalar_mem_of_card_four (K : Subgroup G) (hK : Nat.card K = 4) :
    threeCentral ∈ K := by
  by_contra hn
  have hp (x : K) : x ^ 2 = 1 := by
    have hfour : (x : G) ^ 4 = 1 := by
      exact congrArg Subtype.val (hK ▸ (pow_card_eq_one' (x := x)))
    have hm : ∀ a : Matrix (Fin 2) (Fin 2) (ZMod 3),
        a ^ 4 = 1 → a ^ 2 = 1 ∨ a ^ 2 = threeCentral.val := by decide +kernel
    have hv : (x : G).val ^ 4 = 1 := congrArg Units.val hfour
    rcases hm (x : G).val hv with h | h
    · exact Subtype.ext (Units.ext h)
    · have he : (x : G) ^ 2 = threeCentral := Units.ext h
      exact (hn (he ▸ K.pow_mem x.property 2)).elim
  have hi (x : K) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp x)
  let : IsElementaryAbelian 2 K := {
    toIsMulCommutative := isMulCommutative_iff.mpr fun x y => by
      calc
        x * y = (x * y)⁻¹ := (hi (x * y)).symm
        _ = y⁻¹ * x⁻¹ := _root_.mul_inv_rev x y
        _ = y * x := by rw [hi y, hi x]
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }
  apply hn
  rw [← three_four_centralizer K hK]
  intro x _
  apply Units.ext
  have hm : ∀ a : Matrix (Fin 2) (Fin 2) (ZMod 3),
      a * threeCentral.val = threeCentral.val * a := by decide +kernel
  exact hm x.val

/-- Avoiding the scalar involution forces the subgroup order to divide six. -/
public theorem three_card_dvd_six_of_scalar_not_mem
    (D : Subgroup (GL (Fin 2) (ZMod 3)))
    (hscalar : threeCentral ∉ D) : Nat.card D ∣ 6 := by
  have hfour : ¬4 ∣ Nat.card D := by
    intro hd
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 2 (n := 2) hd
    have hc : Nat.card (K.map D.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective D.subtype_injective, hK]
      norm_num
    have hz := scalar_mem_of_card_four (K.map D.subtype) hc
    exact hscalar ((Subgroup.map_subtype_le K) hz)
  have hd : Nat.card D ∣ 48 := by
    have hG : Nat.card G = 48 := by rw [Matrix.card_GL_field]; decide
    exact hG ▸ D.card_subgroup_dvd_card
  have hle : Nat.card D ≤ 48 := Nat.le_of_dvd (by decide) hd
  interval_cases hn : Nat.card D <;> omega

/-- Every subgroup either contains the scalar involution or has a normal
Sylow three-subgroup. -/
public theorem three_scalar_or_normal_sylow
    (D : Subgroup (GL (Fin 2) (ZMod 3))) :
    threeCentral ∈ D ∨ ∃ P : Sylow 3 D, (P : Subgroup D).Normal := by
  classical
  by_cases hz : threeCentral ∈ D
  · exact Or.inl hz
  right
  let P : Sylow 3 D := default
  refine ⟨P, ?_⟩
  have hd := three_card_dvd_six_of_scalar_not_mem D hz
  have hle : Nat.card D ≤ 6 := Nat.le_of_dvd (by decide) hd
  have hcard := P.card_eq_multiplicity
  have hindex := (P : Subgroup D).card_mul_index
  have hf6 : Nat.factorization 6 3 = 1 := by decide +kernel
  interval_cases hn : Nat.card D <;> try omega
  all_goals norm_num [Nat.factorization_one, Nat.prime_two.factorization,
    Nat.prime_three.factorization, hf6] at hcard
  all_goals simp only [← Nat.card_eq_fintype_card] at hcard
  all_goals first
    | exact (P : Subgroup D).normal_of_index_eq_one (by nlinarith)
    | exact (P : Subgroup D).normal_of_index_eq_two (by nlinarith)

end Matrix.GeneralLinearGroup
