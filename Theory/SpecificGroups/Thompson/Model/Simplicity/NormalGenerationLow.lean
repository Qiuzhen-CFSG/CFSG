module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.PrimeRepresentatives
public import Theory.SpecificGroups.Thompson.Model.Simplicity.Reduction
import Mathlib.Tactic.Group

/-!
# Normal generation by low Thompson prime words

The involution and first order-three representative normally generate using
`(ab)^19 = 1`. For the squared commutator (the proposed 5A representative),
killing it makes the three conjugates of `a` under `b` commute. Their product
is `(ab)^3`, so `(ab)^6 = 1` in the quotient. The coprime exponents 6 and 19
then kill `ab`, which already normally generates the model.

The two other order-three words require separate certificates. The assembly
lemma keeps those two obligations explicit.

Source: the ATLAS Thompson conjugacy-class word table,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ ; matrix provenance is recorded
in `Model/source/README.md`. No asserted class identification is used.
-/

namespace Thompson.Simplicity

private theorem product_pow_six_of_commutator_sq {G : Type*} [Group G]
    (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
    (hc : (a⁻¹ * b⁻¹ * a * b) ^ 2 = 1) : (a * b) ^ 6 = 1 := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  let c := b⁻¹ * a * b
  have hci : c⁻¹ = c := by dsimp [c]; simp [hai, mul_assoc]
  have hac : Commute a c := by
    change a * c = c * a
    have h : (a * c)⁻¹ = a * c :=
      inv_eq_of_mul_eq_one_right (by simpa [c, hai, mul_assoc, pow_two] using hc)
    simpa [mul_inv_rev, hai, hci] using h.symm
  let d := b * a * b⁻¹
  have hdi : d⁻¹ = d := by dsimp [d]; simp [hai, mul_assoc]
  have hbd : b * a * b⁻¹ = d := rfl
  have hcd : Commute d a := by
    change d * a = a * d
    have h := congrArg (fun x => b * x * b⁻¹) hac.eq
    simpa [c, d, mul_assoc] using h
  have hb2 : b * b = b⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [pow_succ, pow_two, mul_assoc] using hb
  have hdc : Commute c d := by
    have h := congrArg (fun x => b * x * b⁻¹) hcd.eq
    have hconj : b * d * b⁻¹ = c := by
      dsimp [c, d]
      calc
        b * (b * a * b⁻¹) * b⁻¹ = (b * b) * a * (b * b)⁻¹ := by group
        _ = b⁻¹ * a * b := by rw [hb2, inv_inv]
    have h' : (b * d * b⁻¹) * (b * a * b⁻¹) = (b * a * b⁻¹) * (b * d * b⁻¹) := by
      simpa [mul_assoc] using h
    rwa [hconj, hbd] at h'
  have hab3 : (a * b) ^ 3 = a * d * c := by
    dsimp [c, d]
    calc
      (a * b) ^ 3 = a * (b * a * b⁻¹) * (b * b * a * (b * b)⁻¹) * b ^ 3 := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      _ = a * (b * a * b⁻¹) * (b⁻¹ * a * b) := by rw [hb2, inv_inv, hb, mul_one]
  rw [show 6 = 3 * 2 from rfl, pow_mul, hab3, (hac.mul_left hdc.symm).mul_pow]
  rw [hcd.symm.mul_pow]
  have hc2 : c ^ 2 = 1 := by simpa only [hci, pow_two] using inv_mul_cancel c
  have hd2 : d ^ 2 = 1 := by simpa only [hdi, pow_two] using inv_mul_cancel d
  rw [ha, hc2, hd2]
  simp

/-- Killing the squared commutator kills the whole Thompson model. -/
public theorem normalClosure_primeRepresentative_four_of_ab19
    (hab19 : (generatorA * generatorB) ^ 19 = 1) :
    Subgroup.normalClosure ({primeRepresentative 4} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative 4} : Set Model)
  let q := QuotientGroup.mk' N
  have hrN : primeRepresentative 4 ∈ N :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hqr : q (primeRepresentative 4) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hrN
  have ha : (q generatorA) ^ 2 = 1 := by simpa using congrArg q generatorA_sq
  have hb : (q generatorB) ^ 3 = 1 := by simpa using congrArg q generatorB_cube
  have hc : ((q generatorA)⁻¹ * (q generatorB)⁻¹ * q generatorA * q generatorB) ^ 2 = 1 := by
    simpa [primeRepresentative, commutatorWord] using hqr
  have hab6 : (q generatorA * q generatorB) ^ 6 = 1 :=
    product_pow_six_of_commutator_sq _ _ ha hb hc
  have hab19' : (q generatorA * q generatorB) ^ 19 = 1 := by
    simpa using congrArg q hab19
  have habN : generatorA * generatorB ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (generatorA * generatorB) = 1
    rw [map_mul]
    exact (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 6 19)).mp ⟨hab6, hab19'⟩
  have hle : Subgroup.normalClosure ({generatorA * generatorB} : Set Model) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using habN)
  rw [normalClosure_ab] at hle
  exact top_unique hle

/-- Assemble the five low-index cases from the two remaining order-three
normal-generation certificates. The caller must discharge both certificates. -/
public theorem normalClosure_primeRepresentative_low_of_three_cases
    (hab19 : (generatorA * generatorB) ^ 19 = 1)
    (hthreeB : Subgroup.normalClosure ({primeRepresentative 2} : Set Model) = ⊤)
    (hthreeC : Subgroup.normalClosure ({primeRepresentative 3} : Set Model) = ⊤)
    (i : Fin 9) (hi : i.val ≤ 4) :
    Subgroup.normalClosure ({primeRepresentative i} : Set Model) = ⊤ := by
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · simpa only [primeRepresentative, Matrix.cons_val_zero] using
      normalClosure_generatorA_of_ab19 hab19
  · simpa only [primeRepresentative, Matrix.cons_val_one, Matrix.cons_val_zero] using
      normalClosure_generatorB_of_ab19 hab19
  · exact hthreeB
  · exact hthreeC
  · exact normalClosure_primeRepresentative_four_of_ab19 hab19

end Thompson.Simplicity
