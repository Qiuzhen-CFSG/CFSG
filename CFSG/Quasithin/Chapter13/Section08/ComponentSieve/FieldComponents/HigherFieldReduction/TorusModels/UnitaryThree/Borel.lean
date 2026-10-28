module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Setup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel.Quotients

/-!
# The unitary Borel residual and its full torus quotient

For any specified Sylow two-subgroup S of SU₃(2ⁿ) or PSU₃(2ⁿ), with n > 1,
put B₀ = N(S) and B = O²(B₀). Then B = B₀ and O₂(B) = O₂(B₀) = S.
The imported quotient construction gives actual multiplicative equivalences
B₀/O₂(B₀) ≃ Eˣ (special case) and Eˣ modulo the norm-one cube roots
(projective case), with their values on every transported torus matrix.

The proof transports the standard full Borel residual calculation through
an equivalence that marks both S and its normalizer. It does not identify
the Borel with the smaller norm-one root–torus join.

Source: Aschbacher–Smith 13.8.20, printed p.954, combined manuscript p.971.
The automorphism calculation using these coordinates is a separate result.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus
open CFSG.Quasithin.ChapterF.Source.Unitary
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree

private theorem borelResidual_eq_of_equiv {G H : Type*} [Group G] [Group H]
    (B : Subgroup G) (C : Subgroup H) (e : B ≃* C)
    (hC : pResidual 2 C = ⊤) : borelResidual B = B := by
  have he := map_pResidual 2 e.symm
  rw [hC, map_top_of_surjective _ e.symm.surjective] at he
  rw [borelResidual, residualIn, ← he, ← MonoidHom.range_eq_map, range_subtype]

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (n : ℕ) (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
variable (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
include n hn hcard hconj

/-- For every specified special Sylow, the full normalizer is its own two-residual. -/
theorem su_borelResidual_eq (S : Sylow 2 J.specialSubgroup) :
    borelResidual (normalizer (S : Set J.specialSubgroup)) =
      normalizer (S : Set J.specialSubgroup) := by
  have hn₀ : 0 < n := by omega
  let : CharP E 2 := charP_two n hn₀ hcard
  obtain ⟨e, _, hB⟩ := su_borel_model J n hn₀ hcard hconj S
  apply borelResidual_eq_of_equiv _ _ (subgroupEquiv e hB)
  apply specialBorel_twoResidual (FormTransport.standardForm J) rfl hcard
    (fixed_card (FormTransport.standardForm J) n hn₀ hcard hconj)
  · simpa only [pow_one] using (pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) hn)
  · exact (suTorus_card (FormTransport.standardForm J) rfl) ▸
      suTorus_odd (FormTransport.standardForm J) rfl n hn₀ hcard

/-- For every specified projective Sylow, the full normalizer is its own two-residual. -/
theorem psu_borelResidual_eq (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    borelResidual (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))) =
      normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hn₀ : 0 < n := by omega
  let : CharP E 2 := charP_two n hn₀ hcard
  obtain ⟨e, _, hB⟩ := psu_borel_model J n hn₀ hcard hconj S
  apply borelResidual_eq_of_equiv _ _ (subgroupEquiv e hB)
  apply projectiveBorel_twoResidual (FormTransport.standardForm J) rfl hcard
    (fixed_card (FormTransport.standardForm J) n hn₀ hcard hconj)
  · simpa only [pow_one] using (pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) hn)
  · exact (suTorus_card (FormTransport.standardForm J) rfl) ▸
      suTorus_odd (FormTransport.standardForm J) rfl n hn₀ hcard

/-- The embedded two-core of the special Borel residual is the specified Sylow. -/
theorem su_borelResidual_twoCore (S : Sylow 2 J.specialSubgroup) :
    (borelResidual (normalizer (S : Set J.specialSubgroup))).pCoreIn 2 =
      (S : Subgroup J.specialSubgroup) := by
  rw [su_borelResidual_eq J n hn hcard hconj S, sylowNormalizer_twoCore]

/-- The embedded two-core of the projective Borel residual is the specified Sylow. -/
theorem psu_borelResidual_twoCore (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    (borelResidual (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)))).pCoreIn 2 =
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rw [psu_borelResidual_eq J n hn hcard hconj S, sylowNormalizer_twoCore]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
