module

public import CFSG.Quasithin.Models
public import CFSG.Quasithin.MainConverse.Suzuki
public import CFSG.Quasithin.MainConverse.AlternatingLocal
public import CFSG.Quasithin.MainConverse.EvenLinearLocal
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal
public import CFSG.Quasithin.MainConverse.ExceptionalLocal
public import CFSG.Quasithin.MainConverse.MathieuLocal
public import CFSG.Quasithin.MainConverse.OddClassicalLocal
public import CFSG.Quasithin.MainConverse.RankOneLocal
public import CFSG.Quasithin.MainConverse.ReeLocal
public import CFSG.Quasithin.MainConverse.SporadicLocal

/-!
# Exhaustive model assembly for the quasithin converse

The family modules prove the two local conclusions for their concrete carriers.
This module is the source-facing dispatcher over the complete
`ClassificationModels.IsQTKEModel` predicate.  Every branch keeps the actual
model equivalence and the source parameter restriction; the proper-K hypothesis
is supplied only when the final `IsQTKE` package is formed.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.Quasithin.ClassificationModels
open CFSG.KnownSimple

universe u

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- QT and even characteristic for every actual model in the Main Theorem list.
The nonabelian hypothesis is needed only by the rank-one local E arguments.
All other family calculations are unconditional once their actual model
witness is supplied. -/
public theorem quasithin_and_evenCharacteristic_of_isQTKEModel
    (hna : ¬ IsMulCommutative G) (hmodel : IsQTKEModel G) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  cases hmodel with
  | bender model =>
      cases model with
      | linear f hf iso =>
          exact ⟨psl2_quasithin hf iso, psl2_evenCharacteristic hna hf iso⟩
      | unitary f hf iso =>
          exact ⟨psu3_quasithin hf iso, psu3_evenCharacteristic hna hf iso⟩
      | suzuki m hm iso =>
          rcases iso with ⟨e⟩
          exact ⟨suzuki_quasithin_of_iso hm e,
            suzuki_evenCharacteristic_of_iso hm e⟩
  | rank_two f model =>
      cases model with
      | linear hf iso =>
          exact psl3_two_pow_quasithin_and_evenCharacteristic hf iso
      | unitary_four hf iso =>
          exact psu4_two_pow_quasithin_and_evenCharacteristic hf iso
      | unitary_five hf iso =>
          exact psu5_two_pow_quasithin_and_evenCharacteristic hf iso
      | symplectic hf iso =>
          exact psp4_two_pow_quasithin_and_evenCharacteristic hf iso
      | g2 hf iso =>
          exact ExceptionalLocal.g2_even_quasithin_evenCharacteristic hf iso
      | triality hf iso =>
          exact ExceptionalLocal.triality_even_quasithin_evenCharacteristic hf iso
      | ree_f4 m hm hf iso =>
          rcases iso with ⟨e⟩
          exact ReeLocal.quasithin_evenCharacteristic_of_iso hm e
      | symplectic_derived hf iso =>
          rcases iso with ⟨e⟩
          exact symplectic_derived_quasithin_and_evenCharacteristic_of_iso e
      | g2_derived hf iso =>
          rcases iso with ⟨e⟩
          exact ExceptionalLocal.g2_binary_derived_quasithin_evenCharacteristic e
      | tits hf iso =>
          rcases iso with ⟨e⟩
          exact ExceptionalLocal.tits_model_quasithin_evenCharacteristic e
  | linear_binary n hn iso =>
      rcases hn with rfl | rfl
      · exact psl4_two_quasithin_and_evenCharacteristic iso
      · exact psl5_two_quasithin_and_evenCharacteristic iso
  | symplectic_binary iso =>
      exact psp6_two_quasithin_and_evenCharacteristic iso
  | alternating n hn iso =>
      rcases iso with ⟨e⟩
      exact alternating_quasithin_and_evenCharacteristic_of_iso hn e
  | linear_prime p hp hlarge iso =>
      exact psl2_fermatMersenne_qt_and_evenCharacteristic_of_isPSL hp hlarge iso
  | linear_three n hn iso =>
      exact psl_three_four_qt_and_evenCharacteristic_of_isPSL hn iso
  | unitary_three n hn iso =>
      exact psu_three_four_qt_and_evenCharacteristic_of_isPSU hn iso
  | g2_three iso =>
      exact ExceptionalLocal.g2_three_quasithin_evenCharacteristic iso
  | sporadic model =>
      rcases model with ⟨name, ⟨e⟩⟩
      cases name with
      | m11 => exact m11_quasithin_and_evenCharacteristic_of_iso (G := G) e
      | m12 => exact m12_quasithin_and_evenCharacteristic_of_iso (G := G) e
      | m22 => exact m22_quasithin_and_evenCharacteristic_of_iso (G := G) e
      | m23 => exact m23_quasithin_and_evenCharacteristic_of_iso (G := G) e
      | m24 => exact m24_quasithin_and_evenCharacteristic_of_iso (G := G) e
      | j2 => exact SporadicLocal.j2_qt_e_of_equiv e
      | j3 => exact SporadicLocal.j3_qt_e_of_equiv e
      | j4 => exact SporadicLocal.j4_qt_e_of_equiv e
      | hs => exact SporadicLocal.hs_qt_e_of_equiv e
      | he => exact SporadicLocal.he_qt_e_of_equiv e
      | ru => exact SporadicLocal.ru_qt_e_of_equiv e

/-- Package the assembled local conclusions with an explicitly supplied
proper-K induction hypothesis. -/
public theorem isQTKE_of_isQTKEModel_of_properK {K : GroupClass.{u}}
    (hna : ¬ IsMulCommutative G) (hK : HasProperKSubgroups K G)
    (hmodel : IsQTKEModel G) : IsQTKE K G := by
  obtain ⟨hQT, hE⟩ := quasithin_and_evenCharacteristic_of_isQTKEModel hna hmodel
  exact ⟨hQT, hK, hE⟩

/-- The approved finite nonabelian-simple converse with the full known-simple
catalogue as its K class. -/
public theorem isQTKE_of_isQTKEModel_of_knownSimple_properK
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups IsKnownSimple G) (hmodel : IsQTKEModel G) :
    IsQTKE IsKnownSimple G :=
  isQTKE_of_isQTKEModel_of_properK hna hK hmodel

/-- The same converse in the `IsSimpleQTKE` package used by the global proof. -/
public theorem isSimpleQTKE_of_isQTKEModel_of_knownSimple_properK
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups IsKnownSimple G) (hmodel : IsQTKEModel G) :
    IsSimpleQTKE IsKnownSimple G :=
  ⟨isQTKE_of_isQTKEModel_of_knownSimple_properK hna hK hmodel,
    inferInstance, hna⟩

end CFSG.Quasithin.MainConverse
