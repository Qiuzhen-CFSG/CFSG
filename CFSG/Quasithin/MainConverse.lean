module

public import CFSG.Quasithin.ClassificationModels
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.MainConverse.SmallModels
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
public import CFSG.Quasithin.MainConverse.ModelCases

/-!
# The converse of the quasithin classification

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2 (printed p.4), repeated as Theorem
0.1.1 on p.482. Within finite nonabelian simple groups satisfying proper K,
each listed model satisfies QT and E. K is instantiated with the complete
known-simple carrier catalogue. Unitary q is the fixed-field order, and the
small nonsimple Lie groups contribute their actual derived carriers.

The proof splits the exact classification output into its rank-one, rank-two,
alternating, odd-classical and sporadic branches and applies their concrete
local calculations. All model witnesses and parameter bounds are retained.
`quasithin_and_evenCharacteristic_of_model` proves both local conclusions.
`isQTKE_of_model_of_properK` packages them with the supplied proper-K hypothesis
for `KnownSimple.IsKnownSimple`; the simple-group wrapper retains the full
source domain in its conclusion.

All previous family results remain public. The stronger Suzuki converse also
instantiates its independent simple-section proof with the complete catalogue.
-/

namespace CFSG.Quasithin.MainConverse

open ClassificationModels

variable {G : Type*} [Group G] [Finite G]

/-- Both local conditions for every rank-one model in the source list. -/
public theorem bender_quasithin_and_evenCharacteristic [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hG : IsBenderModel G) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  cases hG with
  | linear _f hf iso => exact ⟨psl2_quasithin hf iso, psl2_evenCharacteristic hna hf iso⟩
  | unitary _f hf iso => exact ⟨psu3_quasithin hf iso, psu3_evenCharacteristic hna hf iso⟩
  | suzuki _m hm iso =>
    obtain ⟨e⟩ := iso
    exact ⟨suzuki_quasithin_of_iso hm e, suzuki_evenCharacteristic_of_iso hm e⟩

/-- Both local conditions for the complete rank-two list, including general
Ree groups and all three small endpoints. Each branch retains its exact witness. -/
public theorem rankTwo_quasithin_and_evenCharacteristic {f : ℕ}
    (hG : IsRankTwoModel G f) : IsQuasithin G ∧ IsEvenCharacteristic G := by
  cases hG with
  | linear hf iso => exact psl3_two_pow_quasithin_and_evenCharacteristic hf iso
  | unitary_four hf iso => exact psu4_two_pow_quasithin_and_evenCharacteristic hf iso
  | unitary_five hf iso => exact psu5_two_pow_quasithin_and_evenCharacteristic hf iso
  | symplectic hf iso => exact psp4_two_pow_quasithin_and_evenCharacteristic hf iso
  | g2 hf iso => exact ExceptionalLocal.g2_even_quasithin_evenCharacteristic hf iso
  | triality hf iso =>
    exact ExceptionalLocal.triality_even_quasithin_evenCharacteristic hf iso
  | ree_f4 _m hm _ iso =>
    obtain ⟨e⟩ := iso
    exact ReeLocal.quasithin_evenCharacteristic_of_iso hm e
  | symplectic_derived _ iso =>
    obtain ⟨e⟩ := iso
    exact symplectic_derived_quasithin_and_evenCharacteristic_of_iso e
  | g2_derived _ iso =>
    obtain ⟨e⟩ := iso
    exact ExceptionalLocal.g2_binary_derived_quasithin_evenCharacteristic e
  | tits _ iso =>
    obtain ⟨e⟩ := iso
    exact ExceptionalLocal.tits_model_quasithin_evenCharacteristic e

/-- All eleven sporadic alternatives satisfy the source's two local conditions. -/
public theorem sporadic_quasithin_and_evenCharacteristic (hG : IsSporadicModel G) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨name, ⟨e⟩⟩ := hG
  cases name with
  | m11 => exact m11_quasithin_and_evenCharacteristic_of_iso e
  | m12 => exact m12_quasithin_and_evenCharacteristic_of_iso e
  | m22 => exact m22_quasithin_and_evenCharacteristic_of_iso e
  | m23 => exact m23_quasithin_and_evenCharacteristic_of_iso e
  | m24 => exact m24_quasithin_and_evenCharacteristic_of_iso e
  | j2 => exact SporadicLocal.qt_e_of_six_sporadic_equiv (name := .j2) (by simp) e
  | j3 => exact SporadicLocal.qt_e_of_six_sporadic_equiv (name := .j3) (by simp) e
  | j4 => exact SporadicLocal.qt_e_of_six_sporadic_equiv (name := .j4) (by simp) e
  | hs => exact SporadicLocal.qt_e_of_six_sporadic_equiv (name := .hs) (by simp) e
  | he => exact SporadicLocal.qt_e_of_six_sporadic_equiv (name := .he) (by simp) e
  | ru => exact SporadicLocal.qt_e_of_six_sporadic_equiv (name := .ru) (by simp) e

/-- The local conclusions of the full classification converse. Every actual
model alternative supplies QT and E, with no additional local premise. -/
public theorem quasithin_and_evenCharacteristic_of_model [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hG : IsQTKEModel G) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  cases hG with
  | bender model => exact bender_quasithin_and_evenCharacteristic hna model
  | rank_two _f model => exact rankTwo_quasithin_and_evenCharacteristic model
  | linear_binary _n hn iso => exact binary_higher_quasithin_and_evenCharacteristic hn iso
  | symplectic_binary iso => exact psp6_two_quasithin_and_evenCharacteristic iso
  | alternating _n hn iso =>
    obtain ⟨e⟩ := iso
    exact alternating_quasithin_and_evenCharacteristic_of_iso hn e
  | linear_prime p hp hlarge iso =>
    exact odd_classical_qt_and_evenCharacteristic (.inl ⟨p, hp, hlarge, iso⟩)
  | linear_three n hn iso =>
    exact odd_classical_qt_and_evenCharacteristic (.inr (.inl ⟨n, hn, iso⟩))
  | unitary_three n hn iso =>
    exact odd_classical_qt_and_evenCharacteristic (.inr (.inr ⟨n, hn, iso⟩))
  | g2_three iso => exact ExceptionalLocal.g2_three_quasithin_evenCharacteristic iso
  | sporadic model => exact sporadic_quasithin_and_evenCharacteristic model

/-- The complete converse on the approved proper-K induction domain.
K is the full known-simple catalogue; QT and E are proved by the model cases. -/
public theorem isQTKE_of_model_of_properK [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups CFSG.KnownSimple.IsKnownSimple G)
    (hG : IsQTKEModel G) : IsQTKE CFSG.KnownSimple.IsKnownSimple G := by
  obtain ⟨hQT, hE⟩ := quasithin_and_evenCharacteristic_of_model hna hG
  exact ⟨hQT, hK, hE⟩

/-- The same converse retaining the finite nonabelian simple source domain
in the packaged conclusion. -/
public theorem isSimpleQTKE_of_model_of_properK [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups CFSG.KnownSimple.IsKnownSimple G)
    (hG : IsQTKEModel G) : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G :=
  ⟨isQTKE_of_model_of_properK hna hK hG, inferInstance, hna⟩

/-- The earlier stronger Suzuki converse, now instantiated with the full
catalogue. Its proved simple-section calculation supplies proper K as well. -/
public theorem suzuki_isQTKE {m : ℕ} (hm : 1 ≤ m)
    (e : G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    IsQTKE CFSG.KnownSimple.IsKnownSimple G :=
  suzuki_isQTKE_of_catalogue
    (fun _ _ _ _ h => ⟨inferInstance, inferInstance, h.isKnownSimpleCarrier⟩) hm e

end CFSG.Quasithin.MainConverse
