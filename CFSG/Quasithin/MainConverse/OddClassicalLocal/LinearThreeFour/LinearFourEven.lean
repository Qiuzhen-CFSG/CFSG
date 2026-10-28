module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.SylowLocalCentralizerCriterion
public import Theory.SpecificGroups.PSL4Three.TwoLocal.StandardInvolution
public import Theory.SpecificGroups.PSL4Three.TwoLocal.StandardCore
public import Theory.SpecificGroups.PSL4Three.TwoLocal.SylowCenter

/-!
# Even characteristic of PSL₄(3)

A two-local M containing a Sylow two-subgroup T has nontrivial intrinsic
two-core. This core meets the center of T in an involution z. If C_G(z)
has characteristic two, characteristic-two inheritance and the core-centralizer
overgroup criterion give C_M(O₂(M)) ≤ O₂(M).

The block quaternion image extends to a Sylow two-subgroup whose central
involutions all equal the projective image of diag(-1,-1,1,1). The independent
normality and centralizer calculation for this quaternion image proves that
the full projective centralizer has self-centralizing two-core. This calculation
includes anticommuting matrix lifts and block interchange.

The final theorem discharges both model premises of the reductions below.
Sylow conjugacy then gives condition E for every Sylow two-subgroup.
Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, repeated as
Theorem 0.1.1(4), printed p.482, with condition E on pp.3 and 481.
-/

namespace CFSG.Quasithin.MainConverse

open Matrix.PSL4Three.TwoLocal

/-- The centralizer calculations cover every two-local containing a Sylow subgroup;
maximality is not needed for this reduction. -/
public theorem psl4_three_twoLocal_core_of_centralizer_models
    (T : Sylow 2 PSL)
    (hmodels : ∀ z : T, z ∈ Subgroup.center T → orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({(z : PSL)} : Set PSL) ≃* standardCentralizer))
    (hstandard : Subgroup.centralizer (pCore 2 standardCentralizer : Set standardCentralizer) ≤
      pCore 2 standardCentralizer)
    (M : Subgroup PSL) (hM : IsTwoLocal M) (hTM : (T : Subgroup PSL) ≤ M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  apply Subgroup.normalizer_core_selfCentralizing_of_sylow_centralizers T Q hp hQ hTM
  intro z hz ho
  obtain ⟨e⟩ := hmodels z hz ho
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hstandard

/-- Conditional assembly of source condition E from the two intrinsic calculations.
Sylow conjugacy means the centralizer models are needed for only one Sylow subgroup. -/
public theorem psl4_three_evenCharacteristic_of_centralizer_models
    (T : Sylow 2 PSL)
    (hmodels : ∀ z : T, z ∈ Subgroup.center T → orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({(z : PSL)} : Set PSL) ≃* standardCentralizer))
    (hstandard : Subgroup.centralizer (pCore 2 standardCentralizer : Set standardCentralizer) ≤
      pCore 2 standardCentralizer) : IsEvenCharacteristic PSL := by
  apply IsEvenCharacteristicAt.all (T := T)
  intro M hM hTM
  exact psl4_three_twoLocal_core_of_centralizer_models T hmodels hstandard M hM.1 hTM

/-- The concrete projective group PSL₄(3) satisfies condition E for every Sylow
two-subgroup, without additional local or classification hypotheses. -/
public theorem psl4_three_evenCharacteristic :
    IsEvenCharacteristic PSL := by
  obtain ⟨T, hmodels⟩ := exists_sylow_center_centralizer_equiv
  exact psl4_three_evenCharacteristic_of_centralizer_models T hmodels
    standardCentralizer_centralizer_twoCore_le

end CFSG.Quasithin.MainConverse
