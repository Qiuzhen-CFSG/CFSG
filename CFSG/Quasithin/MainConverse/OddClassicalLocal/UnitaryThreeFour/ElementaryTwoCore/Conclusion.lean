module

public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.ElementaryTwoCore
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer.Trace
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.InvolutionTransport
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore

/-!
# PSU₄(3): intrinsic two-cores of normal elementary normalizers

For every nonidentity elementary abelian subgroup R normal in a Sylow
two-subgroup T, the normalizer N of its ambient image satisfies
C_N(O₂(N)) ≤ O₂(N). In particular this holds when N is maximal two-local.
The elementary-normalizer reduction then gives source condition E for
the actual field-nine projective special unitary group.

The trace-zero theorem supplies the only premise of involution-centralizer
transport. The representative calculation identifies its intrinsic two-core
with the normal projective quaternion central product of order 32 and proves
that this core contains its centralizer. The Sylow-centralizer criterion
passes this property to N. All normality is relative to the indicated local
group; the projective calculations retain the full scalar kernel and the
lifts interchanging the two eigenspaces. No local model premises remain.

Source: Aschbacher–Smith, condition E and Theorem 0.1.2(4), printed pp.3–4
of `refs/quasithin.pdf`, repeated on pp.481–482. Unitary conventions are
those of GLS3, chapter 2, §2.7.
-/

public section
namespace CFSG.Quasithin.MainConverse.UnitaryFourThree

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

/-- The intrinsic two-core of a normal elementary normalizer contains its
centralizer. Normality is inside T; maximality of the normalizer is unnecessary. -/
theorem normal_elementary_core
    (T : Sylow 2 (Carrier 4)) (R : Subgroup T) (hR : R ≠ ⊥)
    (hn : R.Normal) (he : IsElementaryAbelian 2 R) :
    let N := Subgroup.normalizer (R.map (T : Subgroup (Carrier 4)).subtype : Set (Carrier 4))
    Subgroup.centralizer (pCore 2 N : Set N) ≤ pCore 2 N :=
  normal_elementary_core_of_centralizer_models
    (centralizer_models_of_trace_zero
      ElementaryLocal.InvolutionCentralizer.trace_eq_zero_of_projective_involution)
    standardCentralizer_twoCore_centralizer_le T R hR hn he

/-- Source condition E at every Sylow two-subgroup of the concrete PSU₄(3). -/
theorem model_evenCharacteristicAt (T : Sylow 2 (Carrier 4)) :
    IsEvenCharacteristicAt T := by
  apply model_evenCharacteristicAt_of_normal_elementary_cores T
  intro R hR hn he N _
  exact normal_elementary_core T R hR hn he

/-- The actual projective SU₄ image over the field of nine elements has even
characteristic, with no assumed local classification or core conditions. -/
theorem model_evenCharacteristic : IsEvenCharacteristic (Carrier 4) :=
  model_evenCharacteristicAt

end CFSG.Quasithin.MainConverse.UnitaryFourThree
