module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.Quaternion
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.NormalCentralizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore
public import Theory.GroupTheory.PCoreSurjective

/-!
# The intrinsic two-core of the standard PSU₄(3) involution centralizer

The projective image Q of the two coordinate quaternion groups is normal
inside the full centralizer C of diag(-1,-1,1,1), has order 32, and contains
its centralizer in C. Two explicit cubic elements show that C/Q has trivial
two-core. The p-core lifting lemma therefore identifies Q with O₂(C), giving
C_C(O₂(C)) ≤ O₂(C).

The matrix calculations retain the determinant-compatible GU₂ blocks, their
interchange, and the full scalar kernel of SU₄ → PSU₄. Normality is relative
to C. The conditional assembly lemmas are preserved, and the final theorems
discharge their premises using the concrete calculations.
Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition E,
printed pp.3–4 of `refs/quasithin.pdf`.
-/

public section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore

/-- Only normality inside the involution centralizer is needed. -/
theorem quaternionCore_le_pCore_of_normal [quaternionCore.Normal] :
    quaternionCore ≤ pCore 2 standardCentralizer :=
  le_sSup ⟨inferInstance, quaternionCore_isPGroup⟩

/-- The remaining quotient calculation identifies the entire intrinsic core. -/
theorem quaternionCore_eq_pCore_of_quotient [quaternionCore.Normal]
    (hq : pCore 2 (standardCentralizer ⧸ quaternionCore) = ⊥) :
    quaternionCore = pCore 2 standardCentralizer := by
  have hk : IsPGroup 2 (QuotientGroup.mk' quaternionCore).ker := by
    rw [QuotientGroup.ker_mk']
    exact quaternionCore_isPGroup
  have he := (QuotientGroup.mk' quaternionCore).comap_pCore_of_ker_isPGroup
    (QuotientGroup.mk'_surjective _) hk
  rw [hq, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at he
  exact he

/-- The quaternion centralizer calculation suffices for the source's core bound. -/
theorem centralizer_pCore_le_of_quaternion [quaternionCore.Normal]
    (hc : Subgroup.centralizer (quaternionCore : Set standardCentralizer) ≤ quaternionCore) :
    Subgroup.centralizer (pCore 2 standardCentralizer : Set standardCentralizer) ≤
      pCore 2 standardCentralizer :=
  (Subgroup.centralizer_le quaternionCore_le_pCore_of_normal).trans
    (hc.trans quaternionCore_le_pCore_of_normal)

/-- The intrinsic two-core is exactly the projective quaternion central product. -/
theorem quaternionCore_eq_pCore : quaternionCore = pCore 2 standardCentralizer := by
  let : quaternionCore.Normal := quaternionCore_normal
  exact quaternionCore_eq_pCore_of_quotient quotient_twoCore_eq_bot

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

/-- The order is obtained from the explicit quaternion kernel calculation. -/
theorem standardCentralizer_twoCore_card : Nat.card (pCore 2 standardCentralizer) = 32 := by
  rw [← RepresentativeCore.quaternionCore_eq_pCore]
  exact RepresentativeCore.quaternionCore_card

/-- The full projective involution centralizer has characteristic two. -/
theorem standardCentralizer_twoCore_centralizer_le :
    Subgroup.centralizer (pCore 2 standardCentralizer : Set standardCentralizer) ≤
      pCore 2 standardCentralizer := by
  rw [← RepresentativeCore.quaternionCore_eq_pCore]
  exact RepresentativeCore.quaternionCore_centralizer_le

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
