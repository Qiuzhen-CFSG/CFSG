module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.MathieuOverlap.Elementary
public import Theory.SpecificGroups.Janko4.Model.SylowOvergroups.PrimeTwentyThree

/-!
# Mathieu placement of the native max4 point parabolics

The eleven certified words give a normal elementary subgroup of order at
least 2048 in each native point parabolic. The native large-subgroup theorem
therefore places the whole parabolic in a conjugate of the Mathieu local.
The supplied ambient Sylow is retained. No arbitrary elementary-normalizer
cover or selection of a source row is assumed.

Source: Aschbacher–Smith 12.5.3–4, printed pp.818–819/PDF pp.835–836.
-/

public noncomputable section
namespace Janko4.LocalStructure.SymmetricLinear
open Subgroup
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

/-- A point parabolic containing the supplied full Sylow lies in a conjugate
of the literal max1 subgroup. -/
theorem pointParabolic_le_conjugate_mathieu (j : Fin 5) (S : Sylow 2 Model)
    (hS : (S : Subgroup Model) ≤ pointParabolic j) :
    ∃ g : Model, pointParabolic j ≤
      (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).map
        (MulAut.conj g).toMonoidHom := by
  obtain ⟨E, hEP, hE, hcard, hnormal⟩ := MathieuOverlap.pointParabolic_large_elementary j
  let := hE
  let F := E.subgroupOf (pointParabolic j)
  let : F.Normal := (normal_subgroupOf_iff_le_normalizer hEP).mpr hnormal
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hEP
  have hF : 2048 ≤ Nat.card F := by
    have he := Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv
    exact hcard.trans_eq he.symm
  exact SylowOvergroups.normal_large_placement S (pointParabolic j) hS F hF

end Janko4.LocalStructure.SymmetricLinear
