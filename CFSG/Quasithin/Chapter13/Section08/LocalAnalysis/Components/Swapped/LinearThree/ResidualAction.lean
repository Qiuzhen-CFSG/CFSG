module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.Wreath
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.Quasithin.Rank

/-!
# The residual action through a literal wreath quotient

If `X/O₂(X)` is the actual two-triple wreath group, its two-residual maps
onto the cubic base. Subnormal two-core intersection identifies the kernel
of this restriction with `O₂(O²(X))`. The resulting equivalence intertwines
literal conjugation, and transports the computed full dihedral image.
No dihedral-automizer premise or splitting of the extension by `O₂(X)` is
used. The three-rank of the residual quotient is two; a source upper bound
on `m₃(X)` gives equality for the residual itself.

Source use: Aschbacher--Smith 13.8.16(1), printed p.952 (PDF p.969).
The branch assembly still has to construct the source `H₁` and its wreath
quotient, and prove that `L₁` is its two-residual.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.ResidualAction
open WreathModel
variable {X : Type*} [Group X] [Finite X]

/-- The literal residual quotient is the cubic wreath base. -/
noncomputable def residualQuotientEquiv (e : X ⧸ pCore 2 X ≃* W) :
    (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) ≃* cubicBase := by
  let R := pResidual 2 X
  let π := QuotientGroup.mk' (pCore 2 X)
  have hr : (R.map π).map e.toMonoidHom = cubicBase := by
    rw [map_pResidual_of_surjective 2 π (QuotientGroup.mk'_surjective _),
      map_pResidual, twoResidual_eq]
  exact ((inferInstance : R.Normal).isSubnormal.quotientCoreImageEquiv 2).trans
    ((e.subgroupMap (R.map π)).trans (MulEquiv.subgroupCongr hr))

/-- The equivalence uses exactly the ambient two-core quotient map. -/
theorem residualQuotientEquiv_mk (e : X ⧸ pCore 2 X ≃* W) (r : pResidual 2 X) :
    (residualQuotientEquiv e (QuotientGroup.mk' (pCore 2 (pResidual 2 X)) r) : W) =
      e (QuotientGroup.mk' (pCore 2 X) r) := by
  rfl

/-- Literal conjugation on `O²(X)/O₂(O²(X))`. -/
noncomputable def action : X →* MulAut (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) :=
  (quotientAut (pCore 2 (pResidual 2 X))).comp MulAut.conjNormal

/-- Conjugation commutes with the actual residual quotient equivalence. -/
theorem intertwines (e : X ⧸ pCore 2 X ≃* W) (x : X)
    (r : pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) :
    residualQuotientEquiv e (action x r) =
      WreathModel.action (e (QuotientGroup.mk' (pCore 2 X) x)) (residualQuotientEquiv e r) := by
  induction r using Quotient.inductionOn with
  | h r =>
    apply Subtype.ext
    change (residualQuotientEquiv e
      (action x (QuotientGroup.mk' (pCore 2 (pResidual 2 X)) r)) : W) = _
    rw [show action x (QuotientGroup.mk' (pCore 2 (pResidual 2 X)) r) =
      QuotientGroup.mk' (pCore 2 (pResidual 2 X)) (MulAut.conjNormal x r) from
        quotientAut_apply_mk _ _ _, residualQuotientEquiv_mk]
    change e (QuotientGroup.mk' (pCore 2 X) (x * (r : X) * x⁻¹)) = _
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    rfl

/-- The full residual action image is `D₈`, proved from the wreath quotient. -/
noncomputable def actionEquivDihedral (e : X ⧸ pCore 2 X ≃* W) :
    (action (X := X)).range ≃* DihedralGroup 4 := by
  let φ : X →* W := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let c := MulAut.congr (residualQuotientEquiv e)
  have hc : c.toMonoidHom.comp action = WreathModel.action.comp φ := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro r
    change residualQuotientEquiv e (action x ((residualQuotientEquiv e).symm r)) = _
    rw [intertwines, MulEquiv.apply_symm_apply]
    rfl
  have hr : (action (X := X)).range.map c.toMonoidHom = WreathModel.action.range := by
    rw [← MonoidHom.range_comp, hc, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr hφ, ← MonoidHom.range_eq_map]
  exact ((c.subgroupMap (action (X := X)).range).trans (MulEquiv.subgroupCongr hr)).trans
    WreathModel.actionEquivDihedral

/-- The quotient used for the marked section has order nine. -/
theorem residualQuotient_card (e : X ⧸ pCore 2 X ≃* W) :
    Nat.card (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) = 9 :=
  (Nat.card_congr (residualQuotientEquiv e).toEquiv).trans cubicBase_card

/-- The three-rank of the literal residual quotient is two. -/
theorem residualQuotient_threeRank (e : X ⧸ pCore 2 X ≃* W) :
    primeRank 3 (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) = 2 := by
  rw [primeRank_congr 3 (residualQuotientEquiv e), cubicBase_threeRank]

/-- The source three-rank upper bound makes the residual three-rank exactly two. -/
theorem residual_threeRank (e : X ⧸ pCore 2 X ≃* W) (hr : primeRank 3 X ≤ 2) :
    primeRank 3 (pResidual 2 X) = 2 := by
  apply le_antisymm ((primeRank_subgroup_le 3 (pResidual 2 X)).trans hr)
  calc
    2 = primeRank 3 (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) :=
      (residualQuotient_threeRank e).symm
    _ ≤ primeRank 3 (pResidual 2 X) :=
      primeRank_quotient_le_of_isTwoGroup 3 (by decide)
        (pCore 2 (pResidual 2 X)) pCore_isPGroup

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.ResidualAction
end
