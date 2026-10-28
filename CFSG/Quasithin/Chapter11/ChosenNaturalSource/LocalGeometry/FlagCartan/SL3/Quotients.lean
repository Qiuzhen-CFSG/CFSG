module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SubspaceTransport
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals

/-!
# The literal local PSL₂ quotients in the SL₃ branch

The original normalizer projection identifies each field-subspace stabilizer
with its marked SL₃ parabolic. The checked model residual calculations and
two-group kernel transport give an isomorphism on the literal two-core
quotients of the ambient residuals. This calculation keeps the full SL₃
center; no projectivization of the initial marking is used.

Source: Aschbacher--Smith, opening of §11.1, printed pp.760--761.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}

/-- The stabilizer retained by the marking is the literal natural SL₃ parabolic. -/
theorem modelStabilizer_eq_parabolic
    (m : ActionEquiv D.centralQuotientAction (linearNatural F 3))
    (U : Submodule F.Carrier (Fin 3 → F.Carrier)) :
    (Coordinates.sl3 m).modelStabilizer U = Matrix.HigherLinear.parabolicSL U := by
  ext g
  rfl

private def intrinsicResidualCoreEquiv {H : Type*} [Group H] (P : Subgroup H) :
    (solvableResidual P ⧸ pCore 2 (solvableResidual P)) ≃*
      ((solvableResidual P).map P.subtype ⧸ pCore 2 ((solvableResidual P).map P.subtype)) :=
  let e := (solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private def residualCoreEquiv {H K : Type*} [Group H] [Group K] [Finite H]
    (e : H ≃* K) :
    (solvableResidual H ⧸ pCore 2 (solvableResidual H)) ≃*
      (solvableResidual K ⧸ pCore 2 (solvableResidual K)) :=
  QuotientGroup.congr _ _ e.solvableResidualEquiv (pCore_map_iso 2 e.solvableResidualEquiv)

/-- Every proper nonzero marked subspace gives the original PSL₂ core quotient. -/
def localCoreEquiv (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (U : Submodule S.field.Carrier (Fin 3 → S.field.Carrier)) (hU : U ≠ ⊥) (hUt : U ≠ ⊤) :
    (localResidual L ((Coordinates.sl3 m).preimage U) ⧸
      pCore 2 (localResidual L ((Coordinates.sl3 m).preimage U))) ≃* PSL(2,S.field.Carrier) := by
  have hcard : 4 ≤ Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    change (2 : ℕ)^2 ≤ 2 ^ S.field.degree
    exact Nat.pow_le_pow_right (by decide) (by have := S.nonbinary; omega)
  let e := (Coordinates.sl3 m).residualCoreQuotientEquiv U
  have hp := Matrix.PSL3.LinearThree.SubspaceTransport.exists_parabolic_equiv U hU hUt
  rw [← modelStabilizer_eq_parabolic m U] at hp
  apply Classical.choice
  rcases hp with hp | hp
  · exact ⟨e.trans ((residualCoreEquiv hp.some).trans
      ((intrinsicResidualCoreEquiv (pointParabolicSL S.field.Carrier)).trans
        (pointParabolicSLResidualCoreEquiv S.field.Carrier hcard)))⟩
  · exact ⟨e.trans ((residualCoreEquiv hp.some).trans
      ((intrinsicResidualCoreEquiv (lineParabolicSL S.field.Carrier)).trans
        (lineParabolicSLResidualCoreEquiv S.field.Carrier hcard)))⟩

/-- The opening of §11.1 on the exact ambient residuals of any marked SL₃ flag. -/
def flagLocalCoreEquiv (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (i : Fin 2) :
    (f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2,S.field.Carrier) :=
  localCoreEquiv S m (f.space i.castSucc) (f.space_ne_bot _) (by
    intro ht
    have hd := f.dimension i.castSucc
    rw [ht] at hd
    change Module.finrank S.field.Carrier (⊤ : Submodule S.field.Carrier (Fin 3 → S.field.Carrier)) = _ at hd
    rw [finrank_top,Module.finrank_fin_fun] at hd
    have hi := i.isLt
    simp only [Fin.val_castSucc] at hd
    omega)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
