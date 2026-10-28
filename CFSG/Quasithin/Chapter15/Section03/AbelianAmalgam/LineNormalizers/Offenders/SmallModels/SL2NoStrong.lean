module

public import Theory.Representation.SL2NaturalOffenders.NoStrong
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Fields

/-!
# The natural SL₂ case in the marked line-normalizer reduction

The source's literal central-quotient coordinates give a surjective natural
quotient of the same actor. The natural-module bound excludes every strong
offender, and B.1.4(6) makes each ordinary offender best, with equality of
rank and fixed codimension. The quotient and actor markings are retained.
Source: Aschbacher–Smith 15.3.67, printed p.1154, and B.1.4(6), printed p.69.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
open Representation Representation.BinaryOffender BestReduction
open Representation.HigherFieldBorelFixedSpaces
variable {F D W : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The literal central quotient supplies the natural section; no split is assumed. -/
theorem sl2Field_central_quotient_not_strong
    (ρ : Representation (ZMod 2) D W)
    (c : CentralQuotientCoordinates ρ (binaryNatural (F := F) 2)) :
    ¬ IsStrongFFModule ρ := by
  let q := c.coordinates.toLinearMap.comp ρ.invariants.mkQ
  exact Representation.SL2NaturalOffenders.NoStrong.not_strong_of_natural_quotient ρ c.actor.toMonoidHom
    c.actor.injective q (c.coordinates.surjective.comp ρ.invariants.mkQ_surjective)
    c.intertwines

/-- Every ordinary offender in this actual central-quotient case is best. -/
theorem sl2Field_offender_best
    (ρ : Representation (ZMod 2) D W)
    (c : CentralQuotientCoordinates ρ (binaryNatural (F := F) 2))
    {A : Subgroup D} (hA : IsOffender ρ A) :
    IsBestOffender ρ A ∧ fixedCodim ρ A = rank A := by
  have hn := sl2Field_central_quotient_not_strong ρ c
  have he : fixedCodim ρ A = rank A :=
    le_antisymm hA.2 (Nat.le_of_not_gt (fun h => hn ⟨A,hA.1,h⟩))
  exact ⟨(isBestOffender_iff_of_not_strong ρ hn A).mpr ⟨hA.1,he⟩,he⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
