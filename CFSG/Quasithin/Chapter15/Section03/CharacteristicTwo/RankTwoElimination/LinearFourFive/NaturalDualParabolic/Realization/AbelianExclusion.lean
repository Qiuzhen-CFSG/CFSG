module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure

/-!
# The abelian MS branch in the original natural-dual residual

The genuine binary MS theorem bounds an abelian commutator core by 64.
The literal point residual constructed from the natural-dual component has
commutator core of order at least 128. Thus its core is nonabelian before
any of the MS93 critical-distance arguments or classification alternatives.

Source: Aschbacher--Smith, C.1.34(1),(2),(5) and 15.3.24;
Meierfrankenfeld--Stellmacher (1993), the binary abelian case.
-/

public section
open Subgroup BinaryLinear.OuterCyclic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {d : LocalData G} {L I : Subgroup G}

/-- The actual residual core is nonabelian, from the original theta and
Sylow hypotheses. No C.1.34 classification witness is required. -/
theorem binaryInput_core_nonabelian_of_theta
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    ¬ IsMulCommutative (ChapterC.BinaryMS.commutatorCore (residualComponent h x)) := by
  intro hc
  have hl := (binaryInput_core_bounds_of_theta h hx hS hθ input).1
  obtain ⟨n, hn, ⟨e⟩⟩ := input.abelianCore_model hc
  have he : Nat.card (ChapterC.BinaryMS.commutatorCore (residualComponent h x)) = 2 ^ n := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin n → ZMod 2) = _
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rcases hn with rfl | rfl | rfl <;> norm_num at he <;> omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
