module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.ModelAlternatives
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Divisibility by three for the classical field-derived endpoints

The opposite binary transvections provide a cubic element in each actual
derived subgroup. Transport through the given model equivalence proves the
three classical `FieldDerivedThreeInput` contracts. For the symplectic model,
the checked characteristic-two central-quotient equivalence identifies the
source's Sp₄ with the stipulated PSp₄ carrier. The field of order two is
included throughout; no perfectness or residual identification is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.7(3a) and the covered case of 16.2.6(1), printed pp.1172–1174.
-/

public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
open Subgroup
open Theory.SpecificGroups.Classical.EvenDerivedThree
open Theory.SpecificGroups.SymplecticFour

private theorem commutator_card_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (commutator G) = Nat.card (commutator H) := by
  have he : (commutator G).map e.toMonoidHom = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  exact Nat.card_congr ((e.subgroupMap _).trans (MulEquiv.subgroupCongr he)).toEquiv

/-- The actual derived subgroup of PSL₂(2ⁿ) has order divisible by three,
including n = 1. -/
theorem fieldDerivedThree_linearTwo : FieldDerivedThreeInput .linearTwo := by
  intro M hM hfin n _ hmodel
  rcases hmodel with ⟨F, hF, hFfin, hcard, ⟨e⟩⟩
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  rw [commutator_card_eq e]
  exact three_dvd_card_psl_commutator (F := F) (show (0 : Fin 2) ≠ 1 by decide)

/-- The actual derived subgroup of PSL₃(2ⁿ) has order divisible by three,
including n = 1. -/
theorem fieldDerivedThree_linearThree : FieldDerivedThreeInput .linearThree := by
  intro M hM hfin n _ hmodel
  rcases hmodel with ⟨F, hF, hFfin, hcard, ⟨e⟩⟩
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  rw [commutator_card_eq e]
  exact three_dvd_card_psl_commutator (F := F) (show (0 : Fin 3) ≠ 1 by decide)

/-- The actual derived subgroup of PSp₄(2ⁿ) has order divisible by three,
including n = 1. -/
theorem fieldDerivedThree_symplecticFour : FieldDerivedThreeInput .symplecticFour := by
  intro M hM hfin n _ hmodel
  rcases hmodel with ⟨F, hF, hFfin, hcard, ⟨e⟩⟩
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  rw [commutator_card_eq (e.trans EvenProjective.equiv.symm)]
  exact three_dvd_card_sp4_commutator

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence

end
