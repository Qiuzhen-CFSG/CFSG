module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.Swap.Standard
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# The two marked Suzuki factors in the Ree model

The first factor is the fixed middle-node B₂ Levi, identified with the
literal Suzuki matrix group by its faithful four-dimensional representation.
The second is its conjugate by the concrete exceptional Weyl interchange.
If these factors commute, triviality of the Suzuki center makes their
multiplication injective. Their ranges are the specified root subgroups,
so the already proved interchange acts on these actual factors.

Source: GLS3, Example 2.6.3, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.SuzukiFactors
open Subgroup BenderSuzuki.MatrixGroups
open MaximalSubgroups.CommutingComponents.CarrierIdentification
open MaximalSubgroups.CommutingComponents.PairSwap
open LargeLocalSeeds.SuzukiLeviProjection

/-- Identification of the root-defined standard factor with Suzuki matrices. -/
def firstEquiv (m : ℕ) : standardSuzukiLevi m ≃* SuzukiMatrixGroup m :=
  (localLeviEquiv (canonicalLocalBlockInput m)).symm.trans
    (fixedLeviEquivSuzuki (canonicalLocalBlockInput m))

/-- The first Suzuki factor, with its actual ambient inclusion. -/
def first (m : ℕ) : SuzukiMatrixGroup m →* Model m :=
  (standardSuzukiLevi m).subtype.comp (firstEquiv m).symm.toMonoidHom

/-- The second Suzuki factor, marked using the fixed Weyl interchange. -/
def second (m : ℕ) : SuzukiMatrixGroup m →* Model m :=
  (MulAut.conj (interchangeElement m)).toMonoidHom.comp (first m)

theorem first_injective (m : ℕ) : Function.Injective (first m) :=
  Subtype.val_injective.comp (firstEquiv m).symm.injective

theorem second_injective (m : ℕ) : Function.Injective (second m) :=
  (MulAut.conj (interchangeElement m)).injective.comp (first_injective m)

theorem first_range (m : ℕ) : (first m).range = standardSuzukiLevi m := by
  rw [first, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (firstEquiv m).symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

theorem second_range (m : ℕ) : (second m).range = standardPartner m := by
  rw [second, MonoidHom.range_comp, first_range]
  rfl

/-- The Weyl element interchanges the two actual ranges in both directions. -/
theorem interchange_ranges (m : ℕ) :
    (first m).range.map (MulAut.conj (interchangeElement m)).toMonoidHom = (second m).range ∧
    (second m).range.map (MulAut.conj (interchangeElement m)).toMonoidHom = (first m).range := by
  rw [first_range, second_range]
  exact interchange_standard_pair m

/-- The remaining root calculation is elementwise commutation of the marked factors. -/
def CommuteFactors (m : ℕ) : Prop :=
  ∀ x y : SuzukiMatrixGroup m, Commute (first m x) (second m y)

private theorem center_eq_bot {m : ℕ} (hm : 1 ≤ m) :
    center (SuzukiMatrixGroup m) = ⊥ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
    apply Group.isSolvable_of_comm
    intro x y
    have hx : x ∈ center (SuzukiMatrixGroup m) := by rw [h]; trivial
    exact (mem_center_iff.mp hx y).symm

/-- Commutation separates the factors, since the first is centerless. -/
theorem ranges_disjoint {m : ℕ} (hm : 1 ≤ m) (hc : CommuteFactors m) :
    Disjoint (first m).range (second m).range := by
  apply Subgroup.disjoint_def.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have hx : x ∈ center (SuzukiMatrixGroup m) := by
    rw [mem_center_iff]
    intro a
    apply first_injective m
    simp only [map_mul]
    rw [← hy]
    exact (hc a y).eq
  have hx1 : x = 1 := by simpa only [center_eq_bot hm, mem_bot] using hx
  rw [hx1, map_one]

/-- Multiplication of the two marked commuting Suzuki factors. -/
def product (m : ℕ) (hc : CommuteFactors m) :
    SuzukiMatrixGroup m × SuzukiMatrixGroup m →* Model m :=
  (first m).noncommCoprod (second m) hc

theorem product_injective {m : ℕ} (hm : 1 ≤ m) (hc : CommuteFactors m) :
    Function.Injective (product m hc) :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨first_injective m, second_injective m, ranges_disjoint hm hc⟩

@[simp] theorem product_first (m : ℕ) (hc : CommuteFactors m) (x : SuzukiMatrixGroup m) :
    product m hc (x, 1) = first m x := by
  change first m x * second m 1 = first m x
  rw [map_one, mul_one]

@[simp] theorem product_second (m : ℕ) (hc : CommuteFactors m) (x : SuzukiMatrixGroup m) :
    product m hc (1, x) = second m x := by
  change first m 1 * second m x = second m x
  rw [map_one, one_mul]

end ReeF4.CentralCovers.OddPrimary.SuzukiFactors
