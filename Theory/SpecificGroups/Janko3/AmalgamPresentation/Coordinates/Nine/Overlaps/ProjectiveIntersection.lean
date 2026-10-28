module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.PairTable
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.ThirdTable

/-! The common normalized matrices give the literal projective intersection. -/
public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates.OverlapTables
open Subgroup

private abbrev Common := {i : Fin 20 // ∃ j : Fin 60, Pair.rowMatrix i = Third.rowMatrix j}

private theorem common_card : Nat.card Common = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem row_eq_iff (i : Fin 20) (j : Fin 60) :
    Pair.repr i = Third.repr j ↔ Pair.rowMatrix i = Third.rowMatrix j := by
  constructor
  · intro h
    have hp : ∀ i : Fin 20, pivot (Pair.row i) = 1 := by decide +kernel
    have ht : ∀ j : Fin 60, pivot (Third.row j) = 1 := by decide +kernel
    exact congrArg (fun m : GL9 => (m : Matrix (Fin 2) (Fin 2) F))
      (normalized_injective (hp i) (ht j) h)
  · intro h
    apply congrArg Matrix.ProjGenLinGroup.mk
    exact Matrix.GeneralLinearGroup.ext fun k l => congrFun (congrFun h k) l

private def commonMap : Common → (Pair.subgroup ⊓ Third.subgroup : Subgroup P) := fun i =>
  ⟨Pair.repr i.val,by
    constructor
    · change Pair.repr i.val ∈ (Pair.subgroup : Set P)
      rw [Pair.carrier_eq]
      exact Set.mem_range_self _
    · obtain ⟨j,hj⟩ := i.property
      change Pair.repr i.val ∈ (Third.subgroup : Set P)
      rw [Third.carrier_eq, (row_eq_iff _ _).mpr hj]
      exact Set.mem_range_self _⟩

private theorem commonMap_bijective : Function.Bijective commonMap := by
  constructor
  · intro i j hij
    apply Subtype.ext
    exact Pair.repr_injective (congrArg (fun x : (Pair.subgroup ⊓ Third.subgroup : Subgroup P) => (x : P)) hij)
  · intro x
    have hp : x.val ∈ Set.range Pair.repr := by rw [←Pair.carrier_eq]; exact x.property.1
    have ht : x.val ∈ Set.range Third.repr := by rw [←Third.carrier_eq]; exact x.property.2
    obtain ⟨i,hi⟩ := hp
    obtain ⟨j,hj⟩ := ht
    refine ⟨⟨i,j,(row_eq_iff _ _).mp (hi.trans hj.symm)⟩,?_⟩
    exact Subtype.ext hi

/-- The two literal projective word subgroups meet in exactly ten elements. -/
theorem intersection_card : Nat.card (Pair.subgroup ⊓ Third.subgroup : Subgroup P) = 10 := by
  rw [←Nat.card_congr (Equiv.ofBijective commonMap commonMap_bijective)]
  exact common_card

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates.OverlapTables
