module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup

public import Submission.FeitThompson.HallSubgroups.Core

/-!
# Hall subgroup consequence for finite Z-groups
-/

/-- In a finite Z-group, the commutator subgroup is a Hall subgroup. -/
public theorem exists_isHallSubgroup_commutator_of_isZGroup
    {G : Type*} [Group G] [Finite G] :
    IsZGroup G → ∃ π : Set Nat.Primes, IsHallSubgroup π (commutator G) := by
  intro hZ
  letI : IsZGroup G := hZ
  let π : Set Nat.Primes := {p | p.val ∣ Nat.card (commutator G)}
  refine ⟨π, ?_⟩
  have hcop : Nat.Coprime (Nat.card (commutator G)) (commutator G).index := by
    simpa using (IsZGroup.coprime_commutator_index (G := G))
  refine isHallSubgroup_of (G := G) (π := π) (H := commutator G) (hcard := ?_) (hindex := ?_)
  · intro p hp_dvd
    exact hp_dvd
  · intro p hp_mem hp_dvd_idx
    exact (Nat.not_coprime_of_dvd_of_dvd p.property.one_lt hp_mem hp_dvd_idx) hcop
