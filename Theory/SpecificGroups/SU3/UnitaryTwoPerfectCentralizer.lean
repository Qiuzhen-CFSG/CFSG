module
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import ABG.ChapterII.Section2.UnitaryScalarCard

/-!
# Scalar centralizers in the actual binary unitary group

Embedding GU₂ in GL₂ forces every centralizer of a noncommutative
subgroup to consist of scalars. The stored unitary form makes those
scalars exactly the norm-one roots. Their existing finite-field count
gives the precise centralizer order q+1.

This is the projective rank-one reduction in Aschbacher–Smith A.3.12(9),
pp.47–48, used for the natural larger-span case C.5.12, p.163.
-/

public section
open Subgroup Matrix
namespace ABG

/-- Every noncommutative subgroup of GU₂ has precisely the norm-one scalars
as its full centralizer in GU₂. -/
theorem GU2_centralizer_eq_scalar
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (B : Subgroup (GU2 p n hn)) (hB : ¬ IsMulCommutative B) :
    centralizer (B : Set (GU2 p n hn)) = (GU2Scalar p n hn).range := by
  let ρ := (unitaryForm 2 p n hn).unitarySubgroup.subtype
  let D := B.map ρ
  have he : B ≃* D := B.equivMapOfInjective ρ Subtype.val_injective
  have hd : ¬ IsMulCommutative D := by
    intro hd
    apply hB
    exact IsMulCommutative.of_comm fun x y => he.injective (by
      rw [map_mul,map_mul,hd.is_comm.comm])
  apply le_antisymm
  · intro x hx
    have hxd : ρ x ∈ centralizer (D : Set _) := by
      rintro d ⟨b,hb,rfl⟩
      exact (map_mul ρ b x).symm.trans ((congrArg ρ (hx b hb)).trans (map_mul ρ x b))
    obtain ⟨a,ha⟩ := GeneralLinearGroup.centralizer_le_scalar_of_noncommutative D hd hxd
    have ham : a ^ (p ^ n + 1) = 1 := (scalar_mem_GU2_iff p n hn a).mp (by
      rw [ha]
      exact x.property)
    refine ⟨⟨a,ham⟩,Subtype.ext ?_⟩
    rw [GU2Scalar_apply_val]
    exact ha
  · exact (GU2Scalar_range_le_center p n hn).trans (center_le_centralizer (B : Set (GU2 p n hn)))

/-- The exact centralizer order follows from the scalar roots-of-unity
count; no complete centralizer recognition or unitary order is assumed. -/
theorem GU2_noncommutative_centralizer_card
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (B : Subgroup (GU2 p n hn)) (hB : ¬ IsMulCommutative B) :
    Nat.card (centralizer (B : Set (GU2 p n hn))) = p ^ n + 1 := by
  rw [GU2_centralizer_eq_scalar p n hn B hB]
  exact (GU2Scalar_structure p n hn).2

end ABG
