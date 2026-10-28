module
public import Glauberman.SymplecticSmallMoverThompson

/-!
# Sharp symplectic abelian offenders under the root-product bound

The all-abelian offender classification has no strict offenders once the
maximum-small-mover join has order at most q squared. Roots have order and
moving index q; plane offenders have order and moving index q squared.
The full point radical is excluded by the same join bound. Transport to a
quotient preserves the full fixed kernel and gives equality for every
maximum abelian subgroup, the input to the all-abelian Baumann replacement.
Source: MS93 (5.1), printed p.913.
-/
public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- Every small offender of order at most q squared is sharp. -/
theorem small_index_eq_card_of_card_le_square
    (A : Subgroup (unipotent (F := F))) (hA : Small A)
    (hcard : Nat.card A ≤ Nat.card F ^ 2) : movingIndex A = Nat.card A := by
  rcases small_classification A hA with hz | ⟨s,rfl⟩ | ⟨hw,hc⟩ | ⟨l,rfl⟩
  · rw [hz,card_bot]
    have hm : 0 < movingIndex (⊥ : Subgroup (unipotent (F := F))) :=
      pow_pos Nat.card_pos _
    have hle := hz ▸ hA.1
    rw [card_bot] at hle
    omega
  · rw [movingIndex_rootFamily,card_rootFamily]
  · have he := le_antisymm hcard hc
    have hq : Nat.card F < Nat.card F ^ 2 := by
      simpa only [pow_one] using
        (pow_lt_pow_right₀ (Finite.one_lt_card : 1 < Nat.card F) (by decide : 1 < 2))
    rw [movingIndex_eq_field_sq_of_large_wing A hw (he ▸ hq),he]
  · rw [movingIndex_finitePlane,card_finitePlane]

/-- The full point radical is impossible under the join bound, so every
abelian offender has exactly as many elements as its moving index. -/
theorem abelian_offender_sharp_of_join_card_le_square
    (hq : 2 < Nat.card F) (T A : Subgroup (unipotent (F := F)))
    [IsMulCommutative A] (hbound : Nat.card (join T) ≤ Nat.card F ^ 2)
    (hAT : A ≤ T) (hoff : movingIndex A ≤ Nat.card A) :
    movingIndex A = Nat.card A := by
  rcases abelian_offender_small_or_point hq A hoff with hs | he
  · exact small_index_eq_card_of_card_le_square A hs
      ((card_le_of_le (small_le_join_of_card_le_square hbound hAT hs)).trans hbound)
  · exact False.elim (not_point_le_of_join_card_le_square T hbound (he ▸ hAT))
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree

namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree.Quotient
variable {F G D : Type*} [Field F] [CharP F 2] [Finite F]
  [Group G] [Finite G] [Group D]

/-- The exact full-layer index of each maximum abelian subgroup equals its
order modulo the original kernel, at every nonbinary field degree. -/
theorem maximum_abelian_sharp_of_smallMover_bound
    (U T : Subgroup G) [IsMulCommutative U] (q : G →* D)
    (i : unipotent (F := F) →* D) (hi : Function.Injective i)
    (hkT : q.ker ≤ T) (hUk : U ≤ q.ker) (hUT : U ≤ centralizer (q.ker : Set G))
    (hTi : T.map q ≤ i.range)
    (hindex : ∀ E : Subgroup G, E ≤ T →
      (centralizer (E : Set G)).relIndex U = movingIndex (coordinates q i E))
    (hq : 2 < Nat.card F)
    (hbound : q.ker.relIndex (Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)) ≤ Nat.card F ^ 2)
    (A : Subgroup G) (hA : A ∈ thompsonAbelianSubgroups T) :
    (centralizer (A : Set G)).relIndex U = q.ker.relIndex A := by
  let J := Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)
  have hJT : J ≤ T := Subgroup.SmallMover.join_le _ _ _ _
  have hc (B : Subgroup G) (hBi : B.map q ≤ i.range) :
      Nat.card (coordinates q i B) = q.ker.relIndex B := by
    rw [relIndex_ker,←coordinates_map q i B hBi,card_map_of_injective hi]
  have hjoin := coordinates_join U T q i hi hkT hUT hTi hindex
  have hsmall : Nat.card (Degree.join (coordinates q i T)) ≤ Nat.card F ^ 2 := by
    rw [←hjoin,hc J ((map_mono hJT).trans hTi)]
    exact hbound
  have hAi := (map_mono hA.1).trans hTi
  let : IsMulCommutative A := hA.2.1
  let : IsMulCommutative (A.map q) := map_isMulCommutative A q
  let : IsMulCommutative (coordinates q i A) := by
    apply IsMulCommutative.of_setLike_mul_comm
    intro x hx y hy
    apply hi
    simpa only [map_mul] using setLike_mul_comm (show i x ∈ A.map q from hx)
      (show i y ∈ A.map q from hy)
  have hoff := Glauberman.maximum_abelian_offender_bound hA (hUk.trans hkT) hUk
    inferInstance hUT
  rw [inf_relIndex_left] at hoff
  have he := Degree.abelian_offender_sharp_of_join_card_le_square hq
    (coordinates q i T) (coordinates q i A) hsmall (comap_mono (map_mono hA.1))
    (by rw [←hindex A hA.1,hc A hAi]; exact hoff)
  rwa [←hindex A hA.1,hc A hAi] at he
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree.Quotient
