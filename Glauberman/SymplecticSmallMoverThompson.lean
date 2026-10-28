module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeAbelian
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeQuotient
public import Glauberman.QuadraticOffenderSelection

/-!
# The ordinary Thompson subgroup under the symplectic root-product bound

Maximum abelian order makes every member an offender on the entire abelian
layer U. Exact natural indices and the abelian Sylow calculation put its
image in the maximum-small-mover join whenever that join has relative order
at most q². Kernel saturation lifts this containment to the original group.

The application is the first paragraph of MS93 (5.1), printed p.913, on the
actual characteristic replacement. The full quotient kernel is retained;
the edge subgroup is not assumed Sylow. This does not supply the later
rank-one pushing-up conclusion or the distance bound.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree.Quotient
variable {F G D : Type*} [Field F] [CharP F 2] [Finite F]
  [Group G] [Finite G] [Group D]
variable (U T : Subgroup G) (q : G →* D) (i : unipotent (F := F) →* D)
  (hi : Function.Injective i)
  (hkT : q.ker ≤ T) (hUT : U ≤ centralizer (q.ker : Set G))
  (hTi : T.map q ≤ i.range)
  (hindex : ∀ E : Subgroup G, E ≤ T →
    (centralizer (E : Set G)).relIndex U = movingIndex (coordinates q i E))
include hi hkT hUT hTi hindex in
/-- Literal quotient transport of the abelian-offender calculation. -/
theorem abelian_offender_le_smallMover_join
    (hq : 2 < Nat.card F)
    (hbound : q.ker.relIndex (Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)) ≤ Nat.card F ^ 2)
    (A : Subgroup G) [IsMulCommutative A] (hAT : A ≤ T)
    (hoff : (centralizer (A : Set G)).relIndex U ≤ q.ker.relIndex A) :
    A ≤ Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2) := by
  let J := Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)
  have hJT : J ≤ T := Subgroup.SmallMover.join_le _ _ _ _
  have hJi : J.map q ≤ i.range := (map_mono hJT).trans hTi
  have hAi : A.map q ≤ i.range := (map_mono hAT).trans hTi
  have hjoin := coordinates_join U T q i hi hkT hUT hTi hindex
  have hc (B : Subgroup G) (hBi : B.map q ≤ i.range) :
      Nat.card (coordinates q i B) = q.ker.relIndex B := by
    rw [relIndex_ker,←coordinates_map q i B hBi,card_map_of_injective hi]
  have hsmall : Nat.card (Degree.join (coordinates q i T)) ≤ Nat.card F ^ 2 := by
    rw [←hjoin,hc J hJi]
    exact hbound
  let : IsMulCommutative (A.map q) := map_isMulCommutative A q
  let : IsMulCommutative (coordinates q i A) := by
    apply IsMulCommutative.of_setLike_mul_comm
    intro x hx y hy
    apply hi
    simpa only [map_mul] using setLike_mul_comm (show i x ∈ A.map q from hx)
      (show i y ∈ A.map q from hy)
  have hAc := Degree.abelian_offender_le_join_of_card_le_square hq
    (coordinates q i T) (coordinates q i A) hsmall (comap_mono (map_mono hAT))
    (by rw [←hindex A hAT,hc A hAi]; exact hoff)
  rw [←hjoin] at hAc
  have hm := map_mono (f := i) hAc
  rw [coordinates_map q i A hAi,coordinates_map q i J hJi] at hm
  have hkJ : q.ker ≤ J := Subgroup.SmallMover.kernel_le_join U q.ker T _
    (Nat.one_le_pow _ _ Nat.card_pos) hkT hUT
  exact (map_le_map_iff.mp hm).trans (sup_le le_rfl hkJ)

include hi hkT hUT hTi hindex in
/-- The source root-product order bound places every maximum abelian
subgroup, and hence the whole ordinary Thompson subgroup, in the small-mover join. -/
theorem thompson_le_smallMover_join
    (hq : 2 < Nat.card F) (hUk : U ≤ q.ker) [IsMulCommutative U]
    (hbound : q.ker.relIndex (Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)) ≤ Nat.card F ^ 2) :
    thompsonSubgroup T ≤ Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2) := by
  apply sSup_le
  intro A hA
  let := hA.2.1
  have hoff := Glauberman.maximum_abelian_offender_bound hA (hUk.trans hkT) hUk
    inferInstance hUT
  rw [inf_relIndex_left] at hoff
  exact abelian_offender_le_smallMover_join U T q i hi hkT hUT hTi hindex hq hbound A hA.1 hoff
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree.Quotient
