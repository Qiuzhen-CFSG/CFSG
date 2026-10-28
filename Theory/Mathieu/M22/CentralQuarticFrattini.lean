module

public import Theory.Mathieu.M22.CentralDoubleExtension
public import Theory.Frattini.BinarySquares
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual central square subgroup in quartic covers of M₂₂

Factor out the squares of the cyclic center of order four. The resulting
surjection onto M₂₂ has central kernel of order two. Its elementary
pullbacks are elementary, so squares in the original pullback lie in the
central square subgroup. Conversely that subgroup consists of squares of
central elements of the pullback. The square description of the Frattini
subgroup proves equality.

This proves the Frattini calculation used with I.2.2(6a), printed pp.410
and 412, without assuming recognition of the quartic local central product.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22CentralCover
open Subgroup
open scoped IsMulCommutative
variable (K : Type*) [Group K]

/-- Squares of the actual center, embedded in the ambient group. -/
noncomputable def centerSquares : Subgroup K :=
  (powMonoidHom 2 : center K →* center K).range.map (center K).subtype

theorem centerSquares_le : centerSquares K ≤ center K := map_subtype_le _

instance centerSquares_normal : (centerSquares K).Normal where
  conj_mem x hx g := by
    rw [mem_center_iff.mp (centerSquares_le K hx) g, mul_inv_cancel_right]
    exact hx

theorem mem_centerSquares_iff (x : K) :
    x ∈ centerSquares K ↔ ∃ z : center K, (z : K) ^ 2 = x := by
  constructor
  · rintro ⟨w, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z ^ 2, ⟨z, rfl⟩, rfl⟩

variable {K} [Finite K]

theorem centerSquares_card [IsCyclic (center K)] (hZ : Nat.card (center K) = 4) :
    Nat.card (centerSquares K) = 2 := by
  rw [centerSquares, card_map_of_injective (center K).subtype_injective,
    IsCyclic.card_powMonoidHom_range, hZ]
  decide

private theorem factored_kernel_card [IsCyclic (center K)] (hZ : Nat.card (center K) = 4) :
    Nat.card ((center K).map (QuotientGroup.mk' (centerSquares K))) = 2 := by
  have hc : Nat.card ((centerSquares K).subgroupOf (center K)) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (centerSquares_le K)).toEquiv).trans
      (centerSquares_card hZ)
  have h := ((centerSquares K).subgroupOf (center K)).card_mul_index
  rw [hc, hZ] at h
  have hi : (centerSquares K).relIndex (center K) = 2 := by
    change ((centerSquares K).subgroupOf (center K)).index = 2
    omega
  have hm := relIndex_ker (center K) (QuotientGroup.mk' (centerSquares K))
  rw [QuotientGroup.ker_mk', hi] at hm
  exact hm.symm

/-- Every lift of a quotient involution has square in the embedded square
subgroup of the actual cyclic center. -/
theorem square_mem_centerSquares [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    (x : K) (hx : (projection e x) ^ 2 = 1) : x ^ 2 ∈ centerSquares K := by
  let S := centerSquares K
  let q := QuotientGroup.mk' S
  have hS : S ≤ (projection e).ker := by rw [projection_ker]; exact centerSquares_le K
  let f : (K ⧸ S) →* M22 := QuotientGroup.lift S (projection e) hS
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective S _ (projection_surjective e) hS
  have hk : f.ker = (center K).map q := by
    rw [QuotientGroup.ker_lift, projection_ker]
  have hc : f.ker ≤ center (K ⧸ S) := by
    rw [hk]
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective S a
    simpa only [map_mul] using congrArg q (mem_center_iff.mp hz b)
  have hp := square_eq_one_of_central_double_extension f hf
    (hk ▸ factored_kernel_card hZ) hc (q x) hx
  apply (QuotientGroup.eq_one_iff (N := S) (x ^ 2)).mp
  change q (x ^ 2) = 1
  rw [map_pow]
  exact hp

/-- The Frattini subgroup of every elementary pullback in a quartic cover
is precisely the order-two square subgroup of the original center. -/
theorem elementary_preimage_frattini [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    (E : Subgroup M22) [IsElementaryAbelian 2 E] :
    (frattini (preimage e E)).map (preimage e E).subtype = centerSquares K := by
  let P := preimage e E
  have hP : IsPGroup 2 P := by
    apply (IsElementaryAbelian.isPGroup 2 E).comap_of_ker_isPGroup (projection e)
    rw [projection_ker]
    exact IsPGroup.of_card (n := 2) (by simpa using hZ)
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    rw [hP.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact square_mem_centerSquares e hZ x
      (elemPow_eq_one_of_isElementaryAbelian _ x.property)
  · intro x hx
    obtain ⟨z, rfl⟩ := (mem_centerSquares_iff K x).mp hx
    let zP : P := ⟨z, center_le_preimage e E z.property⟩
    let : Fact (IsPGroup 2 P) := ⟨hP⟩
    exact ⟨zP ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) zP, rfl⟩

end Sporadic.Mathieu.M22CentralCover
