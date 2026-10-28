module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.RegularSphere

/-!
# Adjacency formulas for the actual local comparison

The distinguished neighboring axis is exactly K∩V. Two neighbors of W
are adjacent precisely when their unique lines through W coincide. For
the opposite cubic Y in the actual SL₂(3) factor, Yᵈ is adjacent to that
axis precisely when d lies in V∩D. The latter follows by transporting
back by d and using uniqueness of the common neighbor on V.

These formulas involve only the original normalizer, D, K and V, as
required by the local isomorphism in Asc9445.11, printed p.248.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem complement_inf_kernel_eq_otherAxis : c.K ⊓ c.V = c.otherAxis := by
  have hle : c.otherAxis ≤ c.K ⊓ c.V :=
    le_inf (le_sup_right.trans (show c.J ≤ c.K from le_sup_left)) c.otherAxis_le_kernel
  have h1 : Nat.card (c.K ⊓ c.V : Subgroup G) ∣ 48 := c.complement_card ▸ card_dvd_of_le inf_le_left
  have h2 : Nat.card (c.K ⊓ c.V : Subgroup G) ∣ 81 := c.kernel_card ▸ card_dvd_of_le inf_le_right
  have hd : Nat.card (c.K ⊓ c.V : Subgroup G) ∣ 3 := Nat.dvd_gcd h1 h2
  exact (eq_of_le_of_card_ge hle (by rw [c.otherAxis_card]; exact Nat.le_of_dvd (by decide) hd)).symm

theorem opposite_neighbor_iff_normalizes_axis {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (d : G) (hd : d ∈ c.D) :
    Y.conjBy d ∈ c.neighbors c.otherAxis ↔ d ∈ normalizer (c.otherAxis : Set G) := by
  have hdn : d ∈ normalizer (c.W : Set G) := c.complement_product.ge (mem_sup_left hd)
  have hwi : c.W.conjBy d⁻¹ = c.W := mem_normalizer_iff_map_conj_eq.mp (inv_mem hdn)
  constructor
  · intro ha
    have hAY := c.neighbor_conjugate ha d⁻¹
    rw [conjBy_inv] at hAY
    have hWZ := c.neighbor_conjugate c.otherAxis_neighbor d⁻¹
    rw [hwi] at hWZ
    let Yp : c.points := ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩
    let Z : c.points := c.conjugatePoint ⟨c.otherAxis, c.otherAxis_is_point⟩ d⁻¹
    have hYZ : c.collinearity.Adj Yp Z := c.collinearity.adj_symm
      (show c.collinearity.Adj Z Yp from hAY)
    have hYA : c.collinearity.Adj Yp ⟨c.otherAxis, c.otherAxis_is_point⟩ :=
      c.collinearity.adj_symm (show c.collinearity.Adj ⟨c.otherAxis, c.otherAxis_is_point⟩ Yp from
        c.opposite_cubic_common_neighbor hYL hY hne)
    have hZV : Z.val ≤ c.V := (map_mono c.otherAxis_le_kernel).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (c.odd_normalizes_kernel (c.D.inv_mem hd)))
    have he := c.common_neighbors_on_line_unique ⟨c.W, c.point_mem⟩ Yp
      ⟨c.otherAxis, c.otherAxis_is_point⟩ Z
      (c.opposite_cubic_not_collinear hYL hY hne)
      (fun he => hne (congrArg Subtype.val he).symm)
      ⟨c.otherAxis_neighbor, hYA⟩ ⟨hWZ, hYZ⟩
      ⟨c.line_mem, c.line_le_kernel⟩ c.otherAxis_le_kernel hZV
    have hi : d⁻¹ ∈ normalizer (c.otherAxis : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr (congrArg Subtype.val he).symm
    simpa only [inv_inv] using (normalizer (c.otherAxis : Set G)).inv_mem hi
  · intro hn
    have hh := c.neighbor_conjugate (c.opposite_cubic_common_neighbor hYL hY hne) d
    have he : c.otherAxis.conjBy d = c.otherAxis := mem_normalizer_iff_map_conj_eq.mp hn
    rwa [he] at hh

/-- The source45.11 adjacency between the distinguished neighbor and an opposite orbit point. -/
theorem opposite_neighbor_iff_mem_kernel_intersection {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (d : G) (hd : d ∈ c.D) :
    Y.conjBy d ∈ c.neighbors c.otherAxis ↔ d ∈ c.V ⊓ c.D := by
  rw [c.opposite_neighbor_iff_normalizes_axis hYL hY hne d hd]
  have hs := c.other_kernelLine_odd_stabilizer
    (c.pointsOn_base ▸ (show c.otherAxis ∈ c.pointsOn c.V from
      ⟨c.otherAxis_is_point, c.otherAxis_le_kernel⟩)) c.otherAxis_ne_point
  exact ⟨fun hn => hs ▸ (show d ∈ c.D ⊓ normalizer (c.otherAxis : Set G) from ⟨hd, hn⟩),
    fun hm => (show d ∈ c.D ⊓ normalizer (c.otherAxis : Set G) from hs.symm ▸ hm).2⟩

/-- The source45.11 adjacency between two distinct neighbors of W. -/
theorem neighboring_axes_adj_iff_normalizes_kernel (k : G)
    (hk : k ∈ normalizer (c.W : Set G)) (hne : c.otherAxis.conjBy k ≠ c.otherAxis) :
    c.otherAxis.conjBy k ∈ c.neighbors c.otherAxis ↔ k ∈ normalizer (c.V : Set G) := by
  have hw : c.W.conjBy k = c.W := mem_normalizer_iff_map_conj_eq.mp hk
  have hn := c.neighbor_conjugate c.otherAxis_neighbor k
  rw [hw] at hn
  constructor
  · intro ha
    obtain ⟨L, hL, hWL, hIL, hIkL⟩ := c.triangle_on_line ⟨c.W, c.point_mem⟩
      ⟨c.otherAxis, c.otherAxis_is_point⟩
      ⟨c.otherAxis.conjBy k, c.point_conjugate_mem c.otherAxis_is_point k⟩ c.otherAxis_neighbor hn ha
    have hLV : L = c.V := c.line_unique c.point_mem c.otherAxis_is_point c.line_mem hL
      c.otherAxis_ne_point c.line_le_kernel hWL c.otherAxis_le_kernel hIL
    have hWVk : c.W ≤ c.V.conjBy k := hw ▸ map_mono c.line_le_kernel
    have he : c.V.conjBy k = c.V := c.line_unique c.point_mem
      (c.point_conjugate_mem c.otherAxis_is_point k) c.line_mem (c.line_conjugate_mem c.line_mem k)
      hn.2.1 c.line_le_kernel hWVk (hLV ▸ hIkL) (map_mono c.otherAxis_le_kernel)
    exact mem_normalizer_iff_map_conj_eq.mpr he
  · intro hV
    exact ⟨c.point_conjugate_mem c.otherAxis_is_point k, hne, c.V, c.line_mem,
      c.otherAxis_le_kernel, (map_mono c.otherAxis_le_kernel).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp hV)⟩

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
