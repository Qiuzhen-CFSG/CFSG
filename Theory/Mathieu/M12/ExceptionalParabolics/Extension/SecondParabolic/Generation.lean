module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Geometry
public import Theory.Mathieu.M12.ValueBoundParabolics

/-!
# Generation of the fixed outer carrier by its two parabolics

The inner generating pair maps into the fixed parabolics. The explicit swap
moves a point out of the marked degree-12 block, while both inner generators
preserve it. Thus the parabolic join properly contains the index-two inner
subgroup and equals the whole carrier.
Source: the Aut(M₁₂) amalgam in Aschbacher--Smith, F.1.12(I)(13), p.263.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def blockColor (i : Fin 24) : Bool := decide (i ∈ Finset.univ.image blockLabel)

private def blockPreserver : Subgroup Carrier where
  carrier := {g | ∀ i, blockColor ((g : Equiv.Perm (Fin 24)) i) = blockColor i}
  one_mem' _ := rfl
  mul_mem' := by
    intro g h hg hh i
    exact (hg ((h : Equiv.Perm (Fin 24)) i)).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (((g : Equiv.Perm (Fin 24))⁻¹) i)).symm

theorem swap_not_inner : swap ∉ inner := by
  have h : inner ≤ blockPreserver := by
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · change ∀ i, blockColor (innerAPerm i) = blockColor i
      decide +kernel
    · change ∀ i, blockColor (innerBPerm i) = blockColor i
      decide +kernel
  intro hs
  have hf := h hs 4
  have hn : blockColor (swapPerm 4) ≠ blockColor 4 := by decide +kernel
  exact hn hf

theorem parabolic_sup_eq_top (m : InnerModel) : firstParabolic ⊔ secondParabolic = ⊤ := by
  let K := firstParabolic ⊔ secondParabolic
  have hin : inner ≤ K := by
    have hH : M12SmallPair.firstParabolic.map m.embedding ≤ firstParabolic := by
      rw [Subgroup.map_le_iff_le_comap, comap_firstParabolic]
    have hA : M12SmallPair.secondParabolic.map m.embedding ≤ secondParabolic := by
      rw [Subgroup.map_le_iff_le_comap, comap_secondParabolic]
    have h := sup_le_sup hH hA
    rw [← Subgroup.map_sup, M12SmallPair.ValueBoundParabolics.parabolic_sup_eq_top,
      ← MonoidHom.range_eq_map, m.embedding_range] at h
    exact h
  have hs : swap ∈ K := by
    have h := movement_mem_overlap QuaternionSwapModel.swap
    rw [movement_swap] at h
    exact Subgroup.mem_sup_left h.1
  have hd := Subgroup.index_dvd_of_le hin
  rw [m.index] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hk | hk
  · exact Subgroup.index_eq_one.mp hk
  · have he : inner = K := Subgroup.eq_of_le_of_card_ge hin (by
      have h := K.index_mul_card
      have hi := inner.index_mul_card
      rw [hk] at h
      rw [m.index] at hi
      omega)
    exact (swap_not_inner (he ▸ hs)).elim

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
