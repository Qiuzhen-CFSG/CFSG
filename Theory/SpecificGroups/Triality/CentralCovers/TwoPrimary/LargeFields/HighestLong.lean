module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Normalization

/-!
# Abelian preimage of the highest long triality root

The highest long root is the tail commutator of the other two long roots.
It commutes with both of them in the base group, by the actual D₄ non-sum
relations. In a central extension, conjugation by a lift of this highest root
therefore changes the two factors only by central elements and fixes their
commutator. Every two lifts of highest-long-root elements commute.

This argument includes q = 2 and q = 4 and uses no scalar-field size bound.
It supplies the highest-root part of the individual root-preimage obligation
in the normalized lifting construction. The final theorem applies it to the
literal canonical projection.

Sources: GLS3 §2.4, in particular the long-root A₂ exchange in 2.4.5;
GLS3 §6.1 and Aschbacher–Smith I.1.3, PDF p.418.
-/

public section
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics ConcreteBruhat RadicalCoordinates.LeviCommutators
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn
variable {E : Type*} [Group E] (f : E →* BinaryCarrier n hn)

private theorem commute_commutator_lift {G : Type*} [Group G] (f : E →* G)
    (hk : f.ker ≤ Subgroup.center E) (x y z : E)
    (hx : Commute (f z) (f x)) (hy : Commute (f z) (f y)) : Commute ⁅x,y⁆ z := by
  have he : z * ⁅x,y⁆ * z⁻¹ = ⁅x,y⁆ := by
    rw [conjugate_commutatorElement]
    apply CentralExtension.commutator_eq_of_image_eq f hk
    · rw [map_mul, map_mul, map_inv, hx.eq, mul_inv_cancel_right]
    · rw [map_mul, map_mul, map_inv, hy.eq, mul_inv_cancel_right]
  exact ((mul_inv_eq_iff_eq_mul.mp he : z * ⁅x,y⁆ = ⁅x,y⁆ * z) : Commute z ⁅x,y⁆).symm

private theorem long_commute_two (Q : Parameters) (hp : Q.prime = 2)
    (i : Fin 3) (hi : i ≠ 2) (s t : fixedField Q) :
    Commute (long Q hp i s) (long Q hp 2 t) := by
  have h : Commute (longElementary Q hp i s) (longElementary Q hp 2 t) := by
    change longElementary Q hp i s * longElementary Q hp 2 t =
      longElementary Q hp 2 t * longElementary Q hp i s
    apply elementaryInclusion_injective Q
    simp only [map_mul, longElementary_val Q hp i s, longElementary_val Q hp 2 t]
    apply PositiveCoordinates.nonsumCommute_parameters Q (longPosition i) (longPosition 2)
      (by
        have hh : ∀ j : Fin 3, j ≠ 2 → longPosition j ≠ longPosition 2 := by decide +kernel
        exact hh i hi)
    rintro ⟨k, hk⟩
    have hsum : ∀ j : Fin 3, ∀ k : Fin 12,
        (longPosition j, longPosition 2, k) ∉ PositiveCoordinates.SumExchangeData.sumTriples := by
      decide +kernel
    exact hsum i k ((PositiveCoordinates.SumExchangeData.mem_sumTriples_iff _ _ _).mpr
      ((PositiveCoordinates.SumExchangeData.root_sum_iff _ _ _).mp hk))
  exact h.map (toCarrier Q)

/-- The full highest-long-root preimage is abelian in every central extension. -/
theorem long_two_preimage_commute
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    {v w : E} (hv : f v ∈ (baseLongHom n hn 2).range)
    (hw : f w ∈ (baseLongHom n hn 2).range) : Commute v w := by
  obtain ⟨s, hs⟩ := hv
  obtain ⟨t, ht⟩ := hw
  obtain ⟨x, hx⟩ := hf (long P rfl 0 s.toAdd)
  obtain ⟨y, hy⟩ := hf (long P rfl 1 1)
  have he : f ⁅x⁻¹,y⁻¹⁆ = f v := by
    rw [map_commutatorElement, map_inv, map_inv, hx, hy, ← hs]
    change ⁅(long P rfl 0 s.toAdd)⁻¹, (long P rfl 1 1)⁻¹⁆ = long P rfl 2 s.toAdd
    calc
      _ = (long P rfl 1 1 * long P rfl 0 s.toAdd)⁻¹ *
          (long P rfl 0 s.toAdd * long P rfl 1 1) := by
        simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
      _ = _ := by rw [long_zero_one_exchange P rfl s.toAdd 1, mul_one, inv_mul_cancel_left]
  have hcx : Commute (f w) (f x⁻¹) := by
    rw [map_inv, hx, ← ht]
    exact (long_commute_two P rfl 0 (by decide) s.toAdd t.toAdd).symm.inv_right
  have hcy : Commute (f w) (f y⁻¹) := by
    rw [map_inv, hy, ← ht]
    exact (long_commute_two P rfl 1 (by decide) 1 t.toAdd).symm.inv_right
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk he.symm rfl]
  exact (commute_commutator_lift f hk x⁻¹ y⁻¹ w hcx hcy).commutator_eq


/-- The unconditional highest-long-root input on the actual canonical cover. -/
theorem universal_long_two_preimage_commute
    {v w : PerfectCentralCovering.UniversalGroup (BinaryCarrier n hn)}
    (hv : PerfectCentralCovering.universalProjection (BinaryCarrier n hn) v ∈
      (baseLongHom n hn 2).range)
    (hw : PerfectCentralCovering.universalProjection (BinaryCarrier n hn) w ∈
      (baseLongHom n hn 2).range) : Commute v w :=
  long_two_preimage_commute n hn _
    (PerfectCentralCovering.universalProjection_surjective _)
    (PerfectCentralCovering.universalProjection_ker_le_center _) hv hw

end Triality.Standard.CentralCovers.TwoPrimary
