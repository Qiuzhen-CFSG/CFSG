module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.Definitions
public import Theory.SpecificGroups.Janko1.Model.Basic

/-!
# The orders of the source matrix elements

For the marked local configuration, an inverter of y cannot belong to S:
its commutator with y would put y² in the disjoint intersection H ∩ S.
Consequently the fifth-power relation gives order exactly five for xw.
An injective representation preserves this order and the order seven of y.
These facts discard the identity solution in the later matrix computation.

Source: Gorenstein, *Finite Groups*, §16.6, (6.2), pp.482–483. All local
configuration premises are explicit; this module does not construct w.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
open Subgroup
variable {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}

/-- An inverter of the marked seven-element cannot lie in the Sylow subgroup. -/
public theorem inverter_not_mem_sylow (D : NormalizerFrame h) (w : G)
    (hinv : w * D.y * w⁻¹ = D.y⁻¹) : w ∉ (h.sylow : Subgroup G) := by
  intro hw
  have hconj : D.y * w⁻¹ * D.y⁻¹ ∈ (h.sylow : Subgroup G) :=
    (mem_normalizer_iff.mp (D.H_le D.y_mem) w⁻¹).mp ((h.sylow : Subgroup G).inv_mem hw)
  have he : w * (D.y * w⁻¹ * D.y⁻¹) = D.y⁻¹ * D.y⁻¹ := by
    calc
      _ = (w * D.y * w⁻¹) * D.y⁻¹ := by group
      _ = _ := by rw [hinv]
  have hin : D.y⁻¹ * D.y⁻¹ ∈ (h.sylow : Subgroup G) :=
    he ▸ (h.sylow : Subgroup G).mul_mem hw hconj
  have hone : D.y⁻¹ * D.y⁻¹ = 1 := disjoint_def.mp D.disjoint
    (D.H.mul_mem (D.H.inv_mem D.y_mem) (D.H.inv_mem D.y_mem)) hin
  have hsquare : D.y ^ 2 = 1 := by
    rw [pow_two]
    simpa only [mul_inv_rev, inv_inv, inv_one] using congrArg (fun a : G => a⁻¹) hone
  have hd := orderOf_dvd_of_pow_eq_one hsquare
  rw [D.order_y] at hd
  norm_num at hd

/-- The source fifth-power relation has a nonidentity product, hence order exactly five. -/
public theorem product_order (D : BruhatFrame h) : orderOf (D.x * D.w) = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hn : D.x * D.w ≠ 1 := by
    intro he
    have hw : D.w = D.x⁻¹ := eq_inv_of_mul_eq_one_right he
    exact inverter_not_mem_sylow D.toNormalizerFrame D.w D.w_inverts
      (hw ▸ (h.sylow : Subgroup G).inv_mem D.x_mem)
  exact orderOf_eq_prime_iff.mpr ⟨D.product_fifth, hn⟩

/-- The actual elements used by the source matrix argument retain their orders
in every supplied faithful representation. No irreducibility is assumed. -/
public theorem representation_orders (D : BruhatFrame h)
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) :
    orderOf (ρ D.y) = 7 ∧ orderOf (ρ (D.x * D.w)) = 5 := by
  rw [orderOf_injective ρ hρ, orderOf_injective ρ hρ]
  exact ⟨D.order_y, product_order D⟩

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
