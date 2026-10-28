module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Coordinates
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# Factor containment and faithful centralizer lifting

Compatible coordinates for I/O_{3′}(I) identify the embedded component
with A₆ and make the quotient by that component a two-group. Thus every
two-perfect local factor lies in the component. Faithfulness on this normal
component detects centralization even for its nonnormal subgroups.

These statements use the actual core quotient map. They do not identify
the core O_{3′}(I) with the residual O^{3′}(I), and the coordinates still
have to be constructed from the raw setup in 15.4.18.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, printed p.1163.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.QuotientCoordinates
variable {I : Type*} [Group I] {L : Subgroup I} (d : QuotientCoordinates L)

noncomputable def componentEquiv : L ≃* A6 :=
  (MulEquiv.ofBijective (d.quotientMap.subgroupMap L)
    ⟨fun _ _ h => d.component_faithful (congrArg Subtype.val h),
      d.quotientMap.subgroupMap_surjective L⟩).trans (MulEquiv.subgroupCongr d.component_image)

include d

theorem quotient_component_isTwoGroup [Finite I] [L.Normal] : IsPGroup 2 (I ⧸ L) := by
  let : L.Normal := d.component_normal
  obtain ⟨n, hn⟩ := d.kernel_two.exists_card_eq
  have hI := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 3 I)
  rw [Nat.card_congr d.equiv.toEquiv, s6_order, hn] at hI
  have hL := card_eq_card_quotient_mul_card_subgroup L
  rw [Nat.card_congr d.componentEquiv.toEquiv, a6_order, hI] at hL
  apply IsPGroup.of_card (n := n + 1)
  rw [pow_succ]
  omega

/-- Every two-perfect subgroup is contained in the component. The quotient
by the component is a two-group; this is unrelated to the 3′-core quotient. -/
theorem factor_le_component [Finite I] (Y : Subgroup I) (hY : IsPPerfect 2 Y) :
    Y ≤ L := by
  let : L.Normal := d.component_normal
  exact (le_pResidual_of_isPPerfect Y hY).trans
    (sInf_le ⟨d.component_normal, d.quotient_component_isTwoGroup⟩)

/-- A quotient faithful on a normal subgroup detects centralization of
all of its subgroups, including the nonnormal local factors. -/
theorem centralizer_lift (Y : Subgroup I) (hY : Y ≤ L) :
    (centralizer (Y.map d.quotientMap : Set S6)).comap d.quotientMap =
      centralizer (Y : Set I) := by
  let q := d.quotientMap
  let : L.Normal := d.component_normal
  apply le_antisymm
  · intro x hx y hy
    have hc : q y * q x = q x * q y := hx (q y) (mem_map_of_mem q hy)
    have he : x * y * x⁻¹ = y := by
      apply congrArg Subtype.val (d.component_faithful
        (a₁ := ⟨x * y * x⁻¹, d.component_normal.conj_mem y (hY hy) x⟩)
        (a₂ := ⟨y, hY hy⟩) _)
      change q (x * y * x⁻¹) = q y
      rw [map_mul, map_mul, map_inv, ← hc, mul_assoc, mul_inv_cancel, mul_one]
    have he' := congrArg (fun a => a * x) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'.symm
  · intro x hx a ha
    obtain ⟨y, hy, rfl⟩ := ha
    exact (map_mul q y x).symm.trans ((congrArg q (hx y hy)).trans (map_mul q x y))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.QuotientCoordinates
