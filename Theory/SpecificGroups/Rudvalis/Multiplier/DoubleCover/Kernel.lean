module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Raw
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Reducing the concrete scalar kernel to order two

The scalar group over GF(5) has order four. The explicit kernel involution
therefore makes the scalar kernel have order two or four. In the second case,
quotient by that central involution. The resulting group is still finite and
perfect and its projection onto the literal Rudvalis model has kernel order two.
This construction uses no upper bound on the universal multiplier.
-/

namespace Rudvalis.Multiplier.DoubleCover
public section
open PerfectCentralCovering

/-- A finite perfect central double cover of the actual model. -/
structure FiniteDoubleCover where
  Carrier : Type
  [group : Group Carrier]
  [finite : Finite Carrier]
  covering : Cover Carrier Rudvalis.Model
  kernel_card_two : Nat.card covering.toMonoidHom.ker = 2

private theorem order_dvd_subgroup_card {G : Type} [Group G]
    (K : Subgroup G) (x : G) (hx : x ∈ K) : orderOf x ∣ Nat.card K := by
  rw [Subgroup.orderOf_coe (⟨x, hx⟩ : K)]
  exact orderOf_dvd_natCard (⟨x, hx⟩ : K)

/-- The known square supplies the lower bound before scalarity is used. -/
theorem two_dvd_kernel_card : 2 ∣ Nat.card projection.ker := by
  have ho : orderOf z = 2 := orderOf_eq_prime z_sq z_ne_one
  have hdvd := order_dvd_subgroup_card projection.ker z projection_z
  rwa [ho] at hdvd

/-- The whole scalar-kernel computation needs only the four units of GF(5). -/
theorem kernel_card_le_four (h : ScalarKernel) : Nat.card projection.ker ≤ 4 := by
  classical
  let f : projection.ker → (ZMod 5)ˣ := fun x => (h x.val x.property).choose
  have hf (x : projection.ker) :
      x.val.val.1 = Matrix.GeneralLinearGroup.scalar (Fin 28) (f x) :=
    (h x.val x.property).choose_spec
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rw [hf x, hf y, hxy]
    · exact x.property.trans y.property.symm
  have hc : Nat.card (ZMod 5)ˣ = 4 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    rw [Nat.card_units, Nat.card_eq_fintype_card, ZMod.card]
  simpa only [hc] using Nat.card_le_card_of_injective f hinj

theorem kernel_card_two_or_four (h : ScalarKernel) :
    Nat.card projection.ker = 2 ∨ Nat.card projection.ker = 4 := by
  have hle := kernel_card_le_four h
  have hdvd := two_dvd_kernel_card
  have hpos := Nat.card_pos (α := projection.ker)
  omega

private theorem card_ker_mul_card {E G : Type} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) :
    Nat.card f.ker * Nat.card G = Nat.card E := by
  have h := f.ker.card_mul_index
  rwa [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h

/-- Construct the desired group as the paired group, or its quotient by the
explicit central involution. Scalarity is the sole outstanding input. -/
noncomputable def doubleCoverOfScalarKernel (h : ScalarKernel) : FiniteDoubleCover := by
  classical
  by_cases htwo : Nat.card projection.ker = 2
  · exact
      { Carrier := Raw
        group := inferInstance
        finite := inferInstance
        covering := coverOfScalarKernel h
        kernel_card_two := htwo }
  have hfour : Nat.card projection.ker = 4 := (kernel_card_two_or_four h).resolve_left htwo
  let N : Subgroup Raw := Subgroup.zpowers z
  have hNker : N ≤ projection.ker := Subgroup.zpowers_le.mpr projection_z
  have hNcenter : N ≤ Subgroup.center Raw := hNker.trans (ker_le_center_of_scalarKernel h)
  letI : N.Normal := ⟨by
    intro n hn g
    have hc := Subgroup.mem_center_iff.mp (hNcenter hn) g
    simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hn⟩
  have hNcard : Nat.card N = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime z_sq z_ne_one
  let q : Raw →* Raw ⧸ N := QuotientGroup.mk' N
  let f : Raw ⧸ N →* Rudvalis.Model := QuotientGroup.lift N projection hNker
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective N projection projection_surjective hNker
  have hcentral : f.ker ≤ Subgroup.center (Raw ⧸ N) := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : y ∈ projection.ker := hx
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N t
    have hc := Subgroup.mem_center_iff.mp ((ker_le_center_of_scalarKernel h) hy) s
    exact (map_mul q s y).symm.trans ((congrArg q hc).trans (map_mul q y s))
  have hqcard : 2 * Nat.card (Raw ⧸ N) = Nat.card Raw := by
    have hc := card_ker_mul_card q (QuotientGroup.mk'_surjective N)
    rw [QuotientGroup.ker_mk', hNcard] at hc
    exact hc
  have hfcard := card_ker_mul_card f hf
  have hpCard := card_ker_mul_card projection projection_surjective
  have hmul : (2 * Nat.card f.ker) * Nat.card Rudvalis.Model =
      4 * Nat.card Rudvalis.Model := by
    rw [mul_assoc, hfcard, hqcard, ← hpCard, hfour]
  have hk : Nat.card f.ker = 2 := by
    have hh := Nat.mul_right_cancel (Nat.card_pos (α := Rudvalis.Model)) hmul
    omega
  exact
    { Carrier := Raw ⧸ N
      group := inferInstance
      finite := inferInstance
      covering :=
        { toMonoidHom := f
          surjective := hf
          isPerfect := inferInstance
          ker_le_center := hcentral }
      kernel_card_two := hk }

end
end Rudvalis.Multiplier.DoubleCover
