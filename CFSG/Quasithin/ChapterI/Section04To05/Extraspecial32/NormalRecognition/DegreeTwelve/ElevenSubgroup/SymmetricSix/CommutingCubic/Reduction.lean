module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.Contracts
public import Theory.GroupTheory.OrderThreeCentralizer

/-!
# The odd subgroup needed for the commuting cubic

The transfer step in Aschbacher's Lemma 4.5 constructs the odd subgroup of
`C_G(X)`, invariant under both marked involutions. The later four-group
calculation needs its fixed subgroup under `z` and its index two. These are
recorded below as an intermediate contract, without asserting that it is inhabited.
The additional three-part is proved separately from either ambient order.
In particular the contract contains neither a commuting cubic nor either
of the final centralizer orders.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.5, p.40.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.CommutingCubic

open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The transfer input, before the four-group argument. -/
public structure OddCentralizerData (h : Hypotheses z) (a : SourceGeometry h) where
  P : Subgroup G
  le_centralizer : P ≤ centralizer (cubicInG h : Set G)
  odd : Odd (Nat.card P)
  z_normalizes : z ∈ normalizer (P : Set G)
  u_normalizes : a.u ∈ normalizer (P : Set G)
  fixed_z : P ⊓ Centralizer z = cubicInG h
  centralizer_card : Nat.card (centralizer (cubicInG h : Set G)) = 2 * Nat.card P

/-- Either ambient order in 4.3 gives the additional three-part in `C_G(X)`. -/
public theorem nine_dvd_cubicCentralizer {h : Hypotheses z} (a : SourceGeometry h) :
    9 ∣ Nat.card (centralizer (cubicInG h : Set G)) := by
  have hG : 9 ∣ Nat.card G := by
    rcases a.order_cases with hc | hc <;> rw [hc] <;> norm_num
  let : IsCyclic (cubicInG h) := isCyclic_of_prime_card (cubicInG_card h)
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (cubicInG h)).mp
    (inferInstance : IsCyclic (cubicInG h))
  have ho : orderOf x = 3 := by rw [← Nat.card_zpowers, hx, cubicInG_card]
  have he : centralizer (cubicInG h : Set G) = centralizer ({x} : Set G) := by
    rw [← hx, zpowers_eq_closure, centralizer_closure]
  rw [he]
  exact nine_dvd_card_centralizer_of_order_three hG x ho

/-- The ambient-order argument is not an additional premise of the transfer data. -/
public theorem OddCentralizerData.nine_dvd {h : Hypotheses z} {a : SourceGeometry h}
    (o : OddCentralizerData h a) : 9 ∣ Nat.card o.P := by
  have hd := nine_dvd_cubicCentralizer a
  rw [o.centralizer_card] at hd
  exact (show Nat.Coprime 9 2 by decide).dvd_of_dvd_mul_left hd

public theorem u_commutes_z {h : Hypotheses z} (a : SourceGeometry h) :
    Commute a.u z := mem_centralizer_singleton_iff.mp a.u_centralizes

public theorem uz_order {h : Hypotheses z} (a : SourceGeometry h) :
    orderOf (a.u * z) = 2 := by
  have hu : a.u ^ 2 = 1 := a.u_order ▸ pow_orderOf_eq_one a.u
  have hz : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
  apply (orderOf_eq_prime_iff (p := 2)).mpr
  refine ⟨?_, ?_⟩
  · rw [(u_commutes_z a).mul_pow, hu, hz, one_mul]
  · intro he
    have hue : a.u = z⁻¹ := eq_inv_of_mul_eq_one_left he
    exact a.u_not_core (hue ▸ (coreInG z).inv_mem h.involution_mem_coreInG)

/-- The second allowed involution remains outside the core. -/
public theorem uz_not_core {h : Hypotheses z} (a : SourceGeometry h) :
    a.u * z ∉ coreInG z := by
  intro hu
  have hh := (coreInG z).mul_mem hu ((coreInG z).inv_mem h.involution_mem_coreInG)
  exact a.u_not_core (by simpa only [mul_inv_cancel_right] using hh)

/-- The existing outside-core orbit producer supplies exactly the missing fusion.
Its orbit statement is internal to `C_G(z)`; `a.u_fused` transports it to G. -/
public theorem uz_fused_of_outside_transitive {h : Hypotheses z} (a : SourceGeometry h)
    (ht : ∀ x : G, x ∈ Centralizer z → x ∉ coreInG z → orderOf x = 2 →
      ∃ c : Centralizer z, MulAut.conj (c : G) a.u = x) : IsConj z (a.u * z) := by
  obtain ⟨c, hc⟩ := ht (a.u * z)
    ((Centralizer z).mul_mem a.u_centralizes (mem_centralizer_singleton_iff.mpr rfl))
    (uz_not_core a) (uz_order a)
  exact a.u_fused.trans (isConj_iff.mpr ⟨c, hc⟩)

/-- Either allowed choice of the marked involution still inverts the same X. -/
public theorem choice_inverts_X {h : Hypotheses z} (a : SourceGeometry h)
    {v : G} (hv : v = a.u ∨ v = a.u * z) (x : G) (hx : x ∈ cubicInG h) :
    v * x * v⁻¹ = x⁻¹ := by
  have hu : a.u * x * a.u⁻¹ = x⁻¹ := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact a.u_inverts_X ⟨y, hy⟩
  have hz : z * x * z⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (cubicInG_le h hx)).symm
  rcases hv with rfl | rfl
  · exact hu
  · calc
      (a.u * z) * x * (a.u * z)⁻¹ = a.u * (z * x * z⁻¹) * a.u⁻¹ := by group
      _ = x⁻¹ := by rw [hz, hu]

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.CommutingCubic
