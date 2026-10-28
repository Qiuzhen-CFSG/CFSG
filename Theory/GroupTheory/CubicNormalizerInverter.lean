module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The normalizer of a cubic line with a specified inverter

An automorphism of a cyclic group of order three either fixes or inverts
its generator. Consequently a specified inverter supplements the element
centralizer in the full line normalizer. The actual inverter is retained.
The consumer is the torus in `G2Recognition.CubicTorus`, following
Fong–Wong, Nagoya Math. J.36 (1969), §3B(ii), printed p.156.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
theorem mem_normalizer_zpowers_of_inverts (x n : G) (hinv : n*x*n⁻¹=x⁻¹) :
    n ∈ normalizer (zpowers x : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change zpowers (n*x*n⁻¹) = zpowers x
  rw [hinv,zpowers_inv]

theorem cubic_normalizer_eq_centralizer_sup_inverter [Finite G] (x n : G)
    (hx : orderOf x = 3) (hinv : n*x*n⁻¹=x⁻¹) :
    normalizer (zpowers x : Set G) = centralizer ({x} : Set G) ⊔ zpowers n := by
  classical
  have hCN : centralizer ({x} : Set G) ≤ normalizer (zpowers x : Set G) := by
    rw [←centralizer_closure,←zpowers_eq_closure]
    exact centralizer_le_normalizer _
  apply le_antisymm ?_ (sup_le hCN (zpowers_le.mpr (mem_normalizer_zpowers_of_inverts x n hinv)))
  intro g hg
  have hmem : g*x*g⁻¹ ∈ zpowers x := (hg x).mp (mem_zpowers x)
  rw [mem_zpowers_iff_mem_range_orderOf,hx] at hmem
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hmem
  have hi3 := Finset.mem_range.mp hi
  have hn : n ∈ centralizer ({x} : Set G) ⊔ zpowers n := mem_sup_right (mem_zpowers n)
  interval_cases i
  · have hx1 : x=1 := (MulAut.conj g).injective (by simpa using he.symm)
    simp [hx1] at hx
  · apply mem_sup_left
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (by simpa using he.symm))
  · have hx2 : x^2=x⁻¹ := by
      apply mul_left_cancel (a := x)
      rw [mul_inv_cancel,←pow_succ',show x^3=1 by simpa only [hx] using pow_orderOf_eq_one x]
    have hgx : g*x*g⁻¹=x⁻¹ := he.symm.trans hx2
    have hgn : g*n ∈ centralizer ({x} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        (g*n)*x*(g*n)⁻¹ = g*(n*x*n⁻¹)*g⁻¹ := by group
        _ = g*x⁻¹*g⁻¹ := by rw [hinv]
        _ = (g*x*g⁻¹)⁻¹ := by group
        _ = x := by rw [hgx,inv_inv]
    simpa only [mul_inv_cancel_right] using
      (centralizer ({x} : Set G) ⊔ zpowers n).mul_mem (mem_sup_left hgn)
        ((centralizer ({x} : Set G) ⊔ zpowers n).inv_mem hn)
theorem map_subtype_normalizer_zpowers (H : Subgroup G) (x : H) :
    (normalizer (zpowers x : Set H)).map H.subtype = H ⊓ normalizer (zpowers (x:G) : Set G) := by
  have he : (zpowers (x:G)).subgroupOf H = zpowers x := by
    change (zpowers (H.subtype x)).subgroupOf H = zpowers x
    rw [←MonoidHom.map_zpowers]
    exact (zpowers x).comap_map_eq_self_of_injective H.subtype_injective
  rw [←he,←subgroupOf_normalizer_eq (zpowers_le.mpr x.property),subgroupOf_map_subtype,inf_comm]
theorem cubic_normalizer_card_of_involutive_inverter [Finite G] (x n : G)
    (hx : orderOf x = 3) (hn : orderOf n = 2) (hinv : n*x*n⁻¹=x⁻¹) :
    Nat.card (normalizer (zpowers x : Set G)) = Nat.card (centralizer ({x} : Set G)) * 2 := by
  classical
  let C := centralizer ({x} : Set G)
  have hnC : n ∉ C := by
    intro hh
    have hxe : x=x⁻¹ := by
      simpa only [mem_centralizer_singleton_iff.mp hh,mul_inv_cancel_right] using hinv
    have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]
      exact (congrArg (fun y => x*y) hxe).trans (mul_inv_cancel x))
    rw [hx] at hd
    omega
  have hdis : Disjoint C (zpowers n) := by
    apply disjoint_iff.mpr
    apply le_antisymm ?_ bot_le
    intro g hg
    have hgC : g ∈ C := hg.1
    have hh : g ∈ zpowers n := hg.2
    rw [mem_zpowers_iff_mem_range_orderOf,hn] at hh
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hh
    have hi2 := Finset.mem_range.mp hi
    interval_cases i
    · exact mem_bot.mpr (by simpa using he.symm)
    · have hgEq : g=n := by simpa only [pow_one] using he.symm
      rw [hgEq] at hgC
      exact (hnC hgC).elim
  have hnorm : zpowers n ≤ normalizer (C : Set G) := by
    apply zpowers_le.mpr
    have hh := normalizer_le_normalizer_centralizer (zpowers x)
      (mem_normalizer_zpowers_of_inverts x n hinv)
    simpa only [zpowers_eq_closure,centralizer_closure] using hh
  rw [cubic_normalizer_eq_centralizer_sup_inverter x n hx hinv,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnorm hdis,Nat.card_zpowers,hn]
end Subgroup
