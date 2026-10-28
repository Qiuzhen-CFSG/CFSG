module

public import Theory.GroupTheory.SylowCentralFusion.Selection
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Odd-order movers normalizing the Sylow centralizer

For a selected subgroup Q, put N = N_G(Q) and C = C_G(Q). Intersecting the
specified Sylow subgroup of N with its normal subgroup C gives C_T(Q) as a
Sylow subgroup of C. Frattini's argument gives N = N_N(C_T(Q)) C.
Since C fixes z, the first factor must move z. Its Sylow two-subgroup fixes z,
so an odd prime divisor of the stabilizer index supplies an odd-order mover.

This proves the common first paragraph of Glauberman's Lemma 1, p.155,
Math. Z. 93 (1966), DOI 10.1007/BF01111033. The literal ambient intersections
and subtype maps are retained throughout.
-/

namespace SylowCentralFusion
open Subgroup
universe u
variable {G : Type u} [Group G]

private theorem exists_odd_order_outside [Finite G] (T : Sylow 2 G)
    (C : Subgroup G) (hTC : (T : Subgroup G) ≤ C) (hC : C ≠ ⊤) :
    ∃ x : G, Odd (orderOf x) ∧ x ∉ C := by
  have hindex : C.index ≠ 1 := fun h => hC (index_eq_one.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hindex
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact T.not_dvd_index (hpd.trans (index_dvd_of_le hTC))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := G)
  have hS : ¬ (S : Subgroup G) ≤ C := by
    intro hSC
    exact S.not_dvd_index (hpd.trans (index_dvd_of_le hSC))
  obtain ⟨x, hxS, hxC⟩ := Set.not_subset.mp hS
  refine ⟨x, ?_, hxC⟩
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_orderOf_eq_pow ⟨x, hxS⟩
  rw [Subgroup.orderOf_mk] at hn
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow


/-- Sylow conjugacy in the centralizer, followed by a prime divisor of the
point stabilizer's index, supplies an odd-order mover with both normalizations.
The subgroup is exactly the one selected in the input. -/
public theorem NormalizerSelection.exists_witness [Finite G] (T : Sylow 2 G) (z : G)
    (hz : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (s : NormalizerSelection T z) :
    ∃ w : Witness T z, w.subgroup = s.subgroup := by
  classical
  let Q := s.subgroup
  let N := normalizer (Q : Set G)
  let C := (centralizer (Q : Set G)).subgroupOf N
  let F := (centralizer ({z} : Set G)).subgroupOf N
  obtain ⟨R, hR⟩ := s.normalizer_sylow
  have hRmem (x : N) : x ∈ (R : Subgroup N) ↔ (x : G) ∈ (T : Subgroup G) := by
    calc
      x ∈ (R : Subgroup N) ↔ (x : G) ∈ (R : Subgroup N).map N.subtype :=
        (mem_map_iff_mem Subtype.val_injective).symm
      _ ↔ (x : G) ∈ (T : Subgroup G) := by
        rw [hR]
        exact and_iff_left x.property
  obtain ⟨P, hP⟩ := R.exists_subgroupOf_eq_of_normal C
  have hPC : (P : Subgroup C).map C.subtype = (R : Subgroup N) ⊓ C := by
    rw [hP, subgroupOf_map_subtype]
  let K := normalizer (((R : Subgroup N) ⊓ C : Subgroup N) : Set N)
  have htop : K ⊔ C = ⊤ := by
    change normalizer (((R : Subgroup N) ⊓ C : Subgroup N) : Set N) ⊔ C = ⊤
    rw [← hPC]
    exact P.normalizer_sup_eq_top
  have hRK : (R : Subgroup N) ≤ K := by
    intro r hr
    apply inf_normalizer_le_normalizer_inf
    refine ⟨le_normalizer hr, ?_⟩
    rw [C.normalizer_eq_top]
    exact mem_top _
  have hCF : C ≤ F := by
    intro c hc
    exact centralizer_le (Set.singleton_subset_iff.mpr s.mem_subgroup) hc
  have hKnot : ¬ K ≤ F := by
    intro hKF
    have hFtop : F = ⊤ := top_le_iff.mp (htop ▸ sup_le hKF hCF)
    obtain ⟨g, hgN, hgm⟩ := s.moves
    have hgF : (⟨g, hgN⟩ : N) ∈ F := hFtop ▸ mem_top _
    have hgcomm : g * z = z * g := mem_centralizer_singleton_iff.mp hgF
    apply hgm
    rw [hgcomm, mul_inv_cancel_right]
  let S : Sylow 2 K := R.subtype hRK
  have hSF : (S : Subgroup K) ≤ F.subgroupOf K := by
    intro x hx
    have hxR : (x : N) ∈ (R : Subgroup N) := hx
    change ((x : N) : G) ∈ centralizer ({z} : Set G)
    exact mem_centralizer_singleton_iff.mpr (hz _ ((hRmem _).mp hxR))
  have hFproper : F.subgroupOf K ≠ ⊤ := by
    intro h
    apply hKnot
    intro k hk
    have : (⟨k, hk⟩ : K) ∈ F.subgroupOf K := h ▸ mem_top _
    exact this
  obtain ⟨x, hxo, hxF⟩ := exists_odd_order_outside S (F.subgroupOf K) hSF hFproper
  let h : G := ((x : K) : N)
  have hhmove : h * z * h⁻¹ ≠ z := by
    intro he
    apply hxF
    change h ∈ centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul).mp he
  have hD : (R : Subgroup N) ⊓ C =
      ((T : Subgroup G) ⊓ centralizer (Q : Set G)).subgroupOf N := by
    ext y
    exact and_congr (hRmem y) Iff.rfl
  have hhD : h ∈ normalizer
      (((T : Subgroup G) ⊓ centralizer (Q : Set G)) : Set G) := by
    have hxn := x.property
    change (x : N) ∈ normalizer (((R : Subgroup N) ⊓ C : Subgroup N) : Set N) at hxn
    rw [hD, ← subgroupOf_normalizer_eq
      (inf_le_right.trans (centralizer_le_normalizer (Q : Set G)))] at hxn
    exact hxn
  have hho : Odd (orderOf h) := by
    have h1 := orderOf_injective K.subtype Subtype.val_injective x
    have h2 := orderOf_injective N.subtype Subtype.val_injective (x : N)
    exact h2.symm ▸ h1.symm ▸ hxo
  exact ⟨⟨Q, h, s.le_sylow, s.mem_subgroup, s.normalizer_sylow,
    (x : N).property, hhD, hho, hhmove⟩, rfl⟩

end SylowCentralFusion
