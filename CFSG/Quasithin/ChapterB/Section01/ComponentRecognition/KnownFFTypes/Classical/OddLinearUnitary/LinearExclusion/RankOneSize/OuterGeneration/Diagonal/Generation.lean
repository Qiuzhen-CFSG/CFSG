module

public import Mathlib.Order.Atoms
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Four exterior involutions from a centralized maximal pair

Let N have index two. An exterior involution s centralizing a noncommuting
involution pair a,b gives three exterior involutions s,sa,sb. If the pair
generates a maximal subgroup of N, one more exterior involution suffices.
Indeed, fusion of sa with s transports sb to an involution not commuting
with s. A proper intersection of the four-generated subgroup with N would
be the original maximal subgroup and would force all four to commute with s.

This is the group-theoretic step for the diagonal case of Guralnick--Malle,
Classification of 2F-modules I, Proposition 4.1, manuscript pp.8--9.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Diagonal
open Subgroup

/-- Fusion can be performed inside an index-two subgroup when the source
and target both lie outside it. -/
theorem conjugator_mem_of_index_two {G : Type*} [Group G]
    (N : Subgroup G) (hindex : N.index = 2) {a b : G}
    (_ha : a ∉ N) (hb : b ∉ N) (hc : IsConj a b) :
    ∃ g : G, g ∈ N ∧ g * a * g⁻¹ = b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  by_cases hgN : g ∈ N
  · exact ⟨g, hgN, hg⟩
  · refine ⟨b * g, (N.mul_mem_iff_of_index_two hindex).mpr
      (iff_of_false hb hgN), ?_⟩
    calc
      (b * g) * a * (b * g)⁻¹ = b * (g * a * g⁻¹) * b⁻¹ := by group
      _ = b := by rw [hg]; group

/-- The low-torus construction needs four exterior involutions, all with
conjugators in the specified index-two subgroup. -/
theorem four_of_maximal_centralized_pair {G : Type*} [Group G]
    (N : Subgroup G) (hindex : N.index = 2)
    (hfuse : ∀ x y : G, x ∉ N → x ^ 2 = 1 → y ∉ N → y ^ 2 = 1 → IsConj x y)
    (s a b : G) (hsN : s ∉ N) (hs2 : s ^ 2 = 1)
    (haN : a ∈ N) (ha2 : a ^ 2 = 1) (hbN : b ∈ N) (hb2 : b ^ 2 = 1)
    (hsa : Commute s a) (hsb : Commute s b) (hab : ¬ Commute a b)
    (hmax : IsCoatom ((closure ({a, b} : Set G)).subgroupOf N))
    (t : G) (htN : t ∉ N) (ht2 : t ^ 2 = 1) :
    ∃ c : Fin 4 → N, N ≤ closure (Set.range fun j =>
      (c j : G) * t * (c j : G)⁻¹) := by
  classical
  let : N.Normal := N.normal_of_index_eq_two hindex
  have hsaN : s * a ∉ N := by
    intro h
    exact hsN (by simpa using N.mul_mem h (N.inv_mem haN))
  have hsbN : s * b ∉ N := by
    intro h
    exact hsN (by simpa using N.mul_mem h (N.inv_mem hbN))
  have hsa2 : (s * a) ^ 2 = 1 := by rw [hsa.mul_pow, hs2, ha2, mul_one]
  have hsb2 : (s * b) ^ 2 = 1 := by rw [hsb.mul_pow, hs2, hb2, mul_one]
  have hab' : ¬ Commute (s * a) (s * b) := by
    intro h
    apply hab
    have hss : s * s = 1 := by simpa [pow_two] using hs2
    have hh := h.eq
    rw [hsa.symm.mul_mul_mul_comm s b, hsb.symm.mul_mul_mul_comm s a,
      hss, one_mul, one_mul] at hh
    exact hh
  obtain ⟨k, _, hk⟩ := conjugator_mem_of_index_two N hindex hsaN hsN
    (hfuse (s * a) s hsaN hsa2 hsN hs2)
  let r : G := k * (s * b) * k⁻¹
  have hrN : r ∉ N := by
    intro hr
    have hback := (inferInstance : N.Normal).conj_mem r hr k⁻¹
    apply hsbN
    simpa [r, mul_assoc] using hback
  have hr2 : r ^ 2 = 1 := by
    change (MulAut.conj k) (s * b) ^ 2 = 1
    rw [← map_pow, hsb2, map_one]
  have hsr : ¬ Commute s r := by
    intro h
    apply hab'
    apply (commute_map_iff (MulAut.conj k).injective).mp
    change Commute (k * (s * a) * k⁻¹) r
    rwa [hk]
  let v : Fin 4 → G := ![s, s * a, s * b, r]
  have hvN (i : Fin 4) : v i ∉ N := by fin_cases i <;> assumption
  have hv2 (i : Fin 4) : v i ^ 2 = 1 := by fin_cases i <;> assumption
  have hvconj (i : Fin 4) : ∃ g : N, (g : G) * t * (g : G)⁻¹ = v i := by
    obtain ⟨g, hgN, hg⟩ := conjugator_mem_of_index_two N hindex htN (hvN i)
      (hfuse t (v i) htN ht2 (hvN i) (hv2 i))
    exact ⟨⟨g, hgN⟩, hg⟩
  choose c hc using hvconj
  refine ⟨c, ?_⟩
  let H := closure (Set.range fun j => (c j : G) * t * (c j : G)⁻¹)
  have hgen (i : Fin 4) : v i ∈ H := hc i ▸ subset_closure ⟨i, rfl⟩
  have hsH : s ∈ H := hgen 0
  have haH : a ∈ H := by
    have hh := H.mul_mem (H.inv_mem hsH) (hgen 1)
    simpa [v] using hh
  have hbH : b ∈ H := by
    have hh := H.mul_mem (H.inv_mem hsH) (hgen 2)
    simpa [v] using hh
  let D := closure ({a, b} : Set G)
  have hDH : D ≤ H := (closure_le _).mpr (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨haH, hbH⟩)
  have hDcent : D ≤ centralizer ({s} : Set G) := (closure_le _).mpr (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨mem_centralizer_singleton_iff.mpr hsa.symm.eq,
      mem_centralizer_singleton_iff.mpr hsb.symm.eq⟩)
  have hsub : D.subgroupOf N ≤ H.subgroupOf N := by intro x hx; exact hDH hx
  by_cases heq : D.subgroupOf N = H.subgroupOf N
  · exfalso
    have hsrN : s⁻¹ * r ∈ N := (N.mul_mem_iff_of_index_two hindex).mpr
      (iff_of_false (by simpa using hsN) hrN)
    have hsrH : s⁻¹ * r ∈ H := H.mul_mem (H.inv_mem hsH) (hgen 3)
    have hsrD : s⁻¹ * r ∈ D := by
      have hh : (⟨s⁻¹ * r, hsrN⟩ : N) ∈ H.subgroupOf N := hsrH
      rwa [← heq] at hh
    have hh := mem_centralizer_singleton_iff.mp (hDcent hsrD)
    apply hsr
    show s * r = r * s
    have hh' := congrArg (fun x : G => s * x) hh
    simpa [mul_assoc] using hh'.symm
  · exact subgroupOf_eq_top.mp (hmax.2 _ (lt_of_le_of_ne hsub heq))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Diagonal
