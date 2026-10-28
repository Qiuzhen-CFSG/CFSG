module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalCounts.Commuting
public import Theory.GroupTheory.PPrimeCoreHall
public import Theory.GroupTheory.NormalizingInvolutionCentralizer
import Mathlib.Tactic

/-!
# The cyclic odd subgroup in the three-normalizer

A double transposition in the actual alternating model inverts a three-cycle.
Sylow conjugacy and the marked centralizer equivalence transport that inverter
to every local element of order three. The odd factor in Bender (4.1) is the
normal Hall odd subgroup of its centralizer, so the entire three-normalizer
preserves it. Its fixed subgroup under the marked involution has order three,
by the common-centralizer calculation and the disjoint product with `⟨z⟩`.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
pp.225–226, the inversion assertion of (4.2).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

private abbrev M := alternatingGroup (Fin 5) × Multiplicative (ZMod 2)
private def three : M :=
  (⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩, 1)
private def reflection : M :=
  (⟨Equiv.swap 0 2 * Equiv.swap 3 4, by simp [Equiv.Perm.mem_alternatingGroup]⟩, 1)
private theorem three_order : orderOf three = 3 := by
  apply orderOf_eq_prime <;> decide +kernel
private theorem reflection_order : orderOf reflection = 2 := by
  apply orderOf_eq_prime <;> decide +kernel
private theorem reflection_inverts : reflection * three * reflection⁻¹ = three⁻¹ := by
  decide +kernel

private theorem model_inverter (x : M) (hx : orderOf x = 3) :
    ∃ t : M, orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹ := by
  have hP (P : Sylow 3 M) : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity]
    have hc : Nat.card M = 120 := by
      rw [Nat.card_prod, nat_card_alternatingGroup]
      norm_num [Nat.factorial, Nat.card_eq_fintype_card]
    rw [hc]
    decide +kernel
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_card_eq_prime (zpowers three) three
    (mem_zpowers three) three_order hP x hx
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hg
  let e := MulAut.conj g
  have hr : reflection * e x * reflection⁻¹ = (e x)⁻¹ := by
    change (MulAut.conj reflection) (e x) = (e x)⁻¹
    rw [show e x = three ^ n from hn.symm, map_zpow]
    change (reflection * three * reflection⁻¹) ^ n = _
    rw [reflection_inverts, inv_zpow]
  refine ⟨e.symm reflection, (e.symm.orderOf_eq _).trans reflection_order, ?_⟩
  apply e.injective
  simpa only [map_mul, map_inv, e.apply_symm_apply] using hr

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The actual alternating model supplies an involution in `C_G(z)`
inverting each of its elements of order three. -/
public theorem exists_local_three_inverter (x : G)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3) :
    ∃ t : G, t ∈ centralizer ({h.z} : Set G) ∧ orderOf t = 2 ∧
      t * x * t⁻¹ = x⁻¹ := by
  let C := centralizer ({h.z} : Set G)
  let e := h.alternatingCentralizerEquiv
  let xC : C := ⟨x, hxC⟩
  have hx' : orderOf (e xC) = 3 := (e.orderOf_eq _).trans
    ((orderOf_injective C.subtype Subtype.val_injective xC).symm.trans hx)
  obtain ⟨u, hu, hi⟩ := model_inverter (e xC) hx'
  let t := e.symm u
  have ht : orderOf (t : G) = 2 :=
    (orderOf_injective C.subtype Subtype.val_injective t).trans
      ((e.symm.orderOf_eq _).trans hu)
  refine ⟨t, t.property, ht, ?_⟩
  have he : t * xC * t⁻¹ = xC⁻¹ := by
    apply e.injective
    simpa only [t, map_mul, map_inv, MulEquiv.apply_symm_apply] using hi
  exact congrArg Subtype.val he


/-- The cyclic odd factor is preserved by the full three-normalizer. Its
intersection with the marked involution centralizer has order three. -/
public theorem exists_three_inversion_structure_of_structure
    (s : OddPrimeCentralizerStructure h) (x : G)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3) :
    ∃ (t : G) (A : Subgroup G),
      t ∈ centralizer ({h.z} : Set G) ∧ orderOf t = 2 ∧
      t * x * t⁻¹ = x⁻¹ ∧ IsCyclic A ∧
      (Nat.card A = 3 ∨ Nat.card A = 15) ∧
      normalizer (zpowers x : Set G) ≤ normalizer (A : Set G) ∧
      Disjoint A (zpowers h.z) ∧
      A ⊔ zpowers h.z = centralizer ({x} : Set G) ∧
      x ∈ A ∧
      Nat.card (A ⊓ centralizer ({h.z} : Set G) : Subgroup G) = 3 := by
  obtain ⟨t, htz, ht, htx⟩ := h.exists_local_three_inverter x hxC hx
  obtain ⟨A, hcyc, hcard, hn, hd, hsup⟩ := s.decomposition 3 (Or.inl rfl) x hxC hx
  have hAC : A ≤ centralizer ({x} : Set G) := hsup ▸ le_sup_left
  have hCN : centralizer ({x} : Set G) ≤ normalizer (A : Set G) := by
    rw [← hsup]
    exact sup_le A.le_normalizer hn
  have hCcard : Nat.card (centralizer ({x} : Set G)) = 2 * Nat.card A := by
    rw [← hsup, card_sup_eq_mul_of_normalizes_of_disjoint A _ hn hd,
      Nat.card_zpowers, h.involution, Nat.mul_comm]
  have hodd : Nat.Coprime 2 (Nat.card A) := by
    rcases hcard with he | he <;> rw [he] <;> decide
  have hNA : normalizer (zpowers x : Set G) ≤ normalizer (A : Set G) := by
    apply normalizer_le_normalizer_of_centralizer_hall 2 (zpowers x) A (n := 1)
    · simpa only [zpowers_eq_closure, centralizer_closure] using hAC
    · simpa only [zpowers_eq_closure, centralizer_closure] using hCN
    · exact hodd
    · simpa only [pow_one, zpowers_eq_closure, centralizer_closure] using hCcard
  have hxA : x ∈ A := by
    let C := centralizer ({x} : Set G)
    let D := A.subgroupOf C
    let _ : D.Normal := (normal_subgroupOf_iff_le_normalizer hAC).mpr hCN
    have hDcard : Nat.card D = Nat.card A :=
      Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv
    have hidx : D.index = 2 := by
      have he := D.index_mul_card
      rw [hDcard] at he
      change D.index * Nat.card A = Nat.card (centralizer ({x} : Set G)) at he
      rw [hCcard] at he
      exact Nat.mul_right_cancel (Nat.card_pos (α := A)) he
    let xC : C := ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩
    have hxo : orderOf xC = 3 :=
      (orderOf_injective C.subtype Subtype.val_injective xC).symm.trans hx
    have htwo : orderOf (QuotientGroup.mk' D xC) ∣ 2 := by
      simpa only [← index_eq_card, hidx] using orderOf_dvd_natCard (QuotientGroup.mk' D xC)
    have hthree : orderOf (QuotientGroup.mk' D xC) ∣ 3 :=
      hxo ▸ orderOf_map_dvd (QuotientGroup.mk' D) xC
    exact (QuotientGroup.eq_one_iff xC).mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3) htwo hthree))
  have hzout : h.z ∉ A := by
    intro hzA
    have he : h.z = 1 := disjoint_def.mp hd hzA (mem_zpowers h.z)
    exact h.z_ne_one he
  have hf := card_centralizer_sup_zpowers_of_normalizing_involution A h.z
    (h.involution ▸ pow_orderOf_eq_one h.z) hzout (hn (mem_zpowers h.z))
  have hf' : Nat.card ((A ⊔ zpowers h.z) ⊓ centralizer ({h.z} : Set G) : Subgroup G) =
      2 * Nat.card (A ⊓ centralizer ({h.z} : Set G) : Subgroup G) := by
    rw [← map_subtype_centralizer_singleton (A ⊔ zpowers h.z)
      ⟨h.z, mem_sup_right (mem_zpowers h.z)⟩,
      card_map_of_injective Subtype.val_injective]
    exact hf
  rw [hsup, inf_comm, h.common_prime_centralizer_card 3 (Or.inl rfl) x hxC hx] at hf'
  exact ⟨t, A, htz, ht, htx, hcyc, hcard, hNA, hd, hsup, hxA, by omega⟩

end CFSG.Quasithin.Janko1CentralizerData
