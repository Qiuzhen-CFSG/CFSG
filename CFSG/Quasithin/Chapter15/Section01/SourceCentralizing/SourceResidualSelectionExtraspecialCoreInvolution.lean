module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.OmegaIntersection
public import Theory.GroupTheory.PCoreCommutator

/-!
# An actual intersection-core involution modulo the original two-core

For the full chosen module, the original intersection core has kernel
exactly O₂(M). Its nontrivial two-group image modulo O₂(M) therefore contains
an involution whose action image is still an involution. Ordering places the
normal action kernel inside the intersection, so the core commutator theorem
makes this involution centralize the kernel image modulo O₂(M).

This uses the original source hypotheses and the literal action map. It
does not require an extraspecial action or any global residual premise.
Source: Aschbacher--Smith 14.1.14, 14.1.17, and 15.1.14.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The full source module produces an involution in the actual quotient by
O₂(M), with nontrivial involution image in the action and centralizing its
original kernel image. Only N ≠ M is required of the distinct maximal local. -/
theorem PreparedChosenModule.full_intersection_core_involution
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) :
    let R₀ := ((M ⊓ N).pCoreIn 2).subgroupOf M
    let q := QuotientGroup.mk' (pCore 2 M)
    let f := (actionHom M V h.normalized).rangeRestrict
    ∃ r ∈ R₀, orderOf (q r) = 2 ∧ orderOf (f r) = 2 ∧
      q r ∈ centralizer (f.ker.map q : Set (M ⧸ pCore 2 M)) := by
  let R₀ := ((M ⊓ N).pCoreIn 2).subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let f := (actionHom M V h.normalized).rangeRestrict
  have hker : f.ker = (centralizer (V : Set G)).subgroupOf M := by
    rw [show f = (actionHom M V h.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict, actionHom_ker]
  have hQK : pCore 2 M ≤ f.ker := by
    rw [hker]
    have hi := le_centralizer_iff.mp (h.reduced T hM.1.2).le_centralizer_pCore
    intro x hx v hv
    exact congrArg M.subtype (hi hx ⟨v, h.le_selected hv⟩ hv)
  obtain ⟨hmeet, hnoncentral⟩ := h.full_intersection_core_noncentral
    hG T hempty hM hN hJ hu hmany hNM.symm hfull
  have hRKQ : R₀ ⊓ f.ker ≤ pCore 2 M := by
    intro x hx
    have hxC : (x : G) ∈ centralizer (V : Set G) := by
      exact show x ∈ (centralizer (V : Set G)).subgroupOf M from hker ▸ hx.2
    have hxQ : (x : G) ∈ M.pCoreIn 2 := hmeet ▸ ⟨hx.1, hxC⟩
    obtain ⟨y, hy, he⟩ := hxQ
    exact (show y = x from Subtype.ext he) ▸ hy
  have hRnot : ¬ R₀ ≤ f.ker := by
    intro hr
    apply hnoncentral
    intro r hrR
    let rM : M := ⟨r, ((pCoreIn_le 2 _).trans inf_le_left) hrR⟩
    have hm := hr (show rM ∈ R₀ from hrR)
    rw [hker] at hm
    exact hm
  let U := R₀.map q
  have hUne : U ≠ ⊥ := by
    intro hb
    apply hRnot
    have hrQ : R₀ ≤ pCore 2 M := by
      have hh := (Subgroup.map_eq_bot_iff R₀).mp hb
      simpa only [q, QuotientGroup.ker_mk'] using hh
    exact hrQ.trans hQK
  have hUp : IsPGroup 2 U := ((isPGroup_pCoreIn 2 (M ⊓ N)).comap_subtype).map q
  have htwo : 2 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := hUp.exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hn0
      have hc := (one_lt_card_iff_ne_bot U).mpr hUne
      rw [hn, hn0, pow_zero] at hc
      omega
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 htwo
  have ha' : orderOf (a : M ⧸ pCore 2 M) = 2 := (Subgroup.orderOf_coe a).trans ha
  obtain ⟨r, hr, he⟩ := a.property
  have hqr : orderOf (q r) = 2 := by rw [he]; exact ha'
  have hqrne : q r ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at hqr
    norm_num at hqr
  have hfrne : f r ≠ 1 := by
    intro hf1
    have hrQ := hRKQ ⟨hr, hf1⟩
    apply hqrne
    change r ∈ q.ker
    simpa only [q, QuotientGroup.ker_mk'] using hrQ
  have hfrsquare : (f r) ^ 2 = 1 := by
    have hrQ : r ^ 2 ∈ pCore 2 M := by
      have hh : r ^ 2 ∈ q.ker := by
        change q (r ^ 2) = 1
        rw [map_pow]
        simpa only [hqr] using pow_orderOf_eq_one (q r)
      simpa only [q, QuotientGroup.ker_mk'] using hh
    simpa only [MonoidHom.mem_ker, map_pow] using hQK hrQ
  refine ⟨r, hr, hqr, orderOf_eq_prime hfrsquare hfrne, ?_⟩
  have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hCN : M ⊓ centralizer (V : Set G) ≤ N := by
    rw [hfull]
    exact ((lemma_A_5_3 ho).2.2 (maximal_local_normalizer_from_source hG T hN)).trans inf_le_left
  let H := (M ⊓ N).subgroupOf M
  have hKH : f.ker ≤ H := by
    intro x hx
    rw [hker] at hx
    exact ⟨x.property, hCN ⟨x.property, hx⟩⟩
  have hcomm : ⁅f.ker, R₀⁆ ≤ pCore 2 M := by
    rw [show R₀ = H.pCoreIn 2 from (pCoreIn_subgroupOf 2 (M ⊓ N) M inf_le_left).symm]
    exact commutator_pCoreIn_le_of_normal f.ker H hKH
  have hcentral : R₀.map q ≤ centralizer (f.ker.map q : Set (M ⧸ pCore 2 M)) := by
    apply le_centralizer_iff.mp
    rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcomm
  exact hcentral (mem_map_of_mem q hr)

end CFSG.Quasithin.Chapter15.Section01
