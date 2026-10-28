module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Geometry of the actual enlargement

The contrary involution centralizes the entire layer closure. Applying
component balance excludes equality with L and gives the swapped or proper
component alternatives, with relative subnormality retained. The original
and contrary involutions generate an actual elementary four-group in T_C.

Source: Aschbacher–Smith, 16.3.8–9, printed pp.1179–1180. The balance
premise is the earlier I.3.1–2 specialization, not a conclusion of §16.3.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The contrary involution supplies the actual input of 16.1.7, with z and t exchanged. -/
theorem setup (h : TerminalCounterexample T z L t) :
    ComponentTransfer.Setup z t L := by
  refine ⟨h.localSetup.involution, h.involution, h.localSetup.component, ?_⟩
  have hzt : z ∈ involutionCentralizer t := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp
      (h.localSetup.sylow_centralizes h.mem_commutingSylow.1)).symm
  have hs : zpowers z ⊔ L ≤ involutionCentralizer t :=
    sup_le (zpowers_le.mpr hzt) (fun x hx =>
      mem_centralizer_singleton_iff.mpr (h.mem_commutingSylow.2 x hx))
  exact fun x hx => mem_centralizer_singleton_iff.mp (hs hx)

/-- All conjugates generating K lie in C_G(t). -/
theorem enlargement_le (h : TerminalCounterexample T z L t) :
    enlargement t L ≤ involutionCentralizer t := by
  apply ComponentTransfer.layerClosure_le
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (h.mem_commutingSylow.2 x hx)

/-- If t lies in K, it lies in its center. -/
theorem involution_mem_center (h : TerminalCounterexample T z L t) (htK : t ∈ enlargement t L) :
    (⟨t, htK⟩ : enlargement t L) ∈ center (enlargement t L) := by
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (show (x : G) ∈ involutionCentralizer t from
    ComponentTransfer.layerClosure_le (fun y hy =>
      mem_centralizer_singleton_iff.mpr (h.mem_commutingSylow.2 y hy)) x.property)


/-- In the inside case the center of K is nontrivial. -/
theorem center_ne_bot (h : TerminalCounterexample T z L t) (htK : t ∈ enlargement t L) :
    center (enlargement t L) ≠ ⊥ := by
  intro he
  have hm := involution_mem_center h htK
  rw [he] at hm
  have ht1 : t = 1 := congrArg Subtype.val (mem_bot.mp hm)
  have := h.involution
  simp [ht1] at this

/-- Balance and nonterminality force genuine strict enlargement. -/
theorem enlargement_proper (h : TerminalCounterexample T z L t)
    (balance : ComponentTransfer.OrdinaryBalanceAt (involutionCentralizer t) z) :
    L < enlargement t L := by
  have hle := ComponentTransfer.le_layerClosure (involutionCentralizer t) L
  apply lt_of_le_of_ne hle
  intro he
  apply h.not_component
  have hLt := (setup h).le_centralizer
  refine ⟨hLt, ?_, ?_⟩
  · simpa only [← he] using ComponentTransfer.closure_subnormal_of_balance (setup h) balance
  · let := h.localSetup.component.quasisimple
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLt).symm

/-- Balance leaves precisely the swapped or proper component branch. -/
theorem proper_structure (h : TerminalCounterexample T z L t)
    (balance : ComponentTransfer.OrdinaryBalanceAt (involutionCentralizer t) z) :
    let K := enlargement t L
    ComponentTransfer.SwappedComponents (involutionCentralizer t) z L K ∨
      (ComponentTransfer.IsComponentIn K (involutionCentralizer t) ∧
        ⁅K, zpowers z⁆ = K ∧
        ComponentTransfer.IsComponentIn L (ComponentTransfer.centralizerIn K z) ∧ L < K) := by
  rcases ComponentTransfer.enlargement_structure_of_balance (setup h) balance with hn | hp
  · exact (h.not_component hn.2).elim
  · exact hp


variable [Finite G]

private theorem not_mem_zpowers (h : TerminalCounterexample T z L t) :
    t ∉ zpowers z := by
  intro hm
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, h.localSetup.involution] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · have ht1 : t = 1 := by simpa using he.symm
    have ht := h.involution
    simp [ht1] at ht
  · exact h.ne_original (by simpa using he.symm)

/-- The distinct commuting involutions generate an elementary group of order four. -/
theorem four_group (h : TerminalCounterexample T z L t) :
    IsElementaryAbelian 2 (zpowers z ⊔ zpowers t : Subgroup G) ∧
      Nat.card (zpowers z ⊔ zpowers t : Subgroup G) = 4 := by
  let : IsElementaryAbelian 2 (zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one
      (h.localSetup.involution ▸ pow_orderOf_eq_one z)
  have hz : z ∈ involutionCentralizer t := (setup h).t_mem
  have hc : Nat.card (zpowers z) = 2 ^ 1 := by
    simpa only [Nat.card_zpowers, pow_one] using h.localSetup.involution
  simpa using IsElementaryAbelian.fixed_join_card (zpowers z) t h.involution
    ((zpowers z).disjoint_zpowers_of_prime_order_not_mem t h.involution (not_mem_zpowers h))
    (zpowers_le.mpr hz) hc

omit [Finite G] in
/-- Both generators of the four-group belong to the actual T_C. -/
theorem four_le_commutingSylow (h : TerminalCounterexample T z L t) :
    zpowers z ⊔ zpowers t ≤ commutingSylow T L := by
  apply sup_le
  · exact zpowers_le.mpr ⟨h.localSetup.mem_sylow,
      h.localSetup.involution_mem_componentCentralizer⟩
  · exact zpowers_le.mpr h.mem_commutingSylow


end CFSG.Quasithin.Chapter16.EnlargementSieve
