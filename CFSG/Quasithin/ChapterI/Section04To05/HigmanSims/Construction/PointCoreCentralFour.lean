module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreLifts

/-!
# The original point core's central cyclic four

The cyclic-four center supplies an actual ambient generator whose square
is the marked involution. It centralizes the entire seed, placing it in
the whole normalizer core. The original involution centralizer normalizes
this cyclic four, so every element moving its generator inverts it.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem ambient_core_shape (h : TypeAt z V) :
    CoreShape ((involutionCentralizer z).pCoreIn 2) :=
  (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv
      ((pCore 2 (involutionCentralizer z)).equivMapOfInjective
        (involutionCentralizer z).subtype (involutionCentralizer z).subtype_injective)

/-- The original point-core center has an ambient generator of order four,
whose square is the marked point and which lies in the whole normalizer core. -/
theorem TypeAt.exists_point_core_central_four (h : TypeAt z V) :
    ∃ c : G, orderOf c = 4 ∧ c ^ 2 = z ∧
      c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
        ((involutionCentralizer z).pCoreIn 2).subtype ∧
      c ∈ (normalizer (V : Set G)).pCoreIn 2 := by
  classical
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  obtain ⟨e⟩ := (ambient_core_shape h).center_model
  let c : center Q := e.symm (Multiplicative.ofAdd (1 : ZMod 4))
  have hc4 : orderOf (c.val : G) = 4 := by
    rw [orderOf_coe, orderOf_coe]
    exact (e.symm.orderOf_eq _).trans ((orderOf_ofAdd_eq_addOrderOf (1 : ZMod 4)).trans
      (ZMod.addOrderOf_one 4))
  have hc2 : (c.val : G) ^ 2 = z := by
    have hh := h.centralizer_core_square_mem (c.val : G) c.val.property
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hh
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hh
    have hn2 : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · have htwo : (c.val : G) ^ 2 = 1 := by simpa using he.symm
      have hd := orderOf_dvd_of_pow_eq_one htwo
      rw [hc4] at hd
      norm_num at hd
    · simpa using he.symm
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 H).map H.subtype
    rw [← h.centralizer_fitting]
    exact h.seed_le_core
  refine ⟨c.val, hc4, hc2, ⟨c.val, c.property, rfl⟩, ?_⟩
  change (c.val : G) ∈ (pCore 2 (normalizer (V : Set G))).map
    (normalizer (V : Set G)).subtype
  rw [← h.seed_centralizer]
  intro v hv
  exact congrArg Subtype.val (mem_center_iff.mp c.property (⟨v, hVQ hv⟩ : Q))

/-- An element of the original involution centralizer which moves a
generator of the point-core center must invert that literal generator. -/
theorem TypeAt.point_core_central_four_inverted (h : TypeAt z V)
    (c : G) (hc4 : orderOf c = 4)
    (hcZ : c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
      ((involutionCentralizer z).pCoreIn 2).subtype)
    (b : G) (hb : b ∈ involutionCentralizer z) (hnc : ¬ Commute b c) :
    b * c * b⁻¹ = c⁻¹ := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  have hHN : H ≤ normalizer (Q : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg q hq
    obtain ⟨qH, hqH, rfl⟩ := hq
    exact ⟨⟨g, hg⟩ * qH * (⟨g, hg⟩ : H)⁻¹,
      (inferInstance : (pCore 2 H).Normal).conj_mem qH hqH ⟨g, hg⟩, rfl⟩
  obtain ⟨cQ, hcQ, rfl⟩ := hcZ
  let x : center Q := ⟨cQ, hcQ⟩
  let a : MulAut Q := Q.normalizerMonoidHom ⟨b, hHN hb⟩
  let y : center Q := centerCongr a x
  obtain ⟨e⟩ := (ambient_core_shape h).center_model
  have hx4 : orderOf x = 4 := by
    rw [← orderOf_coe, ← orderOf_coe]
    exact hc4
  have hy4 : orderOf y = 4 := ((centerCongr a).orderOf_eq x).trans hx4
  have hcases : e y = e x ∨ e y = (e x)⁻¹ := by
    have square_ne_one (a : center Q) (ha : orderOf a = 4) : (e a) ^ 2 ≠ 1 := by
      intro he
      have hd := orderOf_dvd_of_pow_eq_one he
      rw [e.orderOf_eq, ha] at hd
      norm_num at hd
    have cert : ∀ s t : Multiplicative (ZMod 4), s ^ 2 ≠ 1 → t ^ 2 ≠ 1 →
        t = s ∨ t = s⁻¹ := by decide +kernel
    exact cert (e x) (e y) (square_ne_one x hx4) (square_ne_one y hy4)
  rcases hcases with he | he
  · have hexy : y = x := e.injective he
    have heG := congrArg (fun q : center Q => (q.val : G)) hexy
    change b * (cQ : G) * b⁻¹ = cQ at heG
    exact (hnc (mul_inv_eq_iff_eq_mul.mp heG)).elim
  · have hexy : y = x⁻¹ := e.injective (he.trans (e.map_inv x).symm)
    exact congrArg (fun q : center Q => (q.val : G)) hexy

end CFSG.Quasithin.HigmanSims
