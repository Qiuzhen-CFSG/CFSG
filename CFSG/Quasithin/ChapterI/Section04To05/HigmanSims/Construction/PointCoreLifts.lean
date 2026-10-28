module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AmbientControl

/-!
# Involutory representatives in the original HS point core

Every square in the quaternion--cyclic point core is either one or the
distinguished involution. Its central cyclic-four subgroup lies in the
original seed centralizer. Multiplying by its generator therefore changes
an order-four representative into an involution without changing its coset
modulo the seed-normalizer core.

These are consequences of the exact HS1--HS2 hypotheses preceding
Aschbacher--Smith I.4.8, printed p.418. They supply actual root lifts for
the plane-centralizer construction; no splitting is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims

private theorem core_square_central {A : Type*} [Group A] [Finite A]
    (h : CoreShape A) (a : A) : a ^ 2 ∈ center A ∧ a ^ 4 = 1 := by
  obtain ⟨B, D, ⟨hB⟩, ⟨eD⟩, hi, hc, hs⟩ := h
  have hDc : D ≤ center A := by
    intro d hd
    have hh : B ⊔ D ≤ centralizer ({d} : Set A) := by
      apply sup_le
      · intro b hb
        exact mem_centralizer_singleton_iff.mpr (hc b hb d hd)
      · intro c hc
        apply mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (eD.injective (by simp only [map_mul, mul_comm]) :
          (⟨c, hc⟩ : D) * ⟨d, hd⟩ = ⟨d, hd⟩ * ⟨c, hc⟩)
    exact mem_center_iff.mpr fun x =>
      mem_centralizer_singleton_iff.mp (hh (hs ▸ mem_top x))
  have hBZ : (B ⊓ D : Subgroup A) = (center B).map B.subtype := by
    apply eq_of_le_of_card_ge
    · intro b hb
      exact ⟨⟨b, hb.1⟩, mem_center_iff.mpr fun c => Subtype.ext (hc c c.property b hb.2), rfl⟩
    · rw [card_map_of_injective B.subtype_injective, hB.center_card, hi]
  have hn : B ≤ normalizer (D : Set A) := by
    intro b hb
    exact centralizer_le_normalizer (D : Set A) fun d hd => (hc b hb d hd).symm
  have ha : a ∈ (↑(B ⊔ D) : Set A) := hs ▸ mem_top a
  rw [coe_mul_of_left_le_normalizer_right B D hn] at ha
  obtain ⟨b, hb, d, hd, rfl⟩ := ha
  have hbZ : b ^ 2 ∈ (center B).map B.subtype :=
    ⟨(⟨b, hb⟩ : B) ^ 2, hB.square_mem_center _, rfl⟩
  have hbD : b ^ 2 ∈ D := by rw [← hBZ] at hbZ; exact hbZ.2
  have hb4 : b ^ 4 = 1 := by
    have hh := congrArg (fun x : center B => (x.val : A))
      (hB.center_square ⟨(⟨b, hb⟩ : B) ^ 2, hB.square_mem_center _⟩)
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul] using hh
  have hd4 : d ^ 4 = 1 := by
    have hcD : Nat.card D = 4 := by rw [Nat.card_congr eD.toEquiv]; simp
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨d, hd⟩ : D)))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hcD] using hh
  constructor
  · rw [(show Commute b d from hc b hb d hd).mul_pow]
    exact (center A).mul_mem (hDc hbD) (hDc (D.pow_mem hd 2))
  · rw [(show Commute b d from hc b hb d hd).mul_pow, hb4, hd4, one_mul]

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem point_center_mem (h : TypeAt z V) :
    ∃ hz : z ∈ (involutionCentralizer z).pCoreIn 2,
      (⟨z, hz⟩ : (involutionCentralizer z).pCoreIn 2) ∈
        center ((involutionCentralizer z).pCoreIn 2) := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  let zH : H := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzq : zH ∈ pCore 2 H := h.centralizer_twoCore_selfCentralizing fun q _ =>
    Subtype.ext (mem_centralizer_singleton_iff.mp q.property)
  have hz : z ∈ Q := ⟨zH, hzq, rfl⟩
  refine ⟨hz, mem_center_iff.mpr fun q => Subtype.ext ?_⟩
  exact mem_centralizer_singleton_iff.mp ((map_subtype_le (pCore 2 H)) q.property)

/-- Every square in the original point core lies in the marked involution line. -/
theorem TypeAt.centralizer_core_square_mem (h : TypeAt z V) (q : G)
    (hq : q ∈ (involutionCentralizer z).pCoreIn 2) : q ^ 2 ∈ zpowers z := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  let e : pCore 2 H ≃* Q := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hs : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv e
  obtain ⟨hc, hfour⟩ := core_square_central hs (⟨q, hq⟩ : Q)
  by_cases htwo : q ^ 2 = 1
  · rw [htwo]; exact (zpowers z).one_mem
  obtain ⟨hz, hzZ⟩ := point_center_mem h
  obtain ⟨a⟩ := hs.center_model
  let : IsCyclic (center Q) := a.isCyclic.mpr inferInstance
  have he : (⟨(⟨q, hq⟩ : Q) ^ 2, hc⟩ : center Q) = ⟨⟨z, hz⟩, hzZ⟩ := by
    apply IsCyclic.eq_of_orderOf_eq_two
    · apply orderOf_eq_prime_iff.mpr
      constructor
      · apply Subtype.ext
        change ((⟨q, hq⟩ : Q) ^ 2) ^ 2 = 1
        simpa only [← pow_mul] using hfour
      · intro hh
        exact htwo (congrArg (fun x : center Q => (x.val : G)) hh)
    · simpa only [← orderOf_coe] using h.involution
  have hh : q ^ 2 = z := congrArg (fun x : center Q => (x.val : G)) he
  exact hh ▸ mem_zpowers z

/-- Every original point-core element has a square-one representative in the
same actual coset of the seed-normalizer two-core. -/
theorem TypeAt.centralizer_core_involutory_representative (h : TypeAt z V)
    (q : G) (hq : q ∈ (involutionCentralizer z).pCoreIn 2) :
    ∃ t : G, t ∈ (involutionCentralizer z).pCoreIn 2 ∧ t ^ 2 = 1 ∧
      t * q⁻¹ ∈ (normalizer (V : Set G)).pCoreIn 2 := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  let P := (normalizer (V : Set G)).pCoreIn 2
  let e : pCore 2 H ≃* Q := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hs : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv e
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 H).map H.subtype
    rw [← h.centralizer_fitting]
    exact h.seed_le_core
  have hZP (c : center Q) : (c.val : G) ∈ P := by
    change (c.val : G) ∈ (pCore 2 (normalizer (V : Set G))).map
      (normalizer (V : Set G)).subtype
    rw [← h.seed_centralizer]
    intro v hv
    exact congrArg Subtype.val (mem_center_iff.mp c.property (⟨v, hVQ hv⟩ : Q))
  obtain ⟨a⟩ := hs.center_model
  have root : ∀ x : Multiplicative (ZMod 4), x ^ 2 = 1 → ∃ c, c ^ 2 = x := by
    decide +kernel
  have hqZ := (core_square_central hs (⟨q, hq⟩ : Q)).1
  let s : center Q := ⟨(⟨q, hq⟩ : Q) ^ 2, hqZ⟩
  have hs2 : s ^ 2 = 1 := by
    apply Subtype.ext
    change ((⟨q, hq⟩ : Q) ^ 2) ^ 2 = 1
    simpa only [← pow_mul] using (core_square_central hs (⟨q, hq⟩ : Q)).2
  obtain ⟨b, hb⟩ := root (a s) (by rw [← map_pow, hs2, map_one])
  let c := a.symm b
  have hc2 : c ^ 2 = s := by
    apply a.injective
    simpa only [map_pow, MulEquiv.apply_symm_apply, c] using hb
  let t : G := (c.val : G) * q
  have hcomm : Commute (c.val : G) q := by
    exact (congrArg Subtype.val (mem_center_iff.mp c.property (⟨q, hq⟩ : Q))).symm
  have hc2G : (c.val : G) ^ 2 = q ^ 2 := congrArg (fun x : center Q => (x.val : G)) hc2
  refine ⟨t, Q.mul_mem c.val.property hq, ?_, ?_⟩
  · change ((c.val : G) * q) ^ 2 = 1
    rw [hcomm.mul_pow, hc2G, ← pow_add]
    exact congrArg Subtype.val (core_square_central hs (⟨q, hq⟩ : Q)).2
  · change (c.val : G) * q * q⁻¹ ∈ P
    rw [mul_inv_cancel_right]
    exact hZP c

end CFSG.Quasithin.HigmanSims
