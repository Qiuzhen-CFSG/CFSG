module
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.CyclicFour.Factors
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.Frattini.PGroup

/-!
# Embedded quaternion central products from the Frattini subgroup

A binary group of order 64 with cyclic center of order four and Frattini
subgroup of order two contains an embedded central product (Q₈ * Q₈) * C₄.
The center's generator has square in the Frattini subgroup, so its square
generates that subgroup. The existing binary-square factor theorem then
constructs two commuting quaternion groups. Their join has center of order
two, which computes its intersection with the original cyclic center.

The conclusion retains the actual factors, their intersection, and their
commutation and generation properties. This is the structural step used
in Aschbacher--Smith 14.3.32, printed p.1004; the factor construction is the
one used for I.2.2(6a), printed pp.410 and 412.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The unique Frattini involution is the square of a central generator. -/
theorem cyclicFourCenter_frattini_eq_square [IsCyclic (center G)]
    (hp : IsPGroup 2 G) (hZ : Nat.card (center G) = 4)
    (hΦ : Nat.card (frattini G) = 2) :
    ∃ z : G, orderOf z = 4 ∧ center G = zpowers z ∧
      frattini G = zpowers (z ^ 2) := by
  let : Fact (IsPGroup 2 G) := ⟨hp⟩
  obtain ⟨z, hz⟩ := (center G).isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have ho : orderOf z = 4 := by rw [← Nat.card_zpowers, hz, hZ]
  have hs : Nat.card (zpowers (z ^ 2)) = 2 := by
    rw [Nat.card_zpowers, orderOf_pow, ho]
    decide
  refine ⟨z, ho, hz.symm, ?_⟩
  exact (eq_of_le_of_card_ge
    (zpowers_le.mpr (pth_power_mem_frattini_of_isPGroup (p := 2) z))
    (by rw [hΦ, hs])).symm

/-- Construct the actual commuting quaternion join and cyclic-four factor. -/
theorem exists_quaternionCentralProduct_cyclicFour [IsCyclic (center G)]
    (hp : IsPGroup 2 G) (hcard : Nat.card G = 64)
    (hZ : Nat.card (center G) = 4) (hΦ : Nat.card (frattini G) = 2) :
    ∃ B D : Subgroup G, Nonempty (QuaternionCentralProductData B) ∧
      Nonempty (D ≃* Multiplicative (ZMod 4)) ∧
      Nat.card (B ⊓ D : Subgroup G) = 2 ∧
      (∀ b ∈ B, ∀ d ∈ D, b * d = d * b) ∧ B ⊔ D = ⊤ := by
  let : Fact (IsPGroup 2 G) := ⟨hp⟩
  obtain ⟨z, ho, hz, hphi⟩ := cyclicFourCenter_frattini_eq_square hp hZ hΦ
  have hsq (x : G) : x ^ 2 ∈ zpowers (z ^ 2) := by
    rw [← hphi]
    exact pth_power_mem_frattini_of_isPGroup (p := 2) x
  obtain ⟨Q, R, hQ, hR, hinter, hcomm, hgen⟩ :=
    EvenCliffordSix.CyclicFourRecognition.exists_factors z ho hz hcard hsq
  let B : Subgroup G := Q ⊔ R
  have hsignCard : Nat.card (zpowers (z ^ 2)) = 2 := by
    rw [Nat.card_zpowers, orderOf_pow, ho]
    decide
  let d : QuaternionCentralProductData B := {
    left := Q.subgroupOf B
    right := R.subgroupOf B
    left_model := ⟨(subgroupOfEquivOfLe (show Q ≤ B from le_sup_left)).trans hQ.some⟩
    right_model := ⟨(subgroupOfEquivOfLe (show R ≤ B from le_sup_right)).trans hR.some⟩
    intersection_card := by
      change Nat.card ((Q ⊓ R).subgroupOf B) = 2
      rw [Nat.card_congr (subgroupOfEquivOfLe
        (show Q ⊓ R ≤ B from inf_le_left.trans le_sup_left)).toEquiv, hinter]
      exact hsignCard
    commute := fun q hq r hr => Subtype.ext (hcomm q hq r hr)
    span := by
      rw [← subgroupOf_sup (show Q ≤ B from le_sup_left) (show R ≤ B from le_sup_right)]
      exact subgroupOf_self B }
  have hZle : zpowers z ≤ center G := le_of_eq hz.symm
  have hupper : zpowers z ⊓ B ≤ (center B).map B.subtype := by
    intro x hx
    exact ⟨⟨x, hx.2⟩, mem_center_iff.mpr
      (fun b => Subtype.ext (mem_center_iff.mp (hZle hx.1) b)), rfl⟩
  have hlower : zpowers (z ^ 2) ≤ zpowers z ⊓ B := by
    refine le_inf (zpowers_le.mpr ((zpowers z).pow_mem (mem_zpowers z) 2)) ?_
    rw [← hinter]
    exact inf_le_left.trans le_sup_left
  have hover : Nat.card (zpowers z ⊓ B : Subgroup G) = 2 := by
    have hu := Subgroup.card_le_of_le hupper
    have hl := Subgroup.card_le_of_le hlower
    rw [card_subtype, d.center_card] at hu
    rw [hsignCard] at hl
    omega
  refine ⟨B, zpowers z, ⟨d⟩, ⟨mulEquivOfCyclicCardEq ?_⟩, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, ho]
    change 4 = Nat.card (ZMod 4)
    rw [Nat.card_zmod]
  · simpa only [inf_comm] using hover
  · intro b _ x hx
    exact mem_center_iff.mp (hz ▸ hx) b
  · simpa only [sup_comm] using hgen
end Theory.GroupTheory
