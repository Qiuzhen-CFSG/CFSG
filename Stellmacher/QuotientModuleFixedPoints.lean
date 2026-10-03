module
public import Stellmacher.LaterDefs
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Fixed points of quotient-module actions

For a quotient-module witness, fixed points of the image of an ambient
subgroup Y are exactly the vectors centralized by Y. Mapping the fixed-point
subgroup along the injective module subtype identifies it with the ambient
intersection V ∩ C_G(Y), and injectivity gives the cardinality corollary.

The proof uses only the witness's explicit conjugation equation; it imposes
no further condition on the kernel or finiteness. This translates the index
terms in Stellmacher (8.1)(a), journal p.37, into the fixed-point measure of
Section 1 while retaining the exact action instance of the witness.
-/

namespace Stellmacher.Later

universe u

/-- The fixed subgroup maps onto the ambient centralizer intersection. -/
public theorem QuotientModuleWitness.fixedPoints_map_subtype
    {G : Type u} [Group G] {A B V : Subgroup G}
    (w : QuotientModuleWitness A B V) (Y : Subgroup G) (hYA : Y ≤ A) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom V w.action
    (FixedPoints.subgroup ((Y.subgroupOf A).map w.projection) V).map V.subtype =
      V ⊓ Subgroup.centralizer (Y : Set G) := by
  let := w.groupX
  let := MulDistribMulAction.compHom V w.action
  change (FixedPoints.subgroup ((Y.subgroupOf A).map w.projection) V).map V.subtype = _
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    let yA : A := ⟨y, hYA hy⟩
    have hyA : yA ∈ Y.subgroupOf A := hy
    have hfix := (FixedPoints.mem_subgroup
      (M := (Y.subgroupOf A).map w.projection) (a := v)).mp hv
        ⟨w.projection yA, Subgroup.mem_map_of_mem w.projection hyA⟩
    have heq := congrArg Subtype.val hfix
    change ((w.action (w.projection yA)) v : G) = v at heq
    rw [w.action_compatible] at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  · rintro ⟨hxV, hxY⟩
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    change (⟨x, hxV⟩ : V) ∈
      FixedPoints.subgroup ((Y.subgroupOf A).map w.projection) V
    rw [FixedPoints.mem_subgroup]
    intro y
    obtain ⟨yA, hyA, heq⟩ := y.property
    apply Subtype.ext
    change ((w.action y.val) (⟨x, hxV⟩ : V) : G) = x
    rw [← heq, w.action_compatible]
    change (yA : G) * x * (yA : G)⁻¹ = x
    change x ∈ Subgroup.centralizer (Y : Set G) at hxY
    rw [Subgroup.mem_centralizer_iff] at hxY
    rw [hxY yA hyA, mul_inv_cancel_right]

/-- Fixed points in the quotient action have the ambient centralizer order. -/
public theorem QuotientModuleWitness.fixedPoints_card
    {G : Type u} [Group G] {A B V : Subgroup G}
    (w : QuotientModuleWitness A B V) (Y : Subgroup G) (hYA : Y ≤ A) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom V w.action
    Nat.card (FixedPoints.subgroup ((Y.subgroupOf A).map w.projection) V) =
      Nat.card (V ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) := by
  let := w.groupX
  let := MulDistribMulAction.compHom V w.action
  rw [← w.fixedPoints_map_subtype Y hYA, Subgroup.card_map_of_injective V.subtype_injective]

end Stellmacher.Later
