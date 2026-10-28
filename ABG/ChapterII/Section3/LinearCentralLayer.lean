module
public import GorensteinWalter.SL2CentralProductModel
public import Theory.GroupTheory.CentralProductCenter

/-!
# The original central SL2 layer as a concrete linear model

Let Z be a central cyclic subgroup of order 2^(r+1), and let L0 be a
specified odd-field SL2 subgroup meeting Z in order two. If 2^(r+1)
divides |F|−1, their actual join is isomorphic to determinant level r.
The equivalence preserves the specified SL2 matrix map and carries the
original central factor to the exact center of that determinant model.

Restrict both original subgroups to their join and apply the proved
concrete central-product model. The overlap theorem identifies the
intersection with the full center of L0. The shared central-product-center
theorem therefore makes Z the center of the join, and the same chosen
equivalence transports it to the model center. No new matrix recognition
or assumed action matching is used.

This is the linear central-layer identification in
Alperin--Brauer--Gorenstein II.3 Proposition 3, article p26. Its precise
central-kernel map is retained for the following projective quotient and
index-two extension comparison; fields of orders three and nine remain.
-/

namespace ABG
open Matrix.GeneralLinearGroup

public theorem linear_central_layer_model
    {H : Type*} [Group H] [Finite H]
    (F : Type*) [Field F] [Finite F] (hF : Odd (Nat.card F))
    (r : ℕ) (hd : 2 ^ (r + 1) ∣ Nat.card F - 1)
    (Z L0 : Subgroup H) [IsCyclic Z]
    (hZ : Z ≤ Subgroup.center H) (hZcard : Nat.card Z = 2 ^ (r + 1))
    (hcap : Nat.card (Z ⊓ L0 : Subgroup H) = 2)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ e : (Z ⊔ L0 : Subgroup H) ≃* determinantTwoPower F r,
      (∀ l : L0, (e ⟨l.val, (show L0 ≤ Z ⊔ L0 from le_sup_right) l.property⟩).val =
        Matrix.SpecialLinearGroup.toGL (eL0 l)) ∧
      (Z.subgroupOf (Z ⊔ L0)).map e.toMonoidHom = Subgroup.center (determinantTwoPower F r) := by
  let B := Z ⊔ L0
  have hZB : Z ≤ B := le_sup_left
  have hLB : L0 ≤ B := le_sup_right
  let ZB := Z.subgroupOf B
  let LB := L0.subgroupOf B
  let eZ : ZB ≃* Z := Subgroup.subgroupOfEquivOfLe hZB
  let eL : LB ≃* L0 := Subgroup.subgroupOfEquivOfLe hLB
  let : IsCyclic ZB := eZ.isCyclic.mpr inferInstance
  have hZBc : ZB ≤ Subgroup.center B := by
    intro z hz
    apply Subgroup.mem_center_iff.mpr
    intro b
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZ hz) b)
  have hgen : ZB ⊔ LB = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hZB hLB, Subgroup.subgroupOf_self]
  have hZBcarr : Nat.card ZB = 2 ^ (r + 1) := (Nat.card_congr eZ.toEquiv).trans hZcard
  have hi : Nat.card (ZB ⊓ LB : Subgroup B) = 2 := by
    rw [← Subgroup.card_map_of_injective (K := ZB ⊓ LB) B.subtype_injective,
      Subgroup.map_inf _ _ _ B.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hZB, Subgroup.map_subgroupOf_eq_of_le hLB]
    exact hcap
  obtain ⟨e, he⟩ := Matrix.SpecialLinearGroup.exists_mulEquiv_determinantTwoPower_of_central_product
    F hF r hd ZB LB hZBc hgen hZBcarr hi (eL.trans eL0)
  have hLC : Nat.card (Subgroup.center LB) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr (eL.trans eL0)).toEquiv,
      ← GorensteinWalter.sl2ProjectiveProjection_ker F]
    exact GorensteinWalter.sl2ProjectiveProjection_ker_card F hF
  have hOverlap' := Subgroup.overlap_center ZB LB hZBc hLC hi
  have hcenter : Subgroup.center B = ZB := Subgroup.center_eq_of_central_product ZB LB hZBc hgen (by
    rintro _ ⟨l, hl, rfl⟩
    rw [← hOverlap'] at hl
    exact hl)
  refine ⟨e, ?_, ?_⟩
  · intro l
    exact he ⟨⟨l.val, hLB l.property⟩, l.property⟩
  · change ZB.map e.toMonoidHom = _
    rw [← hcenter]
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (Subgroup.centerCongr e ⟨b, hb⟩).property
    · intro hx
      exact ⟨e.symm x, (Subgroup.centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩

end ABG

