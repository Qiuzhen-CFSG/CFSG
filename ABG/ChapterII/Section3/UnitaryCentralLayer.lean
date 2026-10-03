module
public import ABG.ChapterII.Section2.UnitaryCentralProductModel
public import Theory.GroupTheory.CentralProductCenter

/-!
# The original central SL2 layer as a prescribed unitary model

Let Z be a central cyclic subgroup of order 2^(r+1), and L0 a specified
SL2(GF(p^d)) subgroup meeting Z in order two. For odd p, nonzero d and
2^(r+1) dividing p^d+1, their actual join is isomorphic to the unitary
determinant level r. The equivalence preserves the underlying GL2 matrix
of a supplied special-unitary identification on L0, and sends the original
central factor onto the full center of the model. Field orders three and
nine are included.

Restrict both factors to their join and use the proved unitary central-product
model. Adjust its input map by the supplied special-unitary equivalence and
the canonical one; the canonical inverse then cancels, leaving exactly the
prescribed matrix identification. The two-element overlap is the full center
of the SL2 factor. The shared central-product-center theorem therefore makes
the original Z the center of the join, which the same chosen equivalence
transports to the model center.

This is the unitary central-layer step in ABG II.3 Proposition 3, article
pages 26–27. Keeping the supplied special-unitary equivalence allows the
parent theorem to choose it compatible with the actual coefficient action.
The exterior extension comparison and action lift are separate steps.
-/

namespace ABG

public theorem unitary_central_layer_model
    {H : Type*} [Group H] [Finite H]
    (p d : ℕ) [Fact p.Prime] (hp : Odd p) (hd : d ≠ 0)
    (r : ℕ) (hdiv : 2 ^ (r + 1) ∣ p ^ d + 1)
    (Z L0 : Subgroup H) [IsCyclic Z]
    (hZ : Z ≤ Subgroup.center H) (hZcard : Nat.card Z = 2 ^ (r + 1))
    (hcap : Nat.card (Z ⊓ L0 : Subgroup H) = 2)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d))
    (eSU : (unitaryForm 2 p d hd).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d)) :
    ∃ e : (Z ⊔ L0 : Subgroup H) ≃* SU2Level p d hd r,
      (∀ l : L0, (e ⟨l.val, (show L0 ≤ Z ⊔ L0 from le_sup_right) l.property⟩).val.val =
        (eSU.symm (eL0 l)).val) ∧
      (Z.subgroupOf (Z ⊔ L0)).map e.toMonoidHom = Subgroup.center (SU2Level p d hd r) := by
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
  let adjusted := (eL.trans eL0).trans (eSU.symm.trans (specialUnitaryTwo_equiv_sl2 p d hp hd))
  obtain ⟨e, he⟩ := exists_mulEquiv_SU2Level_of_central_product
    p d hp hd r hdiv ZB LB hZBc hgen hZBcarr hi adjusted
  have hF : Odd (Nat.card (GaloisField p d)) := by
    rw [GaloisField.card p d hd]
    exact hp.pow
  have hLC : Nat.card (Subgroup.center LB) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr (eL.trans eL0)).toEquiv,
      ← GorensteinWalter.sl2ProjectiveProjection_ker (GaloisField p d)]
    exact GorensteinWalter.sl2ProjectiveProjection_ker_card (GaloisField p d) hF
  have hOverlap := Subgroup.overlap_center ZB LB hZBc hLC hi
  have hcenter : Subgroup.center B = ZB := Subgroup.center_eq_of_central_product ZB LB hZBc hgen (by
    rintro _ ⟨l, hl, rfl⟩
    rw [← hOverlap] at hl
    exact hl)
  refine ⟨e, ?_, ?_⟩
  · intro l
    have heq := congrArg Subtype.val (he ⟨⟨l.val, hLB l.property⟩, l.property⟩)
    simp only [adjusted, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at heq
    exact heq.trans (SU2LevelZeroEquivSpecial_symm_val p d hd _)
  · change ZB.map e.toMonoidHom = _
    rw [← hcenter]
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (Subgroup.centerCongr e ⟨b, hb⟩).property
    · intro hx
      exact ⟨e.symm x, (Subgroup.centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩

end ABG
