module

public import Theory.SpecificGroups.MacWilliams.HallJankoLiftAlgebra
public import Theory.GroupTheory.PGroup.NormalEightCenterTwoElementaryBound
public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing

/-!
# The common centralizer of a Hall–Janko frame

In an extension of order 128 with a self-centralizing abelian base of order 16,
the conjugation image has order eight. The frame equations give `TV = UVT`.
The action `U` is nonidentity: otherwise both marked generators have square one,
contradicting nontriviality of the marked four. Thus `T` does not centralize `V`,
and the common centralizer of `U,V` inside the conjugation image is a proper
subgroup, of order at most four.

An elementary sixteen containing the two marked involutions has its action
image in this common centralizer. The conjugation kernel formula then forces
its intersection with the base's first omega to have order four, proving that
it contains the marked four. Only these local order and frame assumptions are
needed; central-omega and normal-eight hypotheses are unnecessary here.

Source: the extension calculation underlying Janko–Thompson, Math. Z. 113
(1970), Theorem 1.3(a), printed p.386, citing MacWilliams, Trans. AMS 150
(1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
namespace MacWilliamsSylow.HallJankoActionFrame
variable {P : Type*} [Group P] {D W B : Subgroup P}

private theorem action_u_ne_one [D.Normal] (f : HallJankoActionFrame D W B)
    (hW : W ≠ ⊥) : (MulAut.conjNormal : P →* MulAut D) f.u ≠ 1 := by
  intro hu
  have ha : f.a ∈ D := by simp only [f.base]; exact subset_closure (by simp)
  have hb : f.b ∈ D := by simp only [f.base]; exact subset_closure (by simp)
  have ha' := congrArg (fun z : MulAut D => (z ⟨f.a, ha⟩ : P)) hu
  have hb' := congrArg (fun z : MulAut D => (z ⟨f.b, hb⟩ : P)) hu
  change f.u * f.a * f.u⁻¹ = f.a at ha'
  change f.u * f.b * f.u⁻¹ = f.b at hb'
  rw [f.ua, mul_inv_cancel_right] at ha'
  rw [f.ub, mul_inv_cancel_right] at hb'
  have hb2 : f.b ^ 2 = 1 := by simpa only [hb', ← pow_two] using inv_mul_cancel f.b
  have ha2 : f.a ^ 2 = 1 := by
    rw [hb2, mul_one] at ha'
    simpa only [ha', ← pow_two] using inv_mul_cancel f.a
  apply hW
  rw [f.four, ha2, hb2]
  simp

/-- The frame actions of `t` and `v` do not commute when the marked four is nontrivial. -/
public theorem action_t_v_not_commute [D.Normal] [IsMulCommutative D]
    (f : HallJankoActionFrame D W B)
    (hDC : centralizer (D : Set P) ≤ D) (hW : W ≠ ⊥) :
    ¬ Commute ((MulAut.conjNormal : P →* MulAut D) f.t)
      ((MulAut.conjNormal : P →* MulAut D) f.v) := by
  let α : P →* MulAut D := MulAut.conjNormal
  have hk : α.ker = D := conjNormal_ker_eq_of_selfCentralizing_abelian D hDC
  have hd := f.lift_defects_mem_base hDC |>.2.2
  have he : α (f.t * f.v * (f.u * f.v * f.t)⁻¹) = 1 :=
    MonoidHom.mem_ker.mp (hk.symm ▸ hd)
  have he' : α f.t * α f.v = α f.u * (α f.v * α f.t) := by
    simpa only [map_mul, map_inv, mul_assoc] using mul_inv_eq_one.mp (by simpa only [map_mul, map_inv, mul_assoc] using he)
  intro h
  have hu : α f.u = 1 := by
    have he'' : α f.v * α f.t = α f.u * (α f.v * α f.t) := h.eq ▸ he'
    exact (mul_right_cancel (he''.symm.trans (one_mul _).symm))
  exact f.action_u_ne_one hW hu

/-- The common centralizer of the two marked actions, inside the full conjugation
image of an order-128 extension, has order at most four. -/
public theorem card_action_commonCentralizer_le_four [Finite P] [D.Normal]
    [IsMulCommutative D] (f : HallJankoActionFrame D W B)
    (hP : Nat.card P = 128) (hD : Nat.card D = 16)
    (hDC : centralizer (D : Set P) ≤ D) (hW : W ≠ ⊥) :
    Nat.card (centralizer
      ({(MulAut.conjNormal : P →* MulAut D).rangeRestrict f.u,
        (MulAut.conjNormal : P →* MulAut D).rangeRestrict f.v} :
        Set (MulAut.conjNormal : P →* MulAut D).range)) ≤ 4 := by
  let α : P →* MulAut D := MulAut.conjNormal
  let C := centralizer ({α.rangeRestrict f.u, α.rangeRestrict f.v} : Set α.range)
  have hfull : Nat.card α.range = 8 := by
    have hc := α.ker.card_mul_index
    rw [index_ker, conjNormal_ker_eq_of_selfCentralizing_abelian D hDC, hD, hP] at hc
    omega
  have hproper : C ≠ ⊤ := by
    intro h
    have ht : α.rangeRestrict f.t ∈ C := h ▸ mem_top _
    have hv := ht (α.rangeRestrict f.v) (by simp)
    apply f.action_t_v_not_commute hDC hW
    exact congrArg (fun z : α.range => (z : MulAut D)) hv.symm
  have hi := C.one_lt_index_of_ne_top hproper
  have hc := C.card_mul_index
  rw [hfull] at hc
  change Nat.card C ≤ 4
  nlinarith

/-- The elementary subgroup's action image lies in the common centralizer of
its two marked involutions and consequently has order at most four. -/
public theorem card_conj_image_le_four [Finite P] [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 B] (f : HallJankoActionFrame D W B)
    (hP : Nat.card P = 128) (hD : Nat.card D = 16)
    (hDC : centralizer (D : Set P) ≤ D) (hW : W ≠ ⊥) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  let α : P →* MulAut D := MulAut.conjNormal
  let C := centralizer ({α.rangeRestrict f.u, α.rangeRestrict f.v} : Set α.range)
  let I := (α.rangeRestrict.comp B.subtype).range
  have hIC : I ≤ C := by
    rintro x ⟨b, rfl⟩ z hz
    have hb (y : P) (hy : y ∈ B) : y * (b : P) = b * y :=
      congrArg (fun z : B => (z : P))
        (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : B) b)
    rcases hz with rfl | ⟨rfl⟩
    · exact (map_mul α.rangeRestrict _ _).symm.trans
        ((congrArg α.rangeRestrict (hb f.u f.u_mem)).trans (map_mul _ _ _))
    · exact (map_mul α.rangeRestrict _ _).symm.trans
        ((congrArg α.rangeRestrict (hb f.v f.v_mem)).trans (map_mul _ _ _))
  have hcard : Nat.card ((α.comp B.subtype).range) = Nat.card I := by
    have he : α.comp B.subtype = α.range.subtype.comp (α.rangeRestrict.comp B.subtype) := rfl
    rw [he, MonoidHom.range_comp, card_map_of_injective α.range.subtype_injective]
  rw [hcard]
  exact (card_le_of_le hIC).trans (f.card_action_commonCentralizer_le_four hP hD hDC hW)

/-- An elementary sixteen in a Hall–Janko frame contains the marked four. -/
public theorem four_le_elementary_sixteen [Finite P] [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 B] (f : HallJankoActionFrame D W B)
    (hP : Nat.card P = 128) (hD : Nat.card D = 16)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hW : Nat.card W = 4) (hB : Nat.card B = 16) : W ≤ B := by
  have hWne : W ≠ ⊥ := (one_lt_card_iff_ne_bot W).mp (by omega)
  have him := f.card_conj_image_le_four hP hD hDC hWne
  have hc := card_eq_inf_omega_mul_conj_image_of_elementary W D hDC hO B
  rw [hB] at hc
  have hmeet : Nat.card W ≤ Nat.card (B ⊓ W : Subgroup P) := by
    rw [hW]
    nlinarith
  have heq : B ⊓ W = W := eq_of_le_of_card_ge inf_le_right hmeet
  exact heq ▸ inf_le_left

/-- The containment theorem with the C₄-square model supplied by frame construction. -/
public theorem four_le_elementary_sixteen_of_c4_square
    [Finite P] [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (f : HallJankoActionFrame D W B) (hP : Nat.card P = 128)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hW : Nat.card W = 4) (hB : Nat.card B = 16) : W ≤ B := by
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  exact f.four_le_elementary_sixteen hP hD hDC hO hW hB

end MacWilliamsSylow.HallJankoActionFrame
