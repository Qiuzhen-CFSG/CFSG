module
public import Theory.Representation.SL3.DualLiftCentralizers

/-!
# Abelian subgroup bounds from dual-axis centralizers

For an additive subgroup of V × V, suppose every nonzero first-axis
vector forces the second projection onto its scalar line. If the first-axis
kernel or the second projection is zero, one projection is injective.
Otherwise both the kernel and image of the second projection have order
at most |F|. For V = Dual(F³), the subgroup therefore has order at most
|F|³ in all cases.

Applied to the image of an abelian subgroup of a central extension of two
dual modules, this bounds its order by |F|³ times the central kernel order.
NonblockMSRankBounds applies the result to the original MS core, whose
natural kernel has order |F|³. These are the core rank calculations used
in Aschbacher--Smith, C.1.35, printed pp.138--139; no assertion about a
larger ambient two-core is assumed or proved here.
-/

@[expose] public section
noncomputable section

namespace Representation.SL3ParabolicNatural

/-- An additive subgroup of two vector copies with the centralizer line
condition has order at most one full vector copy. If both the first-axis
kernel and second projection are nonzero, its order is at most |F|². -/
theorem pair_subgroup_card_le {F V : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Finite V]
    (hsize : Nat.card F ^ 2 ≤ Nat.card V) (W : AddSubgroup (V × V))
    (hline : ∀ x ∈ W, x.2 = 0 → x.1 ≠ 0 →
      ∀ y ∈ W, ∃ a : F, y.2 = a • x.1) :
    Nat.card W ≤ Nat.card V := by
  classical
  let π : W →+ V := {
    toFun w := w.val.2
    map_zero' := rfl
    map_add' _ _ := rfl }
  by_cases hπ : ∀ w : W, w.val.2 = 0
  · apply Nat.card_le_card_of_injective (fun w : W => w.val.1)
    intro x y he
    exact Subtype.ext (Prod.ext he ((hπ x).trans (hπ y).symm))
  by_cases hker : ∀ w : W, w.val.2 = 0 → w.val.1 = 0
  · apply Nat.card_le_card_of_injective π
    intro x y he
    have h2 : x.val.2 = y.val.2 := he
    have h1 := hker (x-y) (sub_eq_zero.mpr h2)
    exact Subtype.ext (Prod.ext (sub_eq_zero.mp h1) h2)
  push Not at hπ hker
  obtain ⟨z,hz⟩ := hπ
  obtain ⟨w,hw2,hw1⟩ := hker
  have hrange : Nat.card π.range ≤ Nat.card F := by
    have hh (r : π.range) : ∃ a : F, r.val = a • w.val.1 := by
      obtain ⟨y,hy⟩ := r.property
      rw [←hy]
      exact hline w w.property hw2 hw1 y y.property
    choose a ha using hh
    apply Nat.card_le_card_of_injective a
    intro x y he
    apply Subtype.ext
    rw [ha x,ha y,he]
  have hkernel : Nat.card π.ker ≤ Nat.card F := by
    have hh (v : π.ker) : ∃ a : F, v.val.val.1 = a • z.val.2 := by
      by_cases hv : v.val.val.1 = 0
      · exact ⟨0,by rw [hv,zero_smul]⟩
      obtain ⟨a,ha⟩ := hline v.val v.val.property v.property hv z z.property
      have ha0 : a ≠ 0 := by
        intro he
        exact hz (by simpa only [he,zero_smul] using ha)
      exact ⟨a⁻¹,by rw [ha,inv_smul_smul₀ ha0]⟩
    choose a ha using hh
    apply Nat.card_le_card_of_injective a
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rw [ha x,ha y,he]
    · exact (show x.val.val.2 = 0 from x.property).trans
        (show y.val.val.2 = 0 from y.property).symm
  have hc := π.ker.index_mul_card
  rw [AddSubgroup.index_ker] at hc
  calc
    Nat.card W = Nat.card π.range * Nat.card π.ker := hc.symm
    _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul hrange hkernel
    _ ≤ Nat.card V := by simpa only [pow_two] using hsize

open Subgroup

/-- The centralizer line condition bounds every abelian subgroup of a
central extension of two dual copies by |F|³ times the kernel order. -/
theorem dual_abelian_subgroup_card_le {F Q : Type*} [Field F] [Finite F]
    [Group Q] [Finite Q]
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hcomm : ∀ w z : Q, (p w).toAdd.2 = 0 → (p w).toAdd.1 ≠ 0 →
      Commute w z → ∃ a : F, (p z).toAdd.2 = a • (p w).toAdd.1)
    (B : Subgroup Q) [IsMulCommutative B] :
    Nat.card B ≤ Nat.card F ^ 3 * Nat.card p.ker := by
  let : Finite (Module.Dual F (Fin 3 → F)) :=
    Finite.of_equiv (Fin 3 → F) dualVectorCoordinates.symm.toEquiv
  let W := (B.map p).toAddSubgroup'
  have hV : Nat.card (Module.Dual F (Fin 3 → F)) = Nat.card F ^ 3 := by
    rw [Module.natCard_eq_pow_finrank (K := F),Subspace.dual_finrank_eq,
      Module.finrank_fin_fun]
  have hW : Nat.card W ≤ Nat.card F ^ 3 := by
    rw [←hV]
    apply pair_subgroup_card_le (F := F) (by
      rw [hV]
      exact Nat.pow_le_pow_right Nat.card_pos (by decide)) W
    intro x hx hx2 hx1 y hy
    obtain ⟨w,hw,he⟩ := hx
    obtain ⟨z,hz,hz'⟩ := hy
    have hwc : Commute w z :=
      congrArg Subtype.val (mul_comm' (⟨w,hw⟩ : B) ⟨z,hz⟩)
    have he' : (p w).toAdd = x := congrArg Multiplicative.toAdd he
    have hz'' : (p z).toAdd = y := congrArg Multiplicative.toAdd hz'
    simpa only [he',hz''] using hcomm w z (he'.symm ▸ hx2) (he'.symm ▸ hx1) hwc
  have hrange : Nat.card (B.map p) ≤ Nat.card F ^ 3 := by
    let e : W ≃ B.map p := {
      toFun x := ⟨Multiplicative.ofAdd x.val,x.property⟩
      invFun x := ⟨x.val.toAdd,x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    exact (Nat.card_congr e).symm ▸ hW
  let f := p.comp B.subtype
  have hf : f.range = B.map p := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have hkernel : Nat.card f.ker ≤ Nat.card p.ker := by
    let j : f.ker → p.ker := fun x => ⟨x.val.val,x.property⟩
    apply Nat.card_le_card_of_injective j
    intro x y he
    have hh : x.val.val = y.val.val := congrArg (fun z : p.ker => (z : Q)) he
    exact Subtype.ext (Subtype.ext hh)
  have hc := f.ker.index_mul_card
  rw [index_ker,hf] at hc
  exact hc ▸ Nat.mul_le_mul hrange hkernel

end Representation.SL3ParabolicNatural
end
