module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Reduction

/-!
# Explicit involutions in the source quaternion core

Choose one noncentral representative on each of the three axes of the first
quaternion factor, and all six noncentral elements of the second. Their
eighteen products are distinct involutions: both squares are the shared
central involution, and equality of products identifies the first coordinates
modulo the common center. A small calculation in Q₈ distinguishes those
three representatives. This is a lower bound, not an assumed census.

The actual factor embeddings supplied by `Hypotheses.quaternionCentralProduct`
therefore rule out a thirteen-element class containing every core involution.
Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, with the quaternion structure of Section 2.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.Marking
private abbrev Q8 := QuaternionGroup 2
private def representatives : Fin 3 → Q8 :=
  ![QuaternionGroup.a 1, QuaternionGroup.xa 0, QuaternionGroup.xa 1]

private theorem representative_square : ∀ i, (representatives i) ^ 2 ≠ 1 := by decide
private theorem representatives_distinct_mod_center : ∀ i j,
    (representatives j)⁻¹ * representatives i ∈ center Q8 → i = j := by decide
private theorem representatives_noncentral : ∀ i, representatives i ∉ center Q8 := by decide

private theorem central_product_involution_lower_bound {Q : Type*} [Group Q] [Finite Q]
    (d : QuaternionCentralProductData Q) : 18 ≤ Nat.card {q : Q // orderOf q = 2} := by
  classical
  obtain ⟨eB⟩ := d.left_model
  obtain ⟨eC⟩ := d.right_model
  let U := {c : Q8 // c ^ 2 ≠ 1}
  let b : Fin 3 → d.left := fun i => eB.symm (representatives i)
  let c : U → d.right := fun u => eC.symm u.val
  have hb (i) : (b i : Q) ^ 2 ≠ 1 := by
    intro hi
    apply representative_square i
    have ht : b i ^ 2 = 1 := Subtype.ext hi
    simpa [b] using congrArg eB ht
  have hc (u : U) : (c u : Q) ^ 2 ≠ 1 := by
    intro hi
    apply u.property
    have ht : c u ^ 2 = 1 := Subtype.ext hi
    simpa [c] using congrArg eC ht
  have square_eq (i) (u) : (b i : Q) ^ 2 = (c u : Q) ^ 2 := by
    obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp d.center_card
    let v : center Q := ⟨(b i : Q) ^ 2, d.square_mem_center _⟩
    let v' : center Q := ⟨(c u : Q) ^ 2, d.square_mem_center _⟩
    exact congrArg Subtype.val ((hw v (fun he => hb i (congrArg Subtype.val he))).trans
      (hw v' (fun he => hc u (congrArg Subtype.val he))).symm)
  have map_center (w : d.left) (hw : (w : Q) ∈ center Q) : eB w ∈ center Q8 := by
    apply mem_center_iff.mpr
    intro y
    have ht := congrArg eB (show eB.symm y * w = w * eB.symm y from
      Subtype.ext (mem_center_iff.mp hw (eB.symm y : Q)))
    simpa only [map_mul, eB.apply_symm_apply] using ht
  let f : Fin 3 × U → {q : Q // orderOf q = 2} := fun p =>
    ⟨(b p.1 : Q) * c p.2, orderOf_eq_prime (by
      rw [(show Commute (b p.1 : Q) (c p.2 : Q) from
        d.commute _ (b p.1).property _ (c p.2).property).mul_pow, square_eq p.1 p.2,
        ← pow_two]
      exact congrArg Subtype.val (d.center_square
        ⟨(c p.2 : Q) ^ 2, d.square_mem_center _⟩)) (by
      intro he
      have ht : (b p.1 : Q) ∈ d.right :=
        (eq_inv_of_mul_eq_one_left he).symm ▸ d.right.inv_mem (c p.2).property
      have hz : (b p.1 : Q) ∈ center Q := d.center_eq.symm ▸ ⟨(b p.1).property, ht⟩
      have hn := map_center (b p.1) hz
      exact representatives_noncentral p.1 (by simpa [b] using hn))⟩
  have hf : Function.Injective f := by
    rintro ⟨i,u⟩ ⟨j,v⟩ he
    have he' : (b i : Q) * c u = (b j : Q) * c v := congrArg Subtype.val he
    have hd : (b j : Q)⁻¹ * b i = (c v : Q) * (c u : Q)⁻¹ := by
      calc
        _ = (b j : Q)⁻¹ * ((b i : Q) * c u) * (c u : Q)⁻¹ := by group
        _ = _ := by rw [he']; group
    have hw : ((b j)⁻¹ * b i : d.left) ∈ center d.left := by
      have hQ : (b j : Q)⁻¹ * b i ∈ center Q := by
        rw [d.center_eq]
        exact ⟨d.left.mul_mem (d.left.inv_mem (b j).property) (b i).property,
          hd.symm ▸ d.right.mul_mem (c v).property (d.right.inv_mem (c u).property)⟩
      exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hQ y)
    have hi : i = j := by
      apply representatives_distinct_mod_center
      apply mem_center_iff.mpr
      intro y
      have ht := congrArg eB (mem_center_iff.mp hw (eB.symm y))
      simpa [b] using ht
    subst j
    have hu : u = v := by
      apply Subtype.ext
      have ht : c u = c v := Subtype.ext (mul_left_cancel he')
      simpa [c] using congrArg eC ht
    subst v
    rfl
  have hcount : Nat.card (Fin 3 × U) = 18 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hcount ▸ Nat.card_le_card_of_injective f hf

/-- The actual source core contains at least eighteen involutions. -/
public theorem core_involution_lower_bound {G : Type*} [Group G] [Finite G] {z : G}
    (h : Hypotheses z) : 18 ≤ Nat.card {q : Core z // orderOf q = 2} := by
  obtain ⟨d⟩ := h.quaternionCentralProduct
  exact central_product_involution_lower_bound d

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.Marking
