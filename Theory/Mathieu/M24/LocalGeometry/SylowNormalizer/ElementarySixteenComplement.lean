module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.ElementarySixteenComplement.Data
public import Theory.ElementaryAbelian.Basic
import all Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.ElementarySixteenComplement.Data

/-! Every normal self-centralizing elementary sixteen in the prescribed
native M24 Sylow subgroup has an actual complement. Normality is used on
the literal conjugacy classes, and all finite identities refer to the
fixed native permutation enumeration. -/

open Subgroup
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.ElementarySixteenComplement
open OrderEnumeration
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage

private theorem native_ext (x y : candidate)
    (h : ∀ b : Fin 3, x.val.val (testPoint b) = y.val.val (testPoint b)) : x = y := by
  obtain ⟨i, rfl⟩ := element_surjective x
  obtain ⟨j, rfl⟩ := element_surjective y
  apply congrArg element
  apply (Fin.strictMono_iff_lt_succ.mpr key_lt_succ).injective
  have h0 := h 0
  have h1 := h 1
  have h5 := h 2
  simp only [element_apply, testPoint, Matrix.cons_val_zero] at h0
  simp only [element_apply, testPoint, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  simp only [element_apply, testPoint, Matrix.cons_val_two] at h5
  change OrderEnumeration.point i 0 = OrderEnumeration.point j 0 at h0
  change OrderEnumeration.point i 1 = OrderEnumeration.point j 1 at h1
  change OrderEnumeration.point i 5 = OrderEnumeration.point j 5 at h5
  simp only [key, h0, h1, h5]

private theorem native_point (i : Fin 1024) (x : Fin 24) :
    (element i).val.val x = point i x := (element_apply i x).trans (point_spec i x).symm

private theorem class_conjugate (v : Fin 192) :
    element (classTransport v) * element (classRep (classCode v)) *
      (element (classTransport v))⁻¹ = native v := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply native_ext
  intro b
  change (element (classTransport v)).val.val
      ((element (classRep (classCode v))).val.val (testPoint b)) =
    (element (vertexIndex v)).val.val ((element (classTransport v)).val.val (testPoint b))
  simp only [native_point]
  exact (class_transport_check v b).symm

private theorem conjugate_eq (k l : Fin 26) :
    element (conjugate k l) = element (conjugator k l) * element (classRep l) *
      (element (conjugator k l))⁻¹ := by
  apply Eq.symm
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply native_ext
  intro b
  change (element (conjugator k l)).val.val ((element (classRep l)).val.val (testPoint b)) =
    (element (conjugate k l)).val.val ((element (conjugator k l)).val.val (testPoint b))
  simp only [native_point]
  exact (conjugate_check k l b).symm

private theorem class_mem (A : Subgroup candidate) [A.Normal]
    (v : Fin 192) (hv : native v ∈ A) : element (classRep (classCode v)) ∈ A := by
  have hh := (inferInstance : A.Normal).conj_mem (native v) hv
    (element (classTransport v))⁻¹
  rw [← class_conjugate v] at hh
  simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hh

private theorem normal_compatible (A : Subgroup candidate) [A.Normal]
    [IsElementaryAbelian 2 A] (k l : Fin 26)
    (hk : element (classRep k) ∈ A) (hl : element (classRep l) ∈ A) :
    compatible k l = true := by
  have hq : element (conjugate k l) ∈ A := by
    rw [conjugate_eq]
    exact (inferInstance : A.Normal).conj_mem _ hl _
  have hc : element (classRep k) * element (conjugate k l) =
      element (conjugate k l) * element (classRep k) :=
    congrArg Subtype.val (mul_comm (⟨_, hk⟩ : A) ⟨_, hq⟩)
  apply compatible_check
  intro b
  have hh := congrArg (fun x : candidate => x.val.val (testPoint b)) hc
  change (element (classRep k)).val.val ((element (conjugate k l)).val.val (testPoint b)) =
    (element (conjugate k l)).val.val ((element (classRep k)).val.val (testPoint b)) at hh
  simpa only [native_point] using hh

private theorem check_sound (t : CoverTree) (u : List (Fin 26)) (ht : check t u = true)
    (s : Finset (Fin 26)) (hs : ∀ v ∈ s, v ∈ u)
    (hc : ∀ v ∈ s, ∀ w ∈ s, compatible v w = true) :
    ∃ i : Fin 6, ∀ v ∈ s, (coverMask i).testBit v.val = true := by
  induction t generalizing u with
  | covered i => exact ⟨i, fun v hv => List.all_eq_true.mp ht v (hs v hv)⟩
  | branch v l r ihl ihr =>
    have ⟨hl, hr⟩ : check l (u.filter (fun w => w != v)) = true ∧
        check r (u.filter (compatible v)) = true := by
      simpa only [check, Bool.and_eq_true] using ht
    by_cases hv : v ∈ s
    · apply ihr _ hr
      intro w hw
      exact List.mem_filter.mpr ⟨hs w hw, hc v hv w hw⟩
    · apply ihl _ hl
      intro w hw
      exact List.mem_filter.mpr ⟨hs w hw, by
        simpa only [bne_iff_ne] using (show w ≠ v by rintro rfl; exact hv hw)⟩

private theorem normal_elementary_covered (A : Subgroup candidate) [A.Normal]
    [IsElementaryAbelian 2 A] :
    ∃ i : Fin 6, ∀ x ∈ A, ∃ j : Fin 64, element (row i j) = x := by
  classical
  let s := Finset.univ.filter (fun k : Fin 26 => element (classRep k) ∈ A)
  obtain ⟨i, hi⟩ := check_sound certificate (List.finRange 26) certificate_check s
    (by intro k _; exact List.mem_finRange k) (by
      intro k hk l hl
      exact normal_compatible A k l (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2)
  refine ⟨i, ?_⟩
  intro x hx
  obtain ⟨v, rfl⟩ := vertex_of_square x (elemPow_eq_one_of_isElementaryAbelian x hx)
  have hm : classCode v ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, class_mem A v hx⟩
  exact ⟨rowCode i v, congrArg element (row_cover_check i v (hi _ hm))⟩

private theorem large_row_commutes (i : Fin 2) (j k : Fin 64) :
    element (row ⟨4+i.val, by omega⟩ j) * element (row ⟨4+i.val, by omega⟩ k) =
      element (row ⟨4+i.val, by omega⟩ k) * element (row ⟨4+i.val, by omega⟩ j) := by
  apply native_ext
  intro b
  change (element _).val.val ((element _).val.val _) = (element _).val.val ((element _).val.val _)
  simp only [native_point]
  exact large_row_commute i j k b

private theorem complement_mul (i : Fin 4) (j k : Fin 64) :
    element (complement i (complementMul i j k)) =
      element (complement i j) * element (complement i k) := by
  apply native_ext
  intro b
  change (element _).val.val _ = (element _).val.val ((element _).val.val _)
  simp only [native_point]
  exact complement_mul_check i j k b

private theorem complement_inv (i : Fin 4) (j : Fin 64) :
    element (complement i (complementInv i j)) = (element (complement i j))⁻¹ := by
  apply mul_eq_one_iff_eq_inv.mp
  apply native_ext
  intro b
  change (element _).val.val ((element _).val.val _) = testPoint b
  simp only [native_point]
  exact complement_inv_check i j b

private noncomputable def complementGroup (i : Fin 4) : Subgroup candidate where
  carrier := Set.range (fun j : Fin 64 => element (complement i j))
  one_mem' := ⟨0, by
    change element (complement i 0) = 1
    rw [complement_zero]
    exact element_identity⟩
  mul_mem' := by
    rintro _ _ ⟨j, rfl⟩ ⟨k, rfl⟩
    exact ⟨complementMul i j k, complement_mul i j k⟩
  inv_mem' := by
    rintro _ ⟨j, rfl⟩
    exact ⟨complementInv i j, complement_inv i j⟩

private theorem complementGroup_card (i : Fin 4) : Nat.card (complementGroup i) = 64 := by
  let f : Fin 64 → complementGroup i := fun j => ⟨element (complement i j), ⟨j, rfl⟩⟩
  have hf : Function.Bijective f := ⟨fun j k he => complement_injective i
    (element_injective (congrArg Subtype.val he)), by rintro ⟨x, j, rfl⟩; exact ⟨j, rfl⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (Nat.card_fin 64)

/-- Every supplied normal self-centralizing elementary sixteen in the
literal native Sylow subgroup has a complement on that same carrier. -/
public theorem exists_complement_native (A : Subgroup candidate) [A.Normal]
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hself : centralizer (A : Set candidate) ≤ A) :
    ∃ L : Subgroup candidate, A.IsComplement' L := by
  obtain ⟨i, hi⟩ := normal_elementary_covered A
  by_cases hsmall : i.val < 4
  · let j : Fin 4 := ⟨i.val, hsmall⟩
    have hji : j.castSucc.castSucc = i := rfl
    refine ⟨complementGroup j, isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
    · rw [hA, complementGroup_card, candidate_card]
    · apply disjoint_def.mpr
      rintro x hx ⟨k, hk⟩
      change element (complement j k) = x at hk
      obtain ⟨l, hl⟩ := hi x hx
      have he : row j.castSucc.castSucc l = complement j k :=
        element_injective (by rw [hji, hl]; exact hk.symm)
      rw [← hl, ← hji, complement_disjoint_check j l k he]
      exact element_identity
  · let j : Fin 2 := ⟨i.val-4, by omega⟩
    have hji : (⟨4+j.val, by omega⟩ : Fin 6) = i := Fin.ext (by dsimp [j]; omega)
    have hm (k : Fin 64) : element (row i k) ∈ A := by
      apply hself
      intro x hx
      obtain ⟨l, rfl⟩ := hi x hx
      rw [← hji]
      exact large_row_commutes j l k
    let f : Fin 64 → A := fun k => ⟨element (row i k), hm k⟩
    have hf : Function.Injective f := by
      intro k l he
      apply large_row_injective j
      rw [hji]
      exact element_injective (congrArg Subtype.val he)
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_fin, hA] at hh
    omega


private theorem complement_comap {H J : Type*} [Group H] [Group J]
    (e : H ≃* J) (A L : Subgroup J) (h : A.IsComplement' L) :
    (A.comap e.toMonoidHom).IsComplement' (L.comap e.toMonoidHom) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    intro x hx hL
    apply e.injective
    exact (disjoint_def.mp h.disjoint hx hL).trans e.map_one.symm
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨⟨a,l⟩, hal⟩ := h.2 (e x)
    refine ⟨e.symm a, ?_, e.symm l, ?_, ?_⟩
    · change e (e.symm a) ∈ A
      rw [e.apply_symm_apply]
      exact a.property
    · change e (e.symm l) ∈ L
      rw [e.apply_symm_apply]
      exact l.property
    · apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hal

/-- Transport the complement calculation while retaining the actual
supplied subgroup, along an actual equivalence with the native Sylow. -/
public theorem exists_complement_of_equiv {H : Type*} [Group H]
    (e : H ≃* candidate) (A : Subgroup H) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hself : centralizer (A : Set H) ≤ A) :
    ∃ L : Subgroup H, A.IsComplement' L := by
  let B := A.map e.toMonoidHom
  let : B.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hB : Nat.card B = 16 := (card_map_of_injective e.injective).trans hA
  have hselfB : centralizer (B : Set candidate) ≤ B := by
    intro x hx
    refine ⟨e.symm x, hself ?_, e.apply_symm_apply x⟩
    intro a ha
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)
  obtain ⟨L, hL⟩ := exists_complement_native B hB hselfB
  have heA : B.comap e.toMonoidHom = A := by
    ext x
    simp only [B, mem_comap, mem_map_equiv, MulEquiv.coe_toMonoidHom, e.symm_apply_apply]
  refine ⟨L.comap e.toMonoidHom, ?_⟩
  simpa only [heA] using complement_comap e B L hL

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.ElementarySixteenComplement
