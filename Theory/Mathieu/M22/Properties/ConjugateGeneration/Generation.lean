module

public import Theory.Mathieu.M22.Properties.ConjugateGeneration.Certificates
public import Theory.Mathieu.M22.Properties.ConjugateGeneration.EnumerationBridge

/-!
# Subgroup generation from the checked M₂₂ words

Each representative has the two standard generators in the subgroup generated
by its listed conjugates. Fusion and Sylow conjugacy transfer this containment
to every involution. All conjugators remain in the actual M₂₂ subgroup of the
design group; the inner bound uses three, the general bound four.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript pp.15–16.
-/

public section
namespace Sporadic.Mathieu.M22ConjugateGeneration
open Subgroup M22CubicInverters M22ValueBound.Concrete
open scoped Pointwise

@[expose] def Generates (s : m22DesignAut) (n : ℕ) : Prop :=
  ∃ c : Fin n → M22,
    M22ValueBound.Concrete.inner ≤ closure (Set.range fun i => inclusion (c i) * s * (inclusion (c i))⁻¹)

private theorem wordValue_apply {n : ℕ} (f : Fin n → m22DesignAut)
    (F : Fin n → Fin 22 → Fin 22) (hf : ∀ i x, (f i).val x = F i x)
    (w : List (Fin n)) (x : Fin 22) :
    (wordValue f w).val x = wordAction F w x := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change (f j).val ((wordValue f w).val x) = _
    rw [hf, ih]
    rfl

private theorem wordValue_mem {n : ℕ} (f : Fin n → m22DesignAut)
    (w : List (Fin n)) : wordValue f w ∈ closure (Set.range f) := by
  induction w with
  | nil => exact (Subgroup.closure _).one_mem
  | cons j w ih =>
    exact (Subgroup.closure _).mul_mem (subset_closure ⟨j, rfl⟩) ih

private theorem inner_le_of_generators (H : Subgroup m22DesignAut)
    (ha : inclusion m22GeneratorAInM22 ∈ H)
    (hb : inclusion m22GeneratorBInM22 ∈ H) : M22ValueBound.Concrete.inner ≤ H := by
  rw [← M22ValueBound.Concrete.inclusion_range, MonoidHom.range_eq_map, map_le_iff_le_comap,
    ← m22_generators_closure_eq_top, closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

theorem representative_four (k : Fin 3) : Generates (representative k) 4 := by
  refine ⟨conjugator k, ?_⟩
  have hw (j : Fin 2) : wordValue (conjugate k) (generationWord k j) =
      inclusion (letter j.castSucc) := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [wordValue_apply _ _ (conjugate_apply k), generation_word_table]
    exact (letter_apply _ _).symm
  apply inner_le_of_generators
  · exact hw 0 ▸ wordValue_mem (conjugate k) (generationWord k 0)
  · exact hw 1 ▸ wordValue_mem (conjugate k) (generationWord k 1)

theorem representative_three : Generates (representative 0) 3 := by
  refine ⟨fun i => conjugator 0 i.castSucc, ?_⟩
  have hw (j : Fin 2) :
      wordValue (fun i : Fin 3 => conjugate 0 i.castSucc) (innerGenerationWord j) =
        inclusion (letter j.castSucc) := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [wordValue_apply _ _ (fun i x => conjugate_apply 0 i.castSucc x),
      inner_generation_word_table]
    exact (letter_apply _ _).symm
  apply inner_le_of_generators
  · exact hw 0 ▸ wordValue_mem _ (innerGenerationWord 0)
  · exact hw 1 ▸ wordValue_mem _ (innerGenerationWord 1)

theorem inclusion_action (q : m22DesignAut) (x : M22) :
    inclusion (m22DesignAutToAut q x) = q * inclusion x * q⁻¹ := by
  apply Subtype.ext
  exact m22DesignAutToAut_apply_perm q x

/-- Conjugation transports the actual generators, keeping the conjugators in M₂₂. -/
theorem generates_of_conjugate (s q : m22DesignAut) {n : ℕ}
    (h : Generates (q * s * q⁻¹) n) : Generates s n := by
  obtain ⟨c, hc⟩ := h
  let d (i : Fin n) : M22 := m22DesignAutToAut q⁻¹ (c i)
  refine ⟨d, ?_⟩
  let H := closure (Set.range fun i => inclusion (d i) * s * (inclusion (d i))⁻¹)
  let f : m22DesignAut →* m22DesignAut := (MulAut.conj q⁻¹).toMonoidHom
  have he (i : Fin n) :
      f (inclusion (c i) * (q * s * q⁻¹) * (inclusion (c i))⁻¹) =
        inclusion (d i) * s * (inclusion (d i))⁻¹ := by
    simp only [d, inclusion_action, f, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.conj_apply]
    group
  have hle : closure (Set.range fun i =>
      inclusion (c i) * (q * s * q⁻¹) * (inclusion (c i))⁻¹) ≤ H.comap f := by
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change f _ ∈ H
    rw [he]
    exact subset_closure ⟨i, rfl⟩
  intro x hx
  have hx' : q * x * q⁻¹ ∈ M22ValueBound.Concrete.inner := (inferInstance : M22ValueBound.Concrete.inner.Normal).conj_mem x hx q
  have hh := hle (hc hx')
  change f (q * x * q⁻¹) ∈ H at hh
  change x ∈ H
  simpa only [f, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel, mul_inv_cancel,
    one_mul, mul_one, inv_mul_cancel_left, mul_inv_cancel_left] using hh

theorem row_fusion (i : Fin 256) (hi : orderOf (rowElement i) = 2) :
    rowElement i = inclusion (fusionElement i) * representative (fusionClass i) *
      (inclusion (fusionElement i))⁻¹ := by
  rcases row_fusion_cases i with hid | hsquare | hf
  · have he : rowElement i = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro x
      exact (rowElement_apply i x).trans (hid x)
    simp [he] at hi
  · obtain ⟨x, hx⟩ := hsquare
    have hp : rowElement i ^ 2 = 1 := hi ▸ pow_orderOf_eq_one (rowElement i)
    have he := congrArg (fun s : m22DesignAut => s.val x) hp
    change (rowElement i).val ((rowElement i).val x) = x at he
    exact (hx (by simpa only [rowElement_apply] using he)).elim
  · apply (eq_mul_inv_iff_mul_eq).mpr
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (rowElement i).val ((fusionElement i).val x) =
      (fusionElement i).val ((representative (fusionClass i)).val x)
    simpa only [rowElement_apply, fusion_apply, representative_apply] using hf x

private theorem representative_mem_inner_iff (k : Fin 3) :
    representative k ∈ M22ValueBound.Concrete.inner ↔ k = 0 := by
  fin_cases k
  · exact iff_of_true m22GeneratorAInM22.property rfl
  · exact iff_of_false m22OddPairSwap_not_mem_M22 (by decide)
  · have he : (representative 2).val =
        Equiv.swap 0 4 * Equiv.swap 1 2 * Equiv.swap 3 20 * Equiv.swap 5 12 *
        Equiv.swap 6 16 * Equiv.swap 7 17 * Equiv.swap 8 21 * Equiv.swap 9 15 *
        Equiv.swap 10 18 * Equiv.swap 11 19 * Equiv.swap 13 14 := by
      apply Equiv.ext
      intro x
      rw [representative_apply]
      revert x
      decide +kernel
    refine iff_of_false (fun hk => ?_) (by decide)
    have halt := M22_le_alternatingGroup hk
    change (representative 2).val ∈ alternatingGroup (Fin 22) at halt
    rw [he] at halt
    have hsign := Equiv.Perm.mem_alternatingGroup.mp halt
    simp [Equiv.Perm.sign_swap', Fin.ext_iff] at hsign

theorem row_three (i : Fin 256) (hi : orderOf (rowElement i) = 2)
    (hin : rowElement i ∈ M22ValueBound.Concrete.inner) : Generates (rowElement i) 3 := by
  have hf := row_fusion i hi
  have hc : representative (fusionClass i) ∈ M22ValueBound.Concrete.inner := by
    have hh := (inferInstance : M22ValueBound.Concrete.inner.Normal).conj_mem (rowElement i) hin (inclusion (fusionElement i))⁻¹
    simpa only [hf, inv_inv, mul_assoc, inv_mul_cancel, mul_inv_cancel,
      one_mul, mul_one, inv_mul_cancel_left, mul_inv_cancel_left] using hh
  have hk := (representative_mem_inner_iff _).mp hc
  apply generates_of_conjugate _ (inclusion (fusionElement i))⁻¹
  simpa only [hf, hk, inv_inv, mul_assoc, inv_mul_cancel, mul_inv_cancel,
    one_mul, mul_one, inv_mul_cancel_left, mul_inv_cancel_left] using representative_three

theorem row_four (i : Fin 256) (hi : orderOf (rowElement i) = 2) :
    Generates (rowElement i) 4 := by
  apply generates_of_conjugate _ (inclusion (fusionElement i))⁻¹
  simpa only [row_fusion i hi, inv_inv, mul_assoc, inv_mul_cancel, mul_inv_cancel,
    one_mul, mul_one, inv_mul_cancel_left, mul_inv_cancel_left] using representative_four (fusionClass i)

private theorem exists_standard_conjugate (s : m22DesignAut) (hs : orderOf s = 2) :
    ∃ q : m22DesignAut, ∃ i : Fin 256, q * s * q⁻¹ = rowElement i := by
  have hz : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq m22DesignAut Q standardSylow
  have hm : q * s * q⁻¹ ∈ standardSylow := by
    rw [← hq]
    change MulAut.conj q s ∈ (Q : Subgroup m22DesignAut).map (MulAut.conj q).toMonoidHom
    exact mem_map_of_mem _ (hQ (mem_zpowers s))
  obtain ⟨i, hi⟩ := rowSylow_surjective ⟨q * s * q⁻¹, hm⟩
  exact ⟨q, i, ((rowSylow_val i).symm.trans (congrArg Subtype.val hi)).symm⟩

/-- Every inner design involution has three M₂₂-conjugates generating M₂₂. -/
theorem design_three (s : m22DesignAut) (hs : orderOf s = 2) (hin : s ∈ M22ValueBound.Concrete.inner) :
    Generates s 3 := by
  obtain ⟨q, i, hi⟩ := exists_standard_conjugate s hs
  apply generates_of_conjugate s q
  rw [hi]
  apply row_three
  · rw [← hi, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
  · exact hi ▸ (inferInstance : M22ValueBound.Concrete.inner.Normal).conj_mem s hin q

/-- Every design involution has four M₂₂-conjugates whose closure contains M₂₂. -/
theorem design_four (s : m22DesignAut) (hs : orderOf s = 2) : Generates s 4 := by
  obtain ⟨q, i, hi⟩ := exists_standard_conjugate s hs
  apply generates_of_conjugate s q
  rw [hi]
  apply row_four
  rw [← hi, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]

end Sporadic.Mathieu.M22ConjugateGeneration
