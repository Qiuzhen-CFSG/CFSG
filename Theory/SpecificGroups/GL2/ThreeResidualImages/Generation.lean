module

public import Theory.SpecificGroups.GL2.ThreeResidualImages.Basic

/-!
# Two cubic subgroups generate SL₂(3)

Conjugate one nonidentity cubic matrix to the upper unipotent. A short
kernel-checked calculation writes every determinant-one matrix as four
alternating powers of that unipotent and any cubic matrix outside its cyclic
subgroup. Transporting those words back retains the actual embedded join.
Only matrices and words are enumerated, never the subgroup lattice.

Source application: Aschbacher–Smith, F.6.16, printed pp.308–309.
-/

public section
open Matrix Subgroup
namespace Matrix.GeneralLinearGroup
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)

private theorem matrix_unipotent_words : ∀ B : M, B ^ 3 = 1 →
    B ≠ 1 → B ≠ threeUnipotent.val → B ≠ threeUnipotent.val ^ 2 →
    ∀ C : M, C.det = 1 → ∃ i j k l : Fin 3,
      C = threeUnipotent.val ^ i.val * B ^ j.val *
        threeUnipotent.val ^ k.val * B ^ l.val := by
  decide +kernel

private theorem cubic_conjugate_unipotent (x : (GL (Fin 2) (ZMod 3))) (hx : x ^ 3 = 1) (hne : x ≠ 1) :
    ∃ g : (GL (Fin 2) (ZMod 3)), (MulAut.conj g) x = threeUnipotent := by
  obtain ⟨i, hi, _⟩ := three_conjugacy_data.1 x
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have ho : ![1,2,4,3,6,2,8,8] i = 3 := by
    rw [← three_conjugacy_data.2.1 i, ← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans (orderOf_eq_prime hx hne)
  have hi3 : i = 3 := by fin_cases i <;> first | rfl | norm_num at ho
  exact ⟨g, by change g * x * g⁻¹ = threeUnipotent; simpa [hi3, threeClassRepr] using hg⟩

/-- Independent nonidentity cubic matrices generate the determinant kernel. -/
theorem three_cubic_pair_generate (K : Subgroup (GL (Fin 2) (ZMod 3))) (x y : (GL (Fin 2) (ZMod 3)))
    (hxK : x ∈ K) (hyK : y ∈ K) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x) (hyx2 : y ≠ x ^ 2) :
    threeSpecialLinear ≤ K := by
  obtain ⟨g, he⟩ := cubic_conjugate_unipotent x hx hx1
  let e := MulAut.conj g
  let J := K.map e.toMonoidHom
  have huJ : threeUnipotent ∈ J := he ▸ mem_map_of_mem e.toMonoidHom hxK
  have hyJ : e y ∈ J := mem_map_of_mem e.toMonoidHom hyK
  have hB3 : (e y).val ^ 3 = 1 := by
    have h : (e y) ^ 3 = 1 := by rw [← map_pow, hy, map_one]
    exact congrArg Units.val h
  have hB1 : (e y).val ≠ 1 := by
    intro h
    exact hy1 (e.injective (by simpa only [map_one] using Units.ext h))
  have hBx : (e y).val ≠ threeUnipotent.val := by
    intro h
    exact hyx (e.injective ((Units.ext h).trans he.symm))
  have hBx2 : (e y).val ≠ threeUnipotent.val ^ 2 := by
    intro h
    apply hyx2
    apply e.injective
    rw [map_pow, he]
    exact Units.ext h
  have hSJ : threeSpecialLinear ≤ J := by
    intro z hz
    obtain ⟨i,j,k,l,hword⟩ := matrix_unipotent_words (e y).val hB3 hB1 hBx hBx2
      z.val ((three_mem_specialLinear z).mp hz)
    have heq : z = threeUnipotent ^ i.val * e y ^ j.val *
        threeUnipotent ^ k.val * e y ^ l.val := Units.ext hword
    rw [heq]
    exact J.mul_mem (J.mul_mem (J.mul_mem (J.pow_mem huJ _) (J.pow_mem hyJ _))
      (J.pow_mem huJ _)) (J.pow_mem hyJ _)
  have hES : ∀ z ∈ threeSpecialLinear, e z ∈ threeSpecialLinear := by
    intro z hz
    exact (inferInstance : threeSpecialLinear.Normal).conj_mem z hz g
  intro z hz
  obtain ⟨w, hw, hew⟩ := hSJ (hES z hz)
  exact e.injective hew ▸ hw

private theorem exists_cubic_generator (C : Subgroup (GL (Fin 2) (ZMod 3))) (hC : Nat.card C = 3) :
    ∃ x : (GL (Fin 2) (ZMod 3)), x ≠ 1 ∧ x ^ 3 = 1 ∧ C = zpowers x := by
  let _ : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : C)
  have hx1 : x.val ≠ 1 := fun h => hx (Subtype.ext h)
  have hx3 : x.val ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := x)
    rw [hC] at h
    exact congrArg Subtype.val h
  refine ⟨x.val, hx1, hx3, ?_⟩
  exact (eq_of_le_of_card_ge (zpowers_le.mpr x.property)
    (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, hC])).symm

/-- Every subgroup of order three lies in the determinant kernel. -/
theorem three_card_three_le_specialLinear (C : Subgroup (GL (Fin 2) (ZMod 3))) (hC : Nat.card C = 3) :
    C ≤ threeSpecialLinear := by
  intro x hx
  apply three_cubic_mem_specialLinear
  have h := pow_card_eq_one' (x := (⟨x,hx⟩ : C))
  rw [hC] at h
  exact congrArg Subtype.val h

/-- The literal join of two distinct order-three subgroups is SL₂(3). -/
theorem three_distinct_cubic_join (C D : Subgroup (GL (Fin 2) (ZMod 3)))
    (hC : Nat.card C = 3) (hD : Nat.card D = 3) (hne : C ≠ D) :
    C ⊔ D = threeSpecialLinear := by
  obtain ⟨x, hx1, hx3, hxC⟩ := exists_cubic_generator C hC
  obtain ⟨y, hy1, hy3, hyD⟩ := exists_cubic_generator D hD
  have hxmem : x ∈ C := hxC ▸ mem_zpowers x
  have hymem : y ∈ D := hyD ▸ mem_zpowers y
  have hynot : y ∉ C := by
    intro hy
    have hDC : D ≤ C := by rw [hyD]; exact zpowers_le.mpr hy
    exact hne (eq_of_le_of_card_ge hDC (by omega)).symm
  apply le_antisymm (sup_le (three_card_three_le_specialLinear C hC)
    (three_card_three_le_specialLinear D hD))
  exact three_cubic_pair_generate (C ⊔ D) x y
    (mem_sup_left hxmem) (mem_sup_right hymem) hx3 hy3 hx1 hy1
    (fun h => hynot (h ▸ hxmem)) (fun h => hynot (h ▸ C.pow_mem hxmem 2))

end Matrix.GeneralLinearGroup
