module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm.BorelKernel

/-!
# The linear factor on the actual SL₃ and PSL₃ Borel quotients

A GL₃ matrix preserving the projective upper unipotent group is upper triangular.
Its conjugate of a diagonal matrix factors as a unipotent matrix times the same
diagonal matrix: compare the nonzero diagonal entries in m d = (m d m⁻¹) m.
The actual Borel quotient maps therefore kill the entire linear factor,
including diagonal automorphisms. The PSL₃ map retains the cubic scalar quotient.
Source: the matrix actions in GLS3 §2.7 and Aschbacher–Smith 13.8.20, printed p.954.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.NormalizerForm
namespace Matrix.PSL3.CartanActions.SixCommutators
variable (F : Type*) [Field F] [CharP F 2]

private theorem map_inv_stable {G : Type*} [Group G] (U : Subgroup G) (α : MulAut G)
    (h : U.map α.toMonoidHom = U) : U.map α⁻¹.toMonoidHom = U := by
  conv_lhs => rw [← h]
  rw [Subgroup.map_map]
  have he : α⁻¹.toMonoidHom.comp α.toMonoidHom = MonoidHom.id G := by
    ext x
    exact α.symm_apply_apply x
  rw [he, Subgroup.map_id]

theorem linearConjSL_unipotent (m : GL (Fin 3) F)
    (h : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F) :
    (unipotentSL F).map (linearConjSL F m).toMonoidHom = unipotentSL F := by
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    exact linearConjSL_mem_unipotent F m u hu
      (h.le (mem_map_of_mem _ (mem_map_of_mem (projection F) hu)))
  · intro u hu
    have hi : (unipotent F).map (linearConj F m⁻¹).toMonoidHom = unipotent F := by
      rw [map_inv]
      exact map_inv_stable _ _ h
    refine ⟨linearConjSL F m⁻¹ u, ?_, ?_⟩
    · exact linearConjSL_mem_unipotent F m⁻¹ u hu
        (hi.le (mem_map_of_mem _ (mem_map_of_mem (projection F) hu)))
    · rw [map_inv]
      exact (linearConjSL F m).apply_symm_apply u

variable [Finite F]

theorem linearConjSL_borel (m : GL (Fin 3) F)
    (h : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F) :
    (borelSL F).map (linearConjSL F m).toMonoidHom = borelSL F := by
  rw [← normalizer_unipotentSL, map_equiv_normalizer_eq, linearConjSL_unipotent F m h]

theorem linearConjSL_torus_factor (m : GL (Fin 3) F)
    (h : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (d : Fˣ × Fˣ) : ∃ u ∈ unipotentSL F,
    linearConjSL F m (torusSL F d) = u * torusSL F d := by
  let v := linearConjSL F m (torusSL F d)
  have hv : v ∈ borelSL F :=
    (linearConjSL_borel F m h).le (mem_map_of_mem _ (torusSL_mem_borel F d))
  obtain ⟨e,u,hu,he⟩ := borelSL_factorization F v hv
  have hm := linearConj_upperTriangular F m h
  have hv' := (mem_borelSL_iff F v).mp hv
  have hn : Matrix.det m.val ≠ 0 := (GeneralLinearGroup.det m).ne_zero
  rw [Matrix.det_fin_three] at hn
  simp only [hm.1,hm.2.1,hm.2.2,mul_zero,zero_mul,sub_zero,add_zero] at hn
  have h00 : m.val 0 0 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  have h22 : m.val 2 2 ≠ 0 := (mul_ne_zero_iff.mp hn).2
  have heq : m.val * (torusSL F d).val = v.val * m.val := by
    have hl := congrArg Units.val (linearConjSL_toGL F m (torusSL F d))
    change v.val = m.val * (torusSL F d).val * m.inv at hl
    rw [hl, Matrix.mul_assoc, m.inv_val, mul_one]
  have h0 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 0) heq
  have h2 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 2) heq
  simp [Matrix.mul_apply, Fin.sum_univ_three, torusSL_val,hm.1,hm.2.1] at h0
  simp [Matrix.mul_apply, Fin.sum_univ_three, torusSL_val,hv'.2.1,hv'.2.2] at h2
  have hu00 := ((mem_pointLocalSL_iff F u).mp hu.1).1
  have hu22 := ((mem_lineLocalSL_iff F u).mp hu.2).2.2
  rw [he] at h0 h2
  simp only [SpecialLinearGroup.coe_mul, torusSL_val, Matrix.mul_diagonal,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_two, hu00,hu22,one_mul] at h0 h2
  have hed : e = d := Prod.ext
    (Units.ext (mul_right_cancel₀ h00 (by simpa [mul_comm] using h0.symm)))
    (Units.ext (mul_right_cancel₀ h22 (by simpa [mul_comm] using h2.symm)))
  refine ⟨u,hu,?_⟩
  simpa only [hed] using he

noncomputable def specialQuotientMap (hF : Nat.card F = 2 ^ 6) :
    borelSL F →* (Fˣ × Fˣ) :=
  (quotientSLTorusEquiv F hF).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (borelSL F)))

noncomputable def projectiveQuotientMap (hF : Nat.card F = 2 ^ 6) :
    borel F →* ((Fˣ × Fˣ) ⧸ cubicScalars F) :=
  (quotientTorusEquiv F hF).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (borel F)))

omit [CharP F 2] in
theorem specialQuotientMap_torus (hF : Nat.card F = 2 ^ 6) (d : Fˣ × Fˣ) :
    specialQuotientMap F hF ⟨torusSL F d,torusSL_mem_borel F d⟩ = d :=
  quotientSLTorusEquiv_mk_torus F hF d

omit [CharP F 2] in
theorem projectiveQuotientMap_torus (hF : Nat.card F = 2 ^ 6) (d : Fˣ × Fˣ) :
    projectiveQuotientMap F hF ⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩ =
      QuotientGroup.mk d := quotientTorusEquiv_mk_torus F hF d

omit [CharP F 2] in
theorem specialQuotientMap_unipotent (hF : Nat.card F = 2 ^ 6)
    (u : SL(3,F)) (hu : u ∈ unipotentSL F) :
    specialQuotientMap F hF ⟨u,unipotentSL_le_borelSL F hu⟩ = 1 := by
  change quotientSLTorusEquiv F hF (QuotientGroup.mk _) = 1
  rw [(QuotientGroup.eq_one_iff _).mpr (by rw [twoCoreSL_eq F hF]; exact hu),map_one]

omit [CharP F 2] in
theorem projectiveQuotientMap_unipotent (hF : Nat.card F = 2 ^ 6)
    (u : PSL(3,F)) (hu : u ∈ unipotent F) :
    projectiveQuotientMap F hF ⟨u,unipotent_le_borel F hu⟩ = 1 := by
  change quotientTorusEquiv F hF (QuotientGroup.mk _) = 1
  rw [(QuotientGroup.eq_one_iff _).mpr (by rw [twoCore_eq F hF]; exact hu),map_one]

theorem specialQuotientMap_linear_torus (hF : Nat.card F = 2 ^ 6)
    (m : GL (Fin 3) F)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (d : Fˣ × Fˣ) (hb : linearConjSL F m (torusSL F d) ∈ borelSL F) :
    specialQuotientMap F hF ⟨linearConjSL F m (torusSL F d),hb⟩ = d := by
  obtain ⟨u,hu,he⟩ := linearConjSL_torus_factor F m hm d
  have he' : (⟨linearConjSL F m (torusSL F d),hb⟩ : borelSL F) =
      ⟨u,unipotentSL_le_borelSL F hu⟩ * ⟨torusSL F d,torusSL_mem_borel F d⟩ :=
    Subtype.ext he
  rw [he',map_mul,specialQuotientMap_unipotent F hF u hu,specialQuotientMap_torus,one_mul]

theorem projectiveQuotientMap_linear_torus (hF : Nat.card F = 2 ^ 6)
    (m : GL (Fin 3) F)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (d : Fˣ × Fˣ) (hb : linearConj F m (torusMap F d) ∈ borel F) :
    projectiveQuotientMap F hF ⟨linearConj F m (torusMap F d),hb⟩ =
      QuotientGroup.mk d := by
  obtain ⟨u,hu,he⟩ := linearConjSL_torus_factor F m hm d
  have he' : (⟨linearConj F m (torusMap F d),hb⟩ : borel F) =
      ⟨projection F u,unipotent_le_borel F (mem_map_of_mem _ hu)⟩ *
        ⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩ := by
    apply Subtype.ext
    change projection F (linearConjSL F m (torusSL F d)) = _
    rw [he,map_mul]
    rfl
  rw [he',map_mul,projectiveQuotientMap_unipotent F hF _ (mem_map_of_mem _ hu),projectiveQuotientMap_torus,one_mul]

end Matrix.PSL3.CartanActions.SixCommutators
