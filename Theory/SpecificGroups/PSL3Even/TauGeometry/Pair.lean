module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.DiagramLocals

/-!
# Action on the two actual PSL₃ local factors

An automorphism stabilizing the standard unitriangular Sylow subgroup has
upper triangular linear part in its linear–field–graph expression. Triangular
conjugation and field automorphisms preserve both vector/covector stabilizers;
the opposition graph automorphism exchanges them. The calculation includes
fields of orders two and four and uses the actual projective matrix actions.

Source: Aschbacher–Smith, E.1.14(1), printed p.214, and F.1.12(I)(1),
printed pp.263–264; standard automorphism coverage is GLS3, §2.5 and §2.7.
-/

@[expose] public section
open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3 Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.ExtensionBorel
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
namespace Matrix.PSL3Even.TauGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem linearConjSL_val (g : GL (Fin 3) F) (x : SL(3,F)) :
    (linearConjSL F g x).val = g.val * x.val * (g⁻¹).val :=
  congrArg Units.val (linearConjSL_toGL F g x)

omit [Finite F] [CharP F 2] in
private theorem triangular_mem_local (g : GL (Fin 3) F) (hg : g ∈ glBorel F)
    (b : Bool) (x : SL(3,F)) (hx : x ∈ localSL F b) :
    linearConjSL F g x ∈ localSL F b := by
  obtain ⟨g10,g20,g21⟩ := hg
  obtain ⟨i10,i20,i21⟩ := (glBorel F).inv_mem ⟨g10,g20,g21⟩
  have h00 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 0) g.val_inv
  have h22 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 2) g.val_inv
  change (g.val * (g⁻¹).val) 0 0 = 1 at h00
  change (g.val * (g⁻¹).val) 2 2 = 1 at h22
  simp only [Matrix.mul_apply, Fin.sum_univ_three,
    i10,i20,g20,g21,mul_zero,zero_mul,add_zero,zero_add] at h00 h22
  cases b
  · obtain ⟨x20,x21,x22⟩ := (mem_lineLocalSL_iff F x).mp hx
    apply (mem_lineLocalSL_iff F _).mpr
    rw [linearConjSL_val]
    simp [-Matrix.coe_units_inv, Matrix.mul_apply, Fin.sum_univ_three,
      g20,g21,i20,i21,x20,x21,x22,h22]
  · obtain ⟨x00,x10,x20⟩ := (mem_pointLocalSL_iff F x).mp hx
    apply (mem_pointLocalSL_iff F _).mpr
    rw [linearConjSL_val]
    simp [-Matrix.coe_units_inv, Matrix.mul_apply, Fin.sum_univ_three,
      g10,g20,i10,i20,x00,x10,x20,h00]

omit [Finite F] [CharP F 2] in
theorem triangular_map_local (g : GL (Fin 3) F) (hg : g ∈ glBorel F) (b : Bool) :
    (localFactor F b).map (linearConj F g).toMonoidHom = localFactor F b := by
  have hf (g : GL (Fin 3) F) (hg : g ∈ glBorel F) :
      ∀ x ∈ localFactor F b, linearConj F g x ∈ localFactor F b := by
    have he : localFactor F b = (localSL F b).map (projection F) := by cases b <;> rfl
    rw [he]
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨_, triangular_mem_local F g hg b x hx, rfl⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩; exact hf g hg x hx
  · intro x hx
    refine ⟨linearConj F g⁻¹ x, hf g⁻¹ ((glBorel F).inv_mem hg) x hx, ?_⟩
    change (linearConj F g * linearConj F g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

omit [Finite F] [CharP F 2] in
private theorem oppositionSL_val (x : SL(3,F)) (i j : Fin 3) :
    (linearConjSL F (reversalGL F) (graphSL F x)).val i j = x⁻¹.val j.rev i.rev := by
  rw [linearConjSL_val]
  have hgraph : (graphSL F x).val = x⁻¹.val.transpose := by
    change (Matrix.adjugate x.val.transpose) = (Matrix.adjugate x.val).transpose
    exact (Matrix.adjugate_transpose x.val).symm
  rw [hgraph]
  fin_cases i <;> fin_cases j <;>
    simp [reversalGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.rev]

omit [Finite F] [CharP F 2] in
theorem opposition_map_local (b : Bool) :
    (localFactor F b).map (OddPrimeCoverage.oppositionGraph F).toMonoidHom =
      localFactor F (!b) := by
  have hf (b : Bool) : ∀ x ∈ localFactor F b,
      OddPrimeCoverage.oppositionGraph F x ∈ localFactor F (!b) := by
    have he (b : Bool) : localFactor F b = (localSL F b).map (projection F) := by
      cases b <;> rfl
    rw [he, he]
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨linearConjSL F (reversalGL F) (graphSL F x), ?_, rfl⟩
    have hd : linearConjSL F (reversalGL F) (graphSL F x) = flagDuality F x := by
      apply Subtype.ext
      ext i j
      exact oppositionSL_val F x i j
    rw [hd]
    cases b
    · exact flagDuality_line_mem F ⟨x,hx⟩
    · exact flagDuality_point_mem F ⟨x,hx⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩; exact hf b x hx
  · intro x hx
    refine ⟨OddPrimeCoverage.oppositionGraph F x, ?_, ?_⟩
    · simpa using hf (!b) x hx
    · exact congrArg (fun a : MulAut PSL(3,F) => a x)
        (OddPrimeCoverage.oppositionGraph_sq (F := F))

theorem local_pair_of_unipotent_stable {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (α : MulAut PSL(3,F)) (hα : (unipotent F).map α.toMonoidHom = unipotent F) :
    (∀ b, (localFactor F b).map α.toMonoidHom = localFactor F b) ∨
      (∀ b, (localFactor F b).map α.toMonoidHom = localFactor F (!b)) := by
  have hstd : α ∈ standard F := by rw [standard_eq_top_of_two_power_card F hf hF]; trivial
  obtain ⟨g,σ,he | he⟩ := ResidualLinear.standard_opposition_factorization α hstd
  · rw [he] at hα ⊢
    have hg := ResidualLinear.linear_field_upperTriangular g σ hα
    left
    intro b
    change (localFactor F b).map ((linearConj F g).toMonoidHom.comp
      (fieldAction F σ).toMonoidHom) = _
    rw [← Subgroup.map_map, field_preserves, triangular_map_local F g hg]
  · rw [he] at hα ⊢
    change (unipotent F).map (((linearConj F g * fieldAction F σ).toMonoidHom).comp
      (OddPrimeCoverage.oppositionGraph F).toMonoidHom) = _ at hα
    rw [← Subgroup.map_map, oppositionGraph_unipotent] at hα
    have hg := ResidualLinear.linear_field_upperTriangular g σ hα
    right
    intro b
    change (localFactor F b).map ((linearConj F g).toMonoidHom.comp
      ((fieldAction F σ).toMonoidHom.comp
        (OddPrimeCoverage.oppositionGraph F).toMonoidHom)) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, opposition_map_local,
      field_preserves, triangular_map_local F g hg]

end Matrix.PSL3Even.TauGeometry
