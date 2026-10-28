module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Locals
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootOrientation.Signs
/-!
# The two geometric parabolic types of PSL₃

Linear and coefficient actors preserve each conjugacy class of maximal
parabolics. Coordinate reversal followed by inverse transpose exchanges the
two standard parabolics. The classes are distinct over every positive binary
field, including the field of order two: Sylow conjugacy adjusts a putative
parabolic conjugator into the normalizer of UT₃, which is the common Borel.
The distinct coordinate stabilizers would then have to be equal.

The linear calculation factors GL₃ as SL₃ times a diagonal matrix, retaining
the actual central quotient and inner conjugation. These facts supply the
geometric diagram action in `Diagram.lean`.

Source: Aschbacher–Smith F.1.12, printed pp.263–264 (PDF pp.274–275),
and the A₂ matrix conventions of GLS3 §2.7.
-/

@[expose] public section
open scoped MatrixGroups Pointwise
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage Matrix.PSL3.RootPlaneGeometry
namespace Matrix.PSL3.LinearThree.OuterExtensions
variable (F : Type*) [Field F] [Finite F]

private theorem conjugate_overgroups_eq {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (P Q : Subgroup G)
    (hP : (S : Subgroup G) ≤ P) (hQ : (S : Subgroup G) ≤ Q)
    (hN : Subgroup.normalizer (S : Set G) ≤ Q) (g : G)
    (h : P.map (MulAut.conj g).toMonoidHom = Q) : P = Q := by
  have hSg : (g • S : Sylow p G) ≤ Q := by
    change (S : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ Q
    rw [← h]
    exact Subgroup.map_mono hP
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Q ((g • S).subtype hSg) (S.subtype hQ)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hq
  have hn : (q : G) * g ∈ Subgroup.normalizer (S : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hq)
  have hg : g ∈ Q := by
    simpa using Q.mul_mem (Q.inv_mem q.property) (hN hn)
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  exact h.trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Q.le_normalizer hg)).symm

private theorem point_ne_line : pointParabolic F ≠ lineParabolic F := by
  intro h
  have hs := congrArg (Subgroup.comap (projection F)) h
  rw [pointParabolic_comap, lineParabolic_comap] at hs
  let t : SL(3,F) := SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) 1
  have ht : t ∈ lineParabolicSL F := by
    rw [mem_lineParabolicSL_iff]
    simp [t, SpecialLinearGroup.transvection_coe]
  rw [← hs, mem_pointParabolicSL_iff] at ht
  have : (1 : F) = 0 := by simpa [t, SpecialLinearGroup.transvection_coe] using ht.1
  exact one_ne_zero this

/-- The point and line parabolics are not inner-conjugate, also when q = 2. -/
theorem pointParabolic_not_conjugate_line {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (g : PSL(3,F)) :
    (pointParabolic F).map (MulAut.conj g).toMonoidHom ≠ lineParabolic F := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply fun h => point_ne_line F (conjugate_overgroups_eq (unipotentSylow F hn hF)
    (pointParabolic F) (lineParabolic F) ?_ ?_ ?_ g h)
  · exact (unipotent_le_pointLocal F).trans (Subgroup.map_mono (pointLocalSL_le F))
  · exact (unipotent_le_lineLocal F).trans (Subgroup.map_mono (lineLocalSL_le F))
  · change Subgroup.normalizer (unipotent F : Set PSL(3,F)) ≤ _
    rw [normalizer_unipotent F hn hF]
    exact Subgroup.map_mono inf_le_right

private theorem map_eq_of_preserves {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (a : MulAut G) (h : ∀ x ∈ P, a x ∈ P) :
    P.map a.toMonoidHom = P := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩; exact h x hx
  · rw [Subgroup.card_map_of_injective a.injective]

omit [Finite F] in
private theorem linearConjSL_val (g : GL (Fin 3) F) (x : SL(3,F)) :
    (linearConjSL F g x).val = g.val * x.val * (g⁻¹).val :=
  congrArg Units.val (linearConjSL_toGL F g x)

private theorem diagonal_parabolicSL (d : Fin 3 → Fˣ) (b : Bool)
    (x : SL(3,F)) (hx : x ∈ parabolicSL F b) :
    linearConjSL F (diagonalGL d) x ∈ parabolicSL F b := by
  cases b
  · obtain ⟨h0,h1⟩ := (mem_lineParabolicSL_iff F x).mp hx
    rw [show parabolicSL F false = lineParabolicSL F from rfl, mem_lineParabolicSL_iff,
      linearConjSL_val]
    simp [diagonalGL, Matrix.diagonal_mul, Matrix.mul_diagonal, h0,h1]
  · obtain ⟨h1,h2⟩ := (mem_pointParabolicSL_iff F x).mp hx
    rw [show parabolicSL F true = pointParabolicSL F from rfl, mem_pointParabolicSL_iff,
      linearConjSL_val]
    simp [diagonalGL, Matrix.diagonal_mul, Matrix.mul_diagonal, h1,h2]

/-- Diagonal actors fix both standard parabolics. -/
theorem diagonal_map_parabolic (d : Fin 3 → Fˣ) (b : Bool) :
    (parabolic F b).map (linearConj F (diagonalGL d)).toMonoidHom = parabolic F b := by
  apply map_eq_of_preserves
  rw [parabolic_eq_map]
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨_,diagonal_parabolicSL F d b x hx,rfl⟩

/-- Coefficient actors fix both standard parabolics. -/
theorem field_map_parabolic (σ : F ≃+* F) (b : Bool) :
    (parabolic F b).map (fieldAction F σ).toMonoidHom = parabolic F b := by
  apply map_eq_of_preserves
  rw [parabolic_eq_map]
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨SpecialLinearGroup.map σ.toRingHom x, ?_, fieldAction_mk F σ x |>.symm⟩
  cases b
  · obtain ⟨h0,h1⟩ := (mem_lineParabolicSL_iff F x).mp hx
    apply (mem_lineParabolicSL_iff F _).mpr
    simp [h0,h1]
  · obtain ⟨h1,h2⟩ := (mem_pointParabolicSL_iff F x).mp hx
    apply (mem_pointParabolicSL_iff F _).mpr
    simp [h1,h2]

omit [Finite F] in
private theorem linear_factor (g : GL (Fin 3) F) :
    ∃ (x : SL(3,F)) (d : Fin 3 → Fˣ),
      g = SpecialLinearGroup.toGL x * diagonalGL d := by
  let d : Fin 3 → Fˣ := ![GeneralLinearGroup.det g,1,1]
  have hd : GeneralLinearGroup.det (diagonalGL d) = GeneralLinearGroup.det g := by
    apply Units.ext
    change Matrix.det (Matrix.diagonal (fun i => (d i).val)) = _
    simp [Matrix.det_diagonal, Fin.prod_univ_three, d]
  have hk : g * (diagonalGL d)⁻¹ ∈ (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker := by
    change GeneralLinearGroup.det _ = 1
    rw [map_mul, map_inv, hd, mul_inv_cancel]
  refine ⟨(slEquivDetKernel F).symm ⟨_,hk⟩, d, ?_⟩
  rw [slEquivDetKernel_symm_toGL]
  simp

/-- Every linear actor carries each parabolic to an actual inner conjugate. -/
theorem linear_map_parabolic (g : GL (Fin 3) F) (b : Bool) :
    ∃ x : PSL(3,F), (parabolic F b).map (linearConj F g).toMonoidHom =
      (parabolic F b).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x,d,rfl⟩ := linear_factor F g
  refine ⟨projection F x, ?_⟩
  rw [map_mul, linearConj_toGL]
  change (parabolic F b).map ((MulAut.conj (projection F x)).toMonoidHom.comp
    (linearConj F (diagonalGL d)).toMonoidHom) = _
  rw [← Subgroup.map_map, diagonal_map_parabolic]

omit [Finite F] in
private theorem oppositionSL_val (x : SL(3,F)) (i j : Fin 3) :
    (linearConjSL F (reversalGL F) (graphSL F x)).val i j = x⁻¹.val j.rev i.rev := by
  rw [linearConjSL_val]
  have hgraph : (graphSL F x).val = x⁻¹.val.transpose := by
    change (Matrix.adjugate x.val.transpose) = (Matrix.adjugate x.val).transpose
    exact (Matrix.adjugate_transpose x.val).symm
  rw [hgraph]
  fin_cases i <;> fin_cases j <;>
    simp [reversalGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.rev]

private theorem opposition_mem (x : SL(3,F)) (b : Bool)
    (hx : x ∈ parabolicSL F b) :
    linearConjSL F (reversalGL F) (graphSL F x) ∈ parabolicSL F (!b) := by
  have hi := (parabolicSL F b).inv_mem hx
  cases b
  · obtain ⟨h0,h1⟩ := (mem_lineParabolicSL_iff F x⁻¹).mp hi
    apply (mem_pointParabolicSL_iff F _).mpr
    simp only [oppositionSL_val]
    exact ⟨h1,h0⟩
  · obtain ⟨h1,h2⟩ := (mem_pointParabolicSL_iff F x⁻¹).mp hi
    apply (mem_lineParabolicSL_iff F _).mpr
    simp only [oppositionSL_val]
    exact ⟨h2,h1⟩

/-- The Borel-preserving graph representative exchanges the two diagram types. -/
theorem oppositionGraph_map_parabolic (b : Bool) :
    (parabolic F b).map (oppositionGraph F).toMonoidHom = parabolic F (!b) := by
  have hf (b : Bool) : ∀ x ∈ parabolic F b,
      oppositionGraph F x ∈ parabolic F (!b) := by
    rw [parabolic_eq_map, parabolic_eq_map]
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨_,opposition_mem F x b hx,rfl⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩; exact hf b x hx
  · intro x hx
    refine ⟨oppositionGraph F x, ?_, ?_⟩
    · simpa using hf (!b) x hx
    · exact congrArg (fun a : MulAut PSL(3,F) => a x) (oppositionGraph_sq (F:=F))
end Matrix.PSL3.LinearThree.OuterExtensions
