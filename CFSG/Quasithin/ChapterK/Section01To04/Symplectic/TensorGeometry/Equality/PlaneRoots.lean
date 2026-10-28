module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Plane
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Placement
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFamily

/-!
# Root intersections in the symplectic tensor plane radical

The roots through the vectors (1,x) are literal Levi conjugates of root 0;
root 2 supplies the remaining coordinate line. Nonzero elements on the
coordinate lines, the diagonal, and a line moved by the coefficient twist
force the three lower/off-diagonal blocks of a fixed tensor matrix to vanish.
The calculation retains arbitrary nonzero root parameters.

A root has order |F| in an elementary radical of order |F|³. Thus a subgroup
of binary rank greater than twice the field exponent meets each required
root. Its tensor fixed space is the actual plane tensor plane, of dimension
four over F. No natural-plus-graph fixed-space calculation is used here.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

@[expose] public section
open scoped Matrix TensorProduct
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

noncomputable def lineShear (x t : F) : Plane.symmetricMatrices F :=
  ⟨!![t,t*x;t*x,t*x^2], by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩

noncomputable def infinityShear (t : F) : Plane.symmetricMatrices F :=
  ⟨!![0,0;0,t], by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩

noncomputable def lineLevi (x : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1,0;x,1], by simp [Matrix.det_fin_two]⟩

lemma lineShear_conjugate (x t : F) :
    (MulAut.conj (Plane.leviSp (lineLevi x))) (rootElement 0 t) =
      Plane.shearSp (lineShear x t) := by
  have he : rootElement 0 t = Plane.shearSp (lineShear 0 t) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootElement,rootMatrix,Plane.shearSp,lineShear,fromBlocks,Matrix.single]
  rw [he, conjugate_levi_shear]
  congr 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Plane.congruence,lineLevi,lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,pow_two,mul_assoc,mul_comm] <;> ring

noncomputable def lineRoot (x : F) : Subgroup (Sp F) :=
  (RootSubgroup.group 0).map (MulAut.conj (Plane.leviSp (lineLevi x))).toMonoidHom

lemma mem_lineRoot (x : F) (g : Sp F) :
    g ∈ lineRoot x ↔ ∃ t : F, Plane.shearSp (lineShear x t) = g := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 0 g).mp hg
    exact ⟨t, (lineShear_conjugate x t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨rootElement 0 t, (RootSubgroup.mem_group_iff 0 _).mpr ⟨t, rfl⟩,
      lineShear_conjugate x t⟩

lemma lineRoot_le_plane (x : F) : lineRoot (F := F) x ≤ planeRadical := by
  intro g hg
  obtain ⟨t, rfl⟩ := (mem_lineRoot x g).mp hg
  exact (mem_planeRadical_iff _).mpr ⟨_, rfl⟩

lemma lineRoot_isRoot (x : F) : IsSylowTransvectionRoot (lineRoot x) :=
  ⟨(lineRoot_le_plane x).trans planeRadical_le_unipotent, _, rfl⟩

lemma infinityShear_root (t : F) :
    Plane.shearSp (infinityShear t) = rootElement 2 t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [infinityShear,Plane.shearSp,rootElement,rootMatrix,fromBlocks,Matrix.single]

lemma root_two_le_plane : RootSubgroup.group (F := F) 2 ≤ planeRadical := by
  intro g hg
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 2 g).mp hg
  rw [← infinityShear_root]
  exact (mem_planeRadical_iff _).mpr ⟨_, rfl⟩

private lemma shear_fixed_lower (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (P Q R S : Matrix (Fin 2) (Fin 2) F)
    (h : matrixAction σ (Plane.shearSp B) (fromBlocks P Q R S) = fromBlocks P Q R S) :
    B.val * S = 0 := by
  have hh := congrArg Matrix.toBlocks₁₂ h
  simpa [shear_blocks] using hh

private lemma shear_fixed_upper (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (P Q R : Matrix (Fin 2) (Fin 2) F)
    (h : matrixAction σ (Plane.shearSp B) (fromBlocks P Q R 0) = fromBlocks P Q R 0) :
    B.val * R + Q * (B.val.map σ).transpose = 0 := by
  have hh := congrArg Matrix.toBlocks₁₁ h
  simpa [shear_blocks, add_assoc] using hh

lemma four_roots_fixed (σ : F ≃+* F) (x : F) (hx : σ x ≠ x)
    (a b c d : F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (P Q R S : Matrix (Fin 2) (Fin 2) F)
    (h0 : matrixAction σ (Plane.shearSp (lineShear 0 a)) (fromBlocks P Q R S) = fromBlocks P Q R S)
    (hi : matrixAction σ (Plane.shearSp (infinityShear b)) (fromBlocks P Q R S) = fromBlocks P Q R S)
    (h1 : matrixAction σ (Plane.shearSp (lineShear 1 c)) (fromBlocks P Q R S) = fromBlocks P Q R S)
    (hx' : matrixAction σ (Plane.shearSp (lineShear x d)) (fromBlocks P Q R S) = fromBlocks P Q R S) :
    Q = 0 ∧ R = 0 ∧ S = 0 := by
  have hS : S = 0 := by
    have h0S := shear_fixed_lower σ _ _ _ _ _ h0
    have hiS := shear_fixed_lower σ _ _ _ _ _ hi
    ext i j
    fin_cases i
    · have hh := congrArg (fun M => M 0 j) h0S
      have hh' : a * S 0 j = 0 := by
        simpa [lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using hh
      exact (mul_eq_zero.mp hh').resolve_left ha
    · have hh := congrArg (fun M => M 1 j) hiS
      have hh' : b * S 1 j = 0 := by
        simpa [infinityShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using hh
      exact (mul_eq_zero.mp hh').resolve_left hb
  subst S
  have e0 := shear_fixed_upper σ _ _ _ _ h0
  have ei := shear_fixed_upper σ _ _ _ _ hi
  have e1 := shear_fixed_upper σ _ _ _ _ h1
  have ex := shear_fixed_upper σ _ _ _ _ hx'
  have hsa : σ a ≠ 0 := (map_ne_zero σ).mpr ha
  have hsb : σ b ≠ 0 := (map_ne_zero σ).mpr hb
  have hsc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hsd : σ d ≠ 0 := (map_ne_zero σ).mpr hd
  have r01 : R 0 1 = 0 := by
    have hh : a * R 0 1 = 0 := by
      simpa [lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using congrArg (fun M => M 0 1) e0
    exact (mul_eq_zero.mp hh).resolve_left ha
  have q10 : Q 1 0 = 0 := by
    have hh : Q 1 0 * σ a = 0 := by
      simpa [lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using congrArg (fun M => M 1 0) e0
    exact (mul_eq_zero.mp hh).resolve_right hsa
  have r10 : R 1 0 = 0 := by
    have hh : b * R 1 0 = 0 := by
      simpa [infinityShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using congrArg (fun M => M 1 0) ei
    exact (mul_eq_zero.mp hh).resolve_left hb
  have q01 : Q 0 1 = 0 := by
    have hh : Q 0 1 * σ b = 0 := by
      simpa [infinityShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using congrArg (fun M => M 0 1) ei
    exact (mul_eq_zero.mp hh).resolve_right hsb
  have e100 : c * R 0 0 + Q 0 0 * σ c = 0 := by
    simpa [lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,r10,q01] using congrArg (fun M => M 0 0) e1
  have e101 : c * R 1 1 + Q 0 0 * σ c = 0 := by
    simpa [lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,r01,q01] using congrArg (fun M => M 0 1) e1
  have e110 : c * R 0 0 + Q 1 1 * σ c = 0 := by
    simpa [lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,r10,q10] using congrArg (fun M => M 1 0) e1
  have rdiag : R 1 1 = R 0 0 := by
    apply (mul_left_cancel₀ hc)
    exact add_right_cancel (e101.trans e100.symm)
  have qdiag : Q 1 1 = Q 0 0 := by
    apply (mul_right_cancel₀ hsc)
    exact add_left_cancel (e110.trans e100.symm)
  have ex00 : d * R 0 0 + Q 0 0 * σ d = 0 := by
    simpa [lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,r10,q01] using congrArg (fun M => M 0 0) ex
  have ex01 : d*x*R 0 0 + Q 0 0*(σ d*σ x) = 0 := by
    simpa [lineShear,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,r01,q01,rdiag] using congrArg (fun M => M 0 1) ex
  have q00 : Q 0 0 = 0 := by
    have he : Q 0 0 * (σ d * (σ x - x)) = 0 := by
      linear_combination ex01 - x * ex00
    exact (mul_eq_zero.mp he).resolve_right (mul_ne_zero hsd (sub_ne_zero.mpr hx))
  have r00 : R 0 0 = 0 := by
    rw [q00,zero_mul,add_zero] at ex00
    exact (mul_eq_zero.mp ex00).resolve_left hd
  refine ⟨?_, ?_, rfl⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [q00,q01,q10,qdiag]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [r00,r01,r10,rdiag]


/-- The index calculation for a root of either elementary radical. -/
lemma radical_root_relIndex {Y R : Subgroup (Sp F)}
    (hY : Nat.card Y = Nat.card F ^ 3) (hR : Nat.card R = Nat.card F)
    (hRY : R ≤ Y) : R.relIndex Y = Nat.card F ^ 2 := by
  have he := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Sp F)) R Y bot_le hRY
  simp only [Subgroup.relIndex_bot_left, hY, hR] at he
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F))
  rw [he]
  ring

/-- Rank above twice the field exponent forces intersection with each literal root. -/
lemma radical_root_intersection {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {A Y R : Subgroup (Sp F)} (hAY : A ≤ Y)
    (hY : Nat.card Y = Nat.card F ^ 3) (hR : Nat.card R = Nat.card F)
    (hRY : R ≤ Y) (hr : 2 * n < rank A) : A ⊓ R ≠ ⊥ := by
  intro hz
  have hi := radical_root_relIndex hY hR hRY
  have hle := R.relIndex_le_of_le_right hAY (hi ▸ pow_ne_zero _ Nat.card_pos.ne')
  have he : R.relIndex A = Nat.card A := by
    rw [← Subgroup.inf_relIndex_left, hz, Subgroup.relIndex_bot_left]
  rw [he, hi, hF, ← pow_mul] at hle
  have hl := Nat.log_mono_right (b := 2) hle
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  change rank A ≤ n * 2 at hl
  omega

lemma exists_lineShear_mem_of_rank {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {A : Subgroup (Sp F)} (hA : A ≤ planeRadical) (hr : 2 * n < rank A) (x : F) :
    ∃ t : F, t ≠ 0 ∧ Plane.shearSp (lineShear x t) ∈ A := by
  have hi := radical_root_intersection hF hA card_planeRadical
    (lineRoot_isRoot x).card (lineRoot_le_plane x) hr
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hi
  obtain ⟨t, ht⟩ := (mem_lineRoot x g.val).mp g.property.2
  refine ⟨t, ?_, ht.symm ▸ g.property.1⟩
  intro hz
  apply hg
  apply Subtype.ext
  rw [← ht, hz, ← lineShear_conjugate, RootSubgroup.element_zero, map_one]
  rfl

lemma exists_infinityShear_mem_of_rank {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {A : Subgroup (Sp F)} (hA : A ≤ planeRadical) (hr : 2 * n < rank A) :
    ∃ t : F, t ≠ 0 ∧ Plane.shearSp (infinityShear t) ∈ A := by
  have hi := radical_root_intersection hF hA card_planeRadical
    (RootSubgroup.card 2) root_two_le_plane hr
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hi
  obtain ⟨t, ht⟩ := (RootSubgroup.mem_group_iff 2 g.val).mp g.property.2
  refine ⟨t, ?_, ?_⟩
  · intro hz
    apply hg
    apply Subtype.ext
    rw [← ht, hz, RootSubgroup.element_zero]
    rfl
  · rw [infinityShear_root, ht]
    exact g.property.1

theorem plane_subgroup_matrix_fixed {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    {A : Subgroup (Sp F)} (hA : A ≤ planeRadical) (hr : 2 * n < rank A)
    (X : Mat (F := F)) (hX : ∀ g : A, matrixAction σ g.val X = X) :
    ∀ g : planeRadical (F := F), matrixAction σ g.val X = X := by
  have hex : ∃ x : F, σ x ≠ x := by
    by_contra! he
    apply hne
    ext x
    exact he x
  obtain ⟨x, hx⟩ := hex
  obtain ⟨a, ha, hAa⟩ := exists_lineShear_mem_of_rank hF hA hr 0
  obtain ⟨b, hb, hAb⟩ := exists_infinityShear_mem_of_rank hF hA hr
  obtain ⟨c, hc, hAc⟩ := exists_lineShear_mem_of_rank hF hA hr 1
  obtain ⟨d, hd, hAd⟩ := exists_lineShear_mem_of_rank hF hA hr x
  have hh := four_roots_fixed σ x hx a b c d ha hb hc hd
    X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂
    (by simpa only [Matrix.fromBlocks_toBlocks] using hX ⟨_, hAa⟩)
    (by simpa only [Matrix.fromBlocks_toBlocks] using hX ⟨_, hAb⟩)
    (by simpa only [Matrix.fromBlocks_toBlocks] using hX ⟨_, hAc⟩)
    (by simpa only [Matrix.fromBlocks_toBlocks] using hX ⟨_, hAd⟩)
  have hfix := (blocks_fixed_iff σ hne X.toBlocks₁₁ X.toBlocks₁₂
    X.toBlocks₂₁ X.toBlocks₂₂).mpr hh
  simpa only [Matrix.fromBlocks_toBlocks] using hfix

/-- The root-intersection calculation for the plane branch, on the actual
coefficient-twisted tensor. The rank hypothesis is discharged separately by
the b₁-product and pointwise-fixer argument. -/
theorem plane_subgroup_tensor_invariants {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    {A : Subgroup (Sp F)} (hA : A ≤ planeRadical) (hr : 2 * n < rank A) :
    Representation.invariants ((twistedTensor σ).comp A.subtype) = planeTensorSpace := by
  rw [← plane_tensor_invariants σ hne]
  apply le_antisymm
  · intro v hv g
    apply coordinates.injective
    change coordinates (twistedTensor σ g.val v) = coordinates v
    rw [coordinates_action]
    apply plane_subgroup_matrix_fixed hF σ hne hA hr (coordinates v)
    intro a
    rw [← coordinates_action]
    exact congrArg coordinates (hv a)
  · intro v hv a
    exact hv ⟨a.val, hA a.property⟩

theorem plane_subgroup_tensor_fixed_finrank {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    {A : Subgroup (Sp F)} (hA : A ≤ planeRadical) (hr : 2 * n < rank A) :
    Module.finrank F (Representation.invariants ((twistedTensor σ).comp A.subtype)) = 4 := by
  rw [plane_subgroup_tensor_invariants hF σ hne hA hr, planeTensorSpace_finrank]


end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality
