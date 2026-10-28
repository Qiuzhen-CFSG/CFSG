module

public import Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.Shears
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental

/-!
# A proper unitary line parabolic in every dimension at least three

The line spanned by e₀+e₁ is isotropic in characteristic two. The coordinate
interchange is a shear whose displacements fill it. Consequently the full
projective line stabilizer is two-local. An interchange with a third coordinate
proves properness. The complementary special-unitary block fixes this line.

Source: the classical parabolic sections in Aschbacher--Smith A.2.18, p.40.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections
open ProjectiveKernel OddFundamental
open Theory.SpecificGroups.UnitaryFive (shearSubgroup)
variable {F : Type*} [Field F] [CharP F 2] {d : ℕ}

/-- A coordinate interchange preserves the identity Hermitian form in characteristic two. -/
def swapSpecial (J : HermitianForm d F) (hJ : J.form = 1)
    (i j : Fin d) (hij : i ≠ j) : J.specialSubgroup := by
  let A : GL (Fin d) F :=
    ⟨(Equiv.swap i j).permMatrix F, (Equiv.swap i j).permMatrix F,
      by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one],
      by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]⟩
  refine ⟨A, ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, mul_one]
    have he : J.conjTranspose A.val = A.val := by
      change (((Equiv.swap i j).permMatrix F).map J.conj).transpose = _
      have hm : ((Equiv.swap i j).permMatrix F).map J.conj = (Equiv.swap i j).permMatrix F := by
        ext a b
        simp [Matrix.map, apply_ite]
      rw [hm, transpose_permMatrix, Equiv.swap_inv]
    rw [he]
    exact A.val_inv
  · apply Units.ext
    change ((Equiv.swap i j).permMatrix F).det = 1
    rw [det_permutation, Equiv.Perm.sign_swap hij]
    simp [CharTwo.neg_eq]

@[simp] theorem swapSpecial_apply (J : HermitianForm d F) (hJ : J.form = 1)
    (i j : Fin d) (hij : i ≠ j) (v : Fin d → F) :
    linearAction J (swapSpecial J hJ i j hij) v = v ∘ Equiv.swap i j :=
  Matrix.permMatrix_mulVec _

variable (F) (n : ℕ)

def first : Fin (2+n) := Fin.castAdd n 0
def second : Fin (2+n) := Fin.castAdd n 1

theorem first_ne_second : first n ≠ second n := by simp [first, second]

/-- A generator of the isotropic line. -/
def lineVector : Fin (2+n) → F := Pi.single (first n) 1 + Pi.single (second n) 1

/-- The actual isotropic line used to define the parabolic. -/
def line : Submodule F (Fin (2+n) → F) := Submodule.span F {lineVector F n}

omit [CharP F 2] in
@[simp] theorem lineVector_first : lineVector F n (first n) = 1 := by
  simp [lineVector, first_ne_second]

omit [CharP F 2] in
@[simp] theorem lineVector_second : lineVector F n (second n) = 1 := by
  simp [lineVector, (first_ne_second n).symm]

omit [CharP F 2] in
@[simp] theorem lineVector_other {i : Fin (2+n)} (h0 : i ≠ first n) (h1 : i ≠ second n) :
    lineVector F n i = 0 := by simp [lineVector, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1]

omit [CharP F 2] in
theorem lineVector_mem : lineVector F n ∈ line F n := Submodule.subset_span (by simp)

theorem line_isotropic (σ : F ≃+* F) (v w : line F n) :
    (fun i => σ (v.val i)) ⬝ᵥ w.val = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.property
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp w.property
  rw [← ha, ← hb]
  rw [dotProduct_smul]
  change b * ((fun i => σ ((a • lineVector F n) i)) ⬝ᵥ
    (Pi.single (first n) 1 + Pi.single (second n) 1)) = 0
  rw [dotProduct_add, dotProduct_single, dotProduct_single]
  simp [CharTwo.add_self_eq_zero]

variable {F n} (J : HermitianForm (2+n) F) (hJ : J.form = 1)

def lineSwap : J.specialSubgroup := swapSpecial J hJ (first n) (second n) (first_ne_second n)

private theorem lineSwap_displacement (v : Fin (2+n) → F) :
    linearAction J (lineSwap J hJ) v - v =
      (v (second n) + v (first n)) • lineVector F n := by
  rw [lineSwap, swapSpecial_apply]
  ext i
  by_cases h0 : i = first n
  · subst i
    simp [CharTwo.sub_eq_add]
  by_cases h1 : i = second n
  · subst i
    simp [CharTwo.sub_eq_add, add_comm]
  simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1, lineVector_other F n h0 h1]

theorem lineSwap_shear : lineSwap J hJ ∈ shearSubgroup (linearAction J) (line F n) := by
  constructor
  · intro v hv
    have he : v (second n) = v (first n) := by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp
    apply sub_eq_zero.mp
    rw [lineSwap_displacement, he, CharTwo.add_self_eq_zero, zero_smul]
  · intro v
    rw [lineSwap_displacement]
    exact (line F n).smul_mem _ (lineVector_mem F n)

include hJ in
theorem line_displacements (v : Fin (2+n) → F) (hv : v ∈ line F n) :
    ∃ a ∈ shearSubgroup (linearAction J) (line F n), ∃ w, linearAction J a w - w = v := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨lineSwap J hJ, lineSwap_shear J hJ, Pi.single (second n) c, ?_⟩
  rw [lineSwap_displacement]
  simp [Pi.single_eq_of_ne (first_ne_second n)]

theorem project_lineSwap_ne_one : project J (lineSwap J hJ) ≠ 1 := by
  intro h
  have he : ProjGenLinGroup.mk (lineSwap J hJ).val = 1 := congrArg Subtype.val h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at he
  obtain ⟨u, hu⟩ := he
  have hc := congrArg (fun A : GL (Fin (2+n)) F => A.val (first n) (second n)) hu
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, lineSwap, swapSpecial,
    first_ne_second] at hc

include hJ in
/-- The literal projective line stabilizer is two-local, including the smallest field. -/
theorem lineParabolic_isTwoLocal [Finite F] : IsTwoLocal (parabolic J (line F n)) := by
  refine ⟨projectiveShearSubgroup J (line F n), ?_, projectiveShearSubgroup_isPGroup J _, ?_⟩
  · intro h
    have hm : project J (lineSwap J hJ) ∈ projectiveShearSubgroup J (line F n) :=
      ⟨_, lineSwap_shear J hJ, rfl⟩
    rw [h, Subgroup.mem_bot] at hm
    exact project_lineSwap_ne_one J hJ hm
  · exact (normalizer_projectiveShearSubgroup J _ (line_displacements J hJ)).symm


include hJ in
/-- A third-coordinate interchange does not preserve the isotropic line. -/
theorem lineParabolic_ne_top [NeZero n] : parabolic J (line F n) ≠ ⊤ := by
  let t : Fin (2+n) := Fin.natAdd 2 (0 : Fin n)
  have ht0 : t ≠ first n := by simp [t, first, Fin.ext_iff]
  have ht1 : t ≠ second n := by simp [t, second, Fin.ext_iff]
  let g := swapSpecial J hJ (second n) t ht1.symm
  intro htop
  have hg : project J g ∈ parabolic J (line F n) := htop ▸ Subgroup.mem_top _
  have hs := (project_mem_parabolic_iff J _ g).mp hg
  have hv := (mem_specialStabilizer_iff J _ g).mp hs (lineVector F n)
  have hm : linearAction J g (lineVector F n) ∈ line F n := hv.mpr (lineVector_mem F n)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have h0 := congrFun hc (first n)
  have h1 := congrFun hc (second n)
  have hswap : Equiv.swap (second n) t (first n) = first n :=
    Equiv.swap_apply_of_ne_of_ne (first_ne_second n) ht0.symm
  simp only [g, swapSpecial_apply, Function.comp_apply, hswap, Pi.smul_apply,
    smul_eq_mul, lineVector_first, mul_one] at h0
  simp only [g, swapSpecial_apply, Function.comp_apply, Equiv.swap_apply_left,
    Pi.smul_apply, smul_eq_mul, lineVector_second, mul_one,
    lineVector_other F n ht0 ht1] at h1
  exact one_ne_zero (h0.symm.trans h1)

omit [CharP F 2] in
/-- The complementary block fixes the isotropic line pointwise. -/
theorem right_fixes_lineVector (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (a : (form σ hσ n).specialSubgroup) :
    linearAction (form σ hσ (2+n)) (right σ hσ a) (lineVector F n) = lineVector F n := by
  change blockMatrix (1 : Matrix (Fin 2) (Fin 2) F) a.val.val *ᵥ _ = _
  rw [lineVector, Matrix.mulVec_add, Matrix.mulVec_single, Matrix.mulVec_single]
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl j =>
      fin_cases j <;> simp [blockMatrix, reindex_apply, first, second]
  | inr j =>
      have h0 : Fin.natAdd 2 j ≠ Fin.castAdd n (0 : Fin 2) := by
        intro h
        have hh := congrArg Fin.val h
        change 2 + j.val = 0 at hh
        omega
      have h1 : Fin.natAdd 2 j ≠ Fin.castAdd n (1 : Fin 2) := by
        intro h
        have hh := congrArg Fin.val h
        change 2 + j.val = 1 at hh
        omega
      simp [blockMatrix, reindex_apply, h0, h1, first, second]

omit [CharP F 2] in
/-- The actual complementary SU block lies in the full line stabilizer. -/
theorem right_mem_lineStabilizer [Finite F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (a : (form σ hσ n).specialSubgroup) :
    right σ hσ a ∈ specialStabilizer (form σ hσ (2+n)) (line F n) := by
  apply mem_specialStabilizer_of_preserves
  intro v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, right_fixes_lineVector]
  exact (line F n).smul_mem _ (lineVector_mem F n)

/-- The faithful projective block homomorphism, with codomain the actual parabolic. -/
def complement [Finite F] (σ : F ≃+* F) (hσ : Function.Involutive σ) :
    (form σ hσ n).specialSubgroup →* parabolic (form σ hσ (2+n)) (line F n) :=
  (projectRight σ hσ).codRestrict _ (fun a => ⟨_, right_mem_lineStabilizer σ hσ a, rfl⟩)

omit [CharP F 2] in
theorem complement_injective [Finite F] (σ : F ≃+* F) (hσ : Function.Involutive σ) :
    Function.Injective (complement (n := n) σ hσ) := by
  intro a b h
  exact projectRight_injective σ hσ (congrArg Subtype.val h)

end Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections
