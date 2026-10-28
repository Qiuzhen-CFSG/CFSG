module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Blocks.Exhaustion
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Levi.Structure
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Quotient
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Counting
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Orders and radical normality for the full parabolics of PSU₅(4)

The exhaustive line block map identifies the full projective stabilizer with
`Coord ⋊ (SU₃(4) × C₃)`. Its kernel factor has order `4^7`, and Huppert's
PSU₃ order formula transfers through actual changes of Hermitian basis and
the trivial SU₃ projective kernel. Thus the full line parabolic has order
`2^20 * (3^2 * 5^2 * 13)`. The coordinate subgroup is the image of the
semidirect-product projection kernel, hence normal in the full parabolic.

The plane restriction has the constructed parameter group as its kernel
and quotient GL₂(F₁₆) modulo scalar fifth roots. The parameter count and
Mathlib's general-linear order formula therefore give the full plane
parabolic order `2^20 * (3^2 * 5 * 17)`.

These calculations concern the full projective parabolics, including the
cubic factors above their radical--special-unitary/special-linear subgroups.
They do not identify any subgroup with the solvable residual or the two-core.

Source: the unitary parabolic calculations underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2(1) and F.1.12(7),
printed pp.4 and 263--264; Huppert, *Endliche Gruppen I*, II.10.4 and II.10.12.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F] [Finite F]

/-- The identity-form SU₃ Levi has trivial projective kernel and order 62400. -/
theorem card_identity_su3_four (J : HermitianForm 3 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    Nat.card J.specialSubgroup = 4 ^ 3 * (4 ^ 3 + 1) * (4 ^ 2 - 1) := by
  let J₀ : HermitianForm 3 F :=
    { conj := J.conj
      conj_involutive := J.conj_involutive
      form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
      form_hermitian := by intro i j; fin_cases i <;> fin_cases j <;> simp
      form_nondegenerate := by simp [Matrix.det_fin_three] }
  have hfixed : Nat.card {x : F // J₀.conj x = x} = 4 :=
    fixed_card_four J hcard hconj
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    3 J₀ 4 hcard hfixed
  let e := HermitianForm.IdentityGram.projectiveEquiv J₀ C hC
  have hid : HermitianForm.IdentityGram.identityGram J₀ = J := by
    cases J
    cases hJ
    rfl
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 J₀ 4 hcard hfixed rfl
  calc
    Nat.card J.specialSubgroup = Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Nat.card_congr (LineCore.Levi.projectEquiv J hJ hconj).toEquiv
    _ = Nat.card (ProjectiveSpecialUnitaryMatrixGroup J₀) := by
      simpa only [hid] using Nat.card_congr e.symm.toEquiv
    _ = 4 ^ 3 * (4 ^ 3 + 1) * (4 ^ 2 - 1) := by norm_num at hc ⊢; exact hc

variable [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem exists_trace_one_four (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) : ∃ c : F, c + J.conj c = 1 :=
  BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)

/-- Count the full projective line parabolic through its faithful block decomposition. -/
theorem card_lineParabolic_four (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    Nat.card (lineParabolic J) = 2 ^ 20 * (3 ^ 2 * 5 ^ 2 * 13) := by
  obtain ⟨c, hc⟩ := exists_trace_one_four J hcard hconj
  let e := MulEquiv.ofBijective (LineCore.Parabolic.Blocks.fullMap J hconj c hc hJ)
    ⟨LineCore.Parabolic.Blocks.fullMap_injective J hconj c hc hJ,
      LineCore.Parabolic.Blocks.Exhaustion.fullMap_surjective J hconj hcard c hc hJ⟩
  have hsu := card_identity_su3_four (LineCore.Parabolic.middleForm J) hcard hconj rfl
  have hroots : Nat.card (rootsOfUnity 3 F) = 3 := by
    apply FiniteField.card_rootsOfUnity_of_dvd
    rw [hcard]
    decide
  rw [← Nat.card_congr e.toEquiv, SemidirectProduct.card, Nat.card_prod,
    LineCore.Coord.card c hc, hcard, fixed_card_four J hcard hconj, hsu, hroots]
  norm_num

/-- The concrete line radical is normal inside the full line parabolic. -/
theorem line_projectiveUnipotent_normal_four (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    (LineCore.Parabolic.projectiveUnipotent J hJ).Normal := by
  obtain ⟨c, hc⟩ := exists_trace_one_four J hcard hconj
  let f := LineCore.Parabolic.Blocks.fullMap J hconj c hc hJ
  let i : LineCore.Coord J →* LineCore.Parabolic.Blocks.FullProduct J hconj :=
    SemidirectProduct.inl
  have hi : i.range.Normal := by
    dsimp [i]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hcomp : f.comp i = LineCore.Parabolic.toParabolic J hJ := by
    ext u
    simp [f, i, LineCore.Parabolic.Blocks.fullMap_apply]
  have hn := hi.map f
    (LineCore.Parabolic.Blocks.Exhaustion.fullMap_surjective J hconj hcard c hc hJ)
  rw [← MonoidHom.range_comp, hcomp] at hn
  exact hn

omit [CharP F 2] in
/-- The full plane Levi loses exactly the five scalar matrices. -/
theorem card_planeLevi_quotient_four (hcard : Nat.card F = 16) :
    Nat.card (GL (Fin 2) F ⧸ PlaneCore.planeScalarRoots (F := F)) =
      2 ^ 4 * (3 ^ 2 * 5 * 17) := by
  let : Fintype F := Fintype.ofFinite F
  have hGL : Nat.card (GL (Fin 2) F) = (16 ^ 2 - 1) * (16 ^ 2 - 16) := by
    rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hcard]
    simp [Fin.prod_univ_two]
  have h := (PlaneCore.planeScalarRoots (F := F)).card_mul_index
  rw [PlaneCore.planeScalarRoots_card hcard, Subgroup.index_eq_card, hGL] at h
  norm_num at h ⊢
  omega

/-- Count the full projective plane parabolic using its exact restriction kernel. -/
theorem card_planeParabolic_four (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    Nat.card (planeParabolic J) = 2 ^ 20 * (3 ^ 2 * 5 * 17) := by
  obtain ⟨c, hc⟩ := exists_trace_one_four J hcard hconj
  have hquot := Nat.card_congr
    (PlaneCore.planeParabolicQuotientEquiv J c hc hJ hconj).toEquiv
  have h := (PlaneCore.projectiveUnipotent J hJ).card_mul_index
  rw [PlaneCore.projectiveUnipotent_card, PlaneCore.parameters_card J hcard hconj,
    Subgroup.index_eq_card, hquot, card_planeLevi_quotient_four hcard] at h
  norm_num at h ⊢
  exact h.symm

end Theory.SpecificGroups.UnitaryFive
