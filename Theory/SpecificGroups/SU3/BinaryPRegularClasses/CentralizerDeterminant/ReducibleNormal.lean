module

public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.NormalCorrection
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.TraceParameters
public import BenderSuzuki.External.Huppert.II.theorem_10_4
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Normal determinant witnesses for reducible binary SU₃ elements

For a nonscalar semisimple endomorphism of a three-dimensional space, a root
of its characteristic polynomial has an eigenspace of dimension one or two.
Semisimplicity makes this eigenspace complementary to the image of `g - μ`.
Scaling the eigenspace and fixing that image commutes with every endomorphism
centralizing `g`. Its determinant is the scaling factor or its square, and
squaring is surjective over a finite binary field. The adjoint also centralizes
`g`, so this construction is normal even when the eigenspace is isotropic.

For scalar elements, an orthonormal basis for the original Hermitian form
allows scaling just one basis vector by the prescribed norm-one determinant.
Thus repeated eigenvalues, paired isotropic lines, and the full cubic center
are all retained. The final theorem applies the adjoint correction to the
literal unitary element underlying the given special unitary element.

This is the reducible centralizer step in the semisimple class argument used
with GLS III 2.8.2, 2.8.6(a), and the SU₃ family of 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`. The scalar-case basis theorem is Huppert II.10.4.
-/

noncomputable section

namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.ReducibleNormal

open Module.End
set_option linter.unnecessarySimpa false
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem eigenspace_complement (f : Module.End F V) (hf : f.IsSemisimple) (μ : F) :
    IsCompl (f.eigenspace μ) (LinearMap.range (f - μ • 1)) := by
  have hdisj : Disjoint (f.eigenspace μ) (LinearMap.range (f - μ • 1)) := by
    rw [Submodule.disjoint_def]
    intro x hx hy
    obtain ⟨y, rfl⟩ := hy
    have hy2 : y ∈ f.genEigenspace μ (2 : ℕ∞) := by
      rw [show (2 : ℕ∞) = (2 : ℕ) by rfl, mem_genEigenspace_nat]
      change ((f - μ • 1) ^ 2 : Module.End F V) y = 0
      rw [pow_two, Module.End.mul_apply]
      change f ((f - μ • 1) y) - μ • (f - μ • 1) y = 0
      exact sub_eq_zero.mpr (mem_eigenspace_iff.mp hx)
    rw [hf.isFinitelySemisimple.genEigenspace_eq_eigenspace μ (by norm_num)] at hy2
    change f y - μ • y = 0
    exact sub_eq_zero.mpr (mem_eigenspace_iff.mp hy2)
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).mpr hdisj
  rw [eigenspace_def, add_comm, LinearMap.finrank_range_add_finrank_ker]

private theorem scaling_commutes (U W : Submodule F V) (hcomp : IsCompl U W)
    (t : F) : ∃ c : Module.End F V,
      LinearMap.det c = t ^ Module.finrank F U ∧
      ∀ b : Module.End F V, U ∈ b.invtSubmodule → W ∈ b.invtSubmodule → Commute c b := by
  let e := U.prodEquivOfIsCompl W hcomp
  let a : Module.End F (U × W) := (t • LinearMap.id).prodMap LinearMap.id
  let c : Module.End F V := e.toLinearMap.comp (a.comp e.symm.toLinearMap)
  refine ⟨c, ?_, ?_⟩
  · have hconj : LinearMap.det c = LinearMap.det a := by
      simpa [c, LinearMap.comp_assoc] using LinearMap.det_conj a e
    rw [hconj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id]
    simp
  · intro b hU hW
    let brU : Module.End F U := b.restrict hU
    let brW : Module.End F W := b.restrict hW
    let bp := brU.prodMap brW
    have heq : b.comp e.toLinearMap = e.toLinearMap.comp bp := by
      apply LinearMap.ext
      intro z
      rcases z with ⟨x, y⟩
      change b ((x : V) + (y : V)) = (brU x : V) + (brW y : V)
      rw [map_add]
      rfl
    have hacomm : a.comp bp = bp.comp a := by
      apply LinearMap.ext
      intro z
      rcases z with ⟨x, y⟩
      change (t • brU x, brW y) = (brU (t • x), brW y)
      simp
    change c.comp b = b.comp c
    ext v
    have heq' := congrArg e.symm (LinearMap.congr_fun heq (e.symm v))
    have heq'' : e.symm (b v) = bp (e.symm v) := by simpa using heq'
    simp only [c, LinearMap.comp_apply]
    calc
      e (a (e.symm (b v))) = e (a (bp (e.symm v))) := by rw [heq'']
      _ = e (bp (a (e.symm v))) := congrArg e (LinearMap.congr_fun hacomm _)
      _ = b (e (a (e.symm v))) := (LinearMap.congr_fun heq _).symm
      _ = b (c v) := rfl

private theorem eigen_scaling (f : Module.End F V) (hf : f.IsSemisimple) (μ t : F) :
    ∃ c : Module.End F V,
      LinearMap.det c = t ^ Module.finrank F (f.eigenspace μ) ∧
      ∀ b : Module.End F V, Commute b f → Commute c b := by
  obtain ⟨c, hdet, hc⟩ := scaling_commutes (f.eigenspace μ)
    (LinearMap.range (f - μ • 1)) (eigenspace_complement f hf μ) t
  refine ⟨c, hdet, fun b hb => hc b ?_ ?_⟩
  · rw [mem_invtSubmodule]
    intro x hx
    change b x ∈ f.eigenspace μ
    rw [mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, ← hb.eq, Module.End.mul_apply, hx, map_smul]
  · rw [mem_invtSubmodule]
    rintro _ ⟨x, rfl⟩
    refine ⟨b x, ?_⟩
    have hb' : Commute b (f - μ • 1) :=
      hb.sub_right ((Commute.one_right b).smul_right μ)
    exact (LinearMap.congr_fun hb'.eq x).symm

private theorem nonscalar_spectral [Finite F] [CharP F 2] (f : Module.End F (Fin 3 → F))
    (hf : f.IsSemisimple) (hscalar : ∀ μ : F, f ≠ μ • 1)
    (hred : ¬ Irreducible f.charpoly) (d : F) :
    ∃ c : Module.End F (Fin 3 → F), LinearMap.det c = d ∧
      ∀ b : Module.End F (Fin 3 → F), Commute b f → Commute c b := by
  have hroot : ∃ μ : F, f.HasEigenvalue μ := by
    by_contra h
    push Not at h
    apply hred
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · simp [LinearMap.charpoly_natDegree]
    · intro μ hμ
      exact h μ ((hasEigenvalue_iff_isRoot_charpoly f μ).mpr hμ)
  obtain ⟨μ, hμ⟩ := hroot
  have hpos : 0 < Module.finrank F (f.eigenspace μ) := by
    exact Nat.pos_of_ne_zero (fun hz => hμ (Submodule.finrank_eq_zero.mp hz))
  have hlt : Module.finrank F (f.eigenspace μ) < 3 := by
    have htop : f.eigenspace μ ≠ ⊤ := by
      intro ht
      apply hscalar μ
      apply LinearMap.ext
      intro x
      exact mem_eigenspace_iff.mp (ht ▸ Submodule.mem_top)
    simpa using Submodule.finrank_lt htop
  have hdim : Module.finrank F (f.eigenspace μ) = 1 ∨
      Module.finrank F (f.eigenspace μ) = 2 := by omega
  rcases hdim with hn | hn
  · obtain ⟨c, hc, hb⟩ := eigen_scaling f hf μ d
    exact ⟨c, by simpa [hn] using hc, hb⟩
  · obtain ⟨t, ht⟩ := Finite.surjective_of_injective (frobenius_inj F 2) d
    obtain ⟨c, hc, hb⟩ := eigen_scaling f hf μ t
    rw [hn] at hc
    exact ⟨c, hc.trans (by simpa [frobenius_def] using ht), hb⟩

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant

private theorem normal_nonscalar [Finite F] [CharP F 2] (J : HermitianForm 3 F) (g : J.unitarySubgroup)
    (hf : Module.End.IsSemisimple (Matrix.toLin' g.val.val))
    (hscalar : ∀ μ : F, g.val.val ≠ μ • 1)
    (hred : ¬ Irreducible g.val.val.charpoly) (d : Fˣ) :
    ∃ A : GL (Fin 3) F, Commute A g.val ∧ Commute A (adjoint J A) ∧
      GeneralLinearGroup.det A = d := by
  classical
  let f := Matrix.toLin' g.val.val
  have hns : ∀ μ : F, f ≠ μ • 1 := by
    intro μ he
    apply hscalar μ
    have hh := congrArg LinearMap.toMatrix' he
    simpa [f] using hh
  have hredf : ¬ Irreducible f.charpoly := by
    simpa [f, Matrix.charpoly_toLin'] using hred
  obtain ⟨c, hc, hcb⟩ := nonscalar_spectral f hf hns hredf (d : F)
  have hdet : (LinearMap.toMatrix' c).det = (d : F) := by
    rw [← LinearMap.det_toLin', Matrix.toLin'_toMatrix', hc]
  let A : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix' c)
    (hdet ▸ d.ne_zero)
  have hcomm (B : GL (Fin 3) F) (hB : Commute B g.val) : Commute A B := by
    have hb : Commute (Matrix.toLin' B.val) f := by
      change (Matrix.toLin' B.val).comp (Matrix.toLin' g.val.val) =
        (Matrix.toLin' g.val.val).comp (Matrix.toLin' B.val)
      have hh := congrArg Matrix.toLin' (congrArg Units.val hB.eq)
      simpa only [Units.val_mul, Matrix.toLin'_mul] using hh
    apply Units.ext
    change LinearMap.toMatrix' c * B.val = B.val * LinearMap.toMatrix' c
    have hh := congrArg LinearMap.toMatrix' (hcb _ hb).eq
    simpa only [Module.End.mul_eq_comp, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin'] using hh
  have hAg := hcomm g.val (Commute.refl _)
  exact ⟨A, hAg, hcomm (adjoint J A) (commute_adjoint J g A hAg), Units.ext hdet⟩

private theorem ct_mul (J : HermitianForm 3 F) (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem ct_one (J : HermitianForm 3 F) : J.conjTranspose 1 = 1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one, transpose_one]

private theorem normal_scalar [Finite F] (J : HermitianForm 3 F) (s : ℕ) (hs : 0 < s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (g : GL (Fin 3) F) (μ : F) (hg : g.val = μ • 1)
    (d : Fˣ) (hd : J.conj (d : F) * (d : F) = 1) :
    ∃ A : GL (Fin 3) F, Commute A g ∧ Commute A (adjoint J A) ∧
      GeneralLinearGroup.det A = d := by
  classical
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s hs hcard hconj
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    3 J (2 ^ s) hcard hfixed
  let Dmat : Matrix (Fin 3) (Fin 3) F := diagonal ![(d : F), 1, 1]
  have hDdet : Dmat.det = (d : F) := by
    simp [Dmat, det_diagonal, Fin.prod_univ_three]
  let D : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero Dmat
    (hDdet ▸ d.ne_zero)
  have hD : J.conjTranspose D.val * D.val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Dmat, GeneralLinearGroup.mkOfDetNeZero,
        HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hd]
  let A : GL (Fin 3) F := P * D * P⁻¹
  have hPcancel : J.conjTranspose (P⁻¹).val * J.conjTranspose P.val = 1 := by
    rw [← ct_mul]
    simpa using ct_one J
  have hbase : J.conjTranspose (P⁻¹).val * 1 * (P⁻¹).val = J.form := by
    rw [← hP]
    calc
      _ = (J.conjTranspose (P⁻¹).val * J.conjTranspose P.val) * J.form *
          (P.val * (P⁻¹).val) := by simp only [mul_assoc]
      _ = J.form := by rw [hPcancel, Units.mul_inv, one_mul, mul_one]
  have hA : A ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff]
    change J.conjTranspose (P.val * D.val * (P⁻¹).val) * J.form *
      (P.val * D.val * (P⁻¹).val) = J.form
    rw [ct_mul, ct_mul]
    calc
      _ = J.conjTranspose (P⁻¹).val *
          (J.conjTranspose D.val * (J.conjTranspose P.val * J.form * P.val) * D.val) *
          (P⁻¹).val := by simp only [mul_assoc]
      _ = J.conjTranspose (P⁻¹).val * 1 * (P⁻¹).val := by rw [hP, mul_one, hD]
      _ = J.form := hbase
  refine ⟨A, ?_, ?_, ?_⟩
  · apply Units.ext
    change A.val * g.val = g.val * A.val
    rw [hg]
    simp
  · rw [(mem_unitary_iff_adjoint J A).mp hA]
    exact (Commute.refl A).inv_right
  · have hdetD : GeneralLinearGroup.det D = d := Units.ext hDdet
    simp only [A, map_mul, map_inv, hdetD]
    simp [mul_comm]

/-- Every odd-order special unitary element with reducible characteristic
polynomial has a normal linear centralizer witness of each norm-one determinant. -/
public theorem exists_normal_commuting_det [Finite F] [Algebra (ZMod 2) F]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (g : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g)
    (hred : ¬ Irreducible g.val.val.charpoly)
    (d : Fˣ) (hd : J.conj (d : F) * (d : F) = 1) :
    ∃ A : GL (Fin 3) F, Commute A g.val ∧ Commute A (adjoint J A) ∧
      GeneralLinearGroup.det A = d := by
  classical
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  by_cases hscalar : ∃ μ : F, g.val.val = μ • 1
  · obtain ⟨μ, hμ⟩ := hscalar
    exact normal_scalar J s (by omega) hcard hconj g.val μ hμ d hd
  · push Not at hscalar
    exact normal_nonscalar J ⟨g.val, J.specialSubgroup_le_unitarySubgroup g.property⟩
      (Theory.SpecificGroups.SU3.BinaryPRegularClasses.isSemisimple_of_pRegular J g hg)
      hscalar hred d

/-- The reducible branch of unitary centralizer determinant surjectivity,
with all spectral and Hermitian premises discharged from the given element. -/
public theorem exists_unitary_commuting_det [Finite F] [Algebra (ZMod 2) F]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (g : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g)
    (hred : ¬ Irreducible g.val.val.charpoly)
    (d : Fˣ) (hd : J.conj (d : F) * (d : F) = 1) :
    ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d := by
  obtain ⟨A, hAg, hAn, hAd⟩ :=
    exists_normal_commuting_det J s hs hcard hconj g hg hred d hd
  exact exists_unitary_commuting_det_of_normal J
    ⟨g.val, J.specialSubgroup_le_unitarySubgroup g.property⟩ s (by omega)
    hcard d hd A hAg hAn hAd

end Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.ReducibleNormal
