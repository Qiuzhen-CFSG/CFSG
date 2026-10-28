module

public import GorensteinWalter.PGL2Cardinality

/-!
# Upper-root coordinates in PGL₂

The projective upper unipotents embed the additive field, and the matrices
`diag(k,1)` embed its units. Conjugation multiplies the root parameter by `k`.
For a matrix normalizing the root group, comparison of the bottom row in
`A U(1) z = U(x) A`, with scalar `z`, forces the lower-left entry to vanish.
Dividing by the lower-right entry then gives the root–torus factorization
of every element of the literal full normalizer.

These calculations supply the PGL₂(9) model used in Aschbacher,
*Sporadic Groups* (1994), 47.3(3), printed p.262.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
noncomputable section
namespace GorensteinWalter.PGL2NineSylowNormalizer
variable {K : Type*} [Field K]

def rootGL (x : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [det_fin_two])
def rootGLHom : Multiplicative K →* GL (Fin 2) K where
  toFun x := rootGL x.toAdd
  map_one' := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rootGL]
  map_mul' x y := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rootGL, mul_apply, Fin.sum_univ_two, add_comm]
def root : Multiplicative K →* GorensteinWalter.PGL2 K :=
  ProjGenLinGroup.mk.comp rootGLHom

def diagGL (k : Kˣ) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal ![(k : K), 1])
    (by simp [det_diagonal, Fin.prod_univ_two, k.ne_zero])
def diagGLHom : Kˣ →* GL (Fin 2) K where
  toFun := diagGL
  map_one' := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diagGL]
  map_mul' k l := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [diagGL, mul_apply, Fin.sum_univ_two]
def torus : Kˣ →* GorensteinWalter.PGL2 K :=
  ProjGenLinGroup.mk.comp diagGLHom

lemma root_injective : Function.Injective (root (K := K)) := by
  intro x y h
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h11 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 1) ha
  have h01 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) ha
  have ha1 : (a : K) = 1 := by
    simpa [rootGLHom, rootGL, GeneralLinearGroup.scalar, mul_apply, Fin.sum_univ_two] using h11
  apply Multiplicative.toAdd.injective
  simpa [rootGLHom, rootGL, GeneralLinearGroup.scalar, mul_apply, Fin.sum_univ_two, ha1] using h01

lemma torus_injective : Function.Injective (torus (K := K)) := by
  intro x y h
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h11 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 1) ha
  have h00 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) ha
  have ha1 : (a : K) = 1 := by
    simpa [diagGLHom, diagGL, GeneralLinearGroup.scalar, mul_apply, Fin.sum_univ_two] using h11
  apply Units.ext
  simpa [diagGLHom, diagGL, GeneralLinearGroup.scalar, mul_apply, Fin.sum_univ_two, ha1] using h00

lemma torus_root (k : Kˣ) (x : K) :
    torus k * root (Multiplicative.ofAdd x) * (torus k)⁻¹ =
      root (Multiplicative.ofAdd ((k : K) * x)) := by
  have h : diagGLHom k * rootGLHom (Multiplicative.ofAdd x) =
      rootGLHom (Multiplicative.ofAdd ((k : K) * x)) * diagGLHom k := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [diagGLHom, diagGL, rootGLHom, rootGL, mul_apply, Fin.sum_univ_two]
  apply (mul_inv_eq_iff_eq_mul).2
  exact congrArg ProjGenLinGroup.mk h

private lemma lower_left_zero (A : GL (Fin 2) K)
    (hA : ProjGenLinGroup.mk A ∈ Subgroup.normalizer ((root (K := K)).range : Set _)) :
    (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have hu := (Subgroup.mem_normalizer_iff.mp hA (root (Multiplicative.ofAdd (1 : K)))).1
    (show root (Multiplicative.ofAdd (1 : K)) ∈ (root (K := K)).range from ⟨_, rfl⟩)
  obtain ⟨x, hx⟩ := hu
  have he : ProjGenLinGroup.mk (A * rootGLHom (Multiplicative.ofAdd (1 : K))) =
      ProjGenLinGroup.mk (rootGLHom x * A) := by
    simpa only [map_mul, root, MonoidHom.comp_apply] using
      (mul_inv_eq_iff_eq_mul.mp hx.symm)
  obtain ⟨z, hz⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  have h10 := congrArg (fun B : GL (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K) 1 0) hz
  have h11 := congrArg (fun B : GL (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K) 1 1) hz
  simp [rootGLHom, rootGL, GeneralLinearGroup.scalar, mul_apply, Fin.sum_univ_two] at h10 h11
  by_contra hc
  have hz1 : (z : K) = 1 := (mul_eq_left₀ hc).mp h10
  rw [hz1, mul_one] at h11
  exact hc (add_eq_right.mp h11)

lemma normalizer_factor (g : GorensteinWalter.PGL2 K)
    (hg : g ∈ Subgroup.normalizer ((root (K := K)).range : Set _)) :
    ∃ x k, root x * torus k = g := by
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  have hc := lower_left_zero A hg
  have had : (A : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    have hd := A.det_ne_zero
    simpa [det_fin_two, hc] using hd
  have ha := (mul_ne_zero_iff.mp had).1
  have hd := (mul_ne_zero_iff.mp had).2
  let d : Kˣ := Units.mk0 ((A : Matrix (Fin 2) (Fin 2) K) 1 1) hd
  let k : Kˣ := Units.mk0 ((A : Matrix (Fin 2) (Fin 2) K) 0 0 /
    (A : Matrix (Fin 2) (Fin 2) K) 1 1) (div_ne_zero ha hd)
  let x : K := (A : Matrix (Fin 2) (Fin 2) K) 0 1 /
    (A : Matrix (Fin 2) (Fin 2) K) 1 1
  refine ⟨Multiplicative.ofAdd x, k, ?_⟩
  change ProjGenLinGroup.mk (rootGLHom (Multiplicative.ofAdd x)) *
    ProjGenLinGroup.mk (diagGLHom k) = _
  rw [← map_mul]
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨d, ?_⟩
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rootGLHom, rootGL, diagGLHom, diagGL, GeneralLinearGroup.scalar,
      mul_apply, vecMul, Fin.sum_univ_two, x, k, d, hc, hd]
end GorensteinWalter.PGL2NineSylowNormalizer
