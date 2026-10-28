module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The finite quadratic space of minus type

Over every finite field, `t ↦ t² + t` is not injective (its values at `0`
and `-1` agree), hence not surjective. A missing value `a` makes
`x² + xy - a y²` anisotropic. Its polar form is nonsingular, including
in characteristic two, where its cross coefficient is one.

We add `m` hyperbolic planes to this anisotropic plane. The resulting space
has dimension `2m + 2`, nonsingular polar form, and Witt index exactly `m`.
For the upper bound, project a totally singular subspace onto the second
hyperbolic coordinates. Anisotropy forces the kernel into the first
coordinates; orthogonality puts the image in the annihilator of that kernel.
Rank-nullity gives the bound. The first coordinate subspace attains it.

This is the quadratic-space construction of the minus orthogonal family in
GLS, *The Classification of the Finite Simple Groups*, volume 3, §2.7,
`refs/KGroup/GLS3/chapter2.tex`. The polynomial argument supplies the
anisotropic-plane existence required by that construction without any parity
restriction. All forms retain their quadratic values, not just their polars.
-/

@[expose] public section

namespace ClassicalOrthogonal.Minus
variable (F : Type*) [Field F]

section Finite
variable [Finite F]

theorem exists_parameter : ∃ a : F, ∀ t : F, t ^ 2 + t ≠ a := by
  classical
  have hn : ¬ Function.Injective (fun t : F => t ^ 2 + t) := by
    intro h
    have he : (0 : F) = -1 := h (by ring)
    have : (1 : F) = 0 := by linear_combination he
    exact one_ne_zero this
  have hs := mt (Finite.injective_iff_surjective.mpr) hn
  simpa only [Function.Surjective, not_forall, not_exists] using hs

noncomputable def parameter : F := (exists_parameter F).choose

theorem parameter_spec (t : F) : t ^ 2 + t ≠ parameter F :=
  (exists_parameter F).choose_spec t

end Finite

def plane (a : F) : QuadraticForm F (F × F) :=
  QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.fst F F F) +
  QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F) -
  a • QuadraticMap.linMulLin (LinearMap.snd F F F) (LinearMap.snd F F F)

@[simp] theorem plane_apply (a : F) (v : F × F) :
    plane F a v = v.1 ^ 2 + v.1 * v.2 - a * v.2 ^ 2 := by
  simp [plane, pow_two, smul_eq_mul]

theorem plane_anisotropic (a : F) (ha : ∀ t : F, t ^ 2 + t ≠ a) :
    (plane F a).Anisotropic := by
  rintro ⟨x,y⟩ h
  simp only [plane_apply] at h
  have hy : y = 0 := by
    by_contra hy
    apply ha (x / y)
    field_simp
    linear_combination h
  simp only [hy, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero] at h
  have hx : x = 0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp h
  exact Prod.ext hx hy

@[simp] theorem plane_polar (a : F) (v w : F × F) :
    (plane F a).polarBilin v w =
    2 * v.1 * w.1 + v.1 * w.2 + v.2 * w.1 - 2 * a * v.2 * w.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, plane_apply,
    Prod.fst_add, Prod.snd_add]
  ring

theorem plane_nonsingular (a : F) (ha : ∀ t : F, t ^ 2 + t ≠ a) :
    (plane F a).polarBilin.Nondegenerate := by
  have hs : (plane F a).polarBilin.SeparatingLeft := by
    intro v hv
    by_cases htwo : (2 : F) = 0
    · have h1 := hv (1,0)
      have h2 := hv (0,1)
      simp only [plane_polar, htwo, zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero] at h1 h2
      exact Prod.ext h2 h1
    · apply plane_anisotropic F a ha
      have h := hv v
      rw [plane_polar] at h
      have he : 2 * plane F a v = 0 := by
        rw [plane_apply]
        linear_combination h
      exact (mul_eq_zero.mp he).resolve_left htwo
  refine ⟨hs, ?_⟩
  intro v hv
  apply hs v
  intro w
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  exact hv w

/-- A hyperbolic plane, in coordinates. -/
def hyperbolic : QuadraticForm F (F × F) :=
  QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F)

@[simp] theorem hyperbolic_apply (v : F × F) : hyperbolic F v = v.1 * v.2 := rfl

/-- The space with `m` hyperbolic planes and one final plane. -/
abbrev Space (m : ℕ) := (Fin m → F × F) × (F × F)

/-- The orthogonal sum of `m` hyperbolic planes and the plane with parameter `a`. -/
def form (m : ℕ) (a : F) : QuadraticForm F (Space F m) :=
  (QuadraticMap.pi fun _ : Fin m => hyperbolic F).prod (plane F a)

@[simp] theorem form_apply (m : ℕ) (a : F) (v : Space F m) :
    form F m a v = (∑ i, (v.1 i).1 * (v.1 i).2) + plane F a v.2 := by
  simp [form, QuadraticMap.pi_apply]

@[simp] theorem form_polar (m : ℕ) (a : F) (v w : Space F m) :
    (form F m a).polarBilin v w =
    (∑ i, ((v.1 i).1 * (w.1 i).2 + (v.1 i).2 * (w.1 i).1)) +
      (plane F a).polarBilin v.2 w.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, form_apply,
    Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have he : (∑ i : Fin m, ((v.1 i).1 + (w.1 i).1) * ((v.1 i).2 + (w.1 i).2)) =
      (∑ i, (v.1 i).1 * (v.1 i).2) + (∑ i, (w.1 i).1 * (w.1 i).2) +
      ∑ i, ((v.1 i).1 * (w.1 i).2 + (v.1 i).2 * (w.1 i).1) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem form_nonsingular (m : ℕ) (a : F) (ha : ∀ t : F, t ^ 2 + t ≠ a) :
    (form F m a).polarBilin.Nondegenerate := by
  have hs : (form F m a).polarBilin.SeparatingLeft := by
    intro v hv
    have hplane : v.2 = 0 := by
      apply (plane_nonsingular F a ha).1
      intro w
      have h := hv (0,w)
      rw [form_polar] at h
      simpa only [Pi.zero_apply, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero,
        Finset.sum_const_zero, zero_add] using h
    have hcoords : v.1 = 0 := by
      funext i
      have h1 := hv (Pi.single i (0,1), 0)
      have h2 := hv (Pi.single i (1,0), 0)
      rw [form_polar] at h1 h2
      have e1 : (v.1 i).1 = 0 := by simpa [Pi.single_apply, apply_ite, mul_ite] using h1
      have e2 : (v.1 i).2 = 0 := by simpa [Pi.single_apply, apply_ite, mul_ite] using h2
      exact Prod.ext e1 e2
    exact Prod.ext hcoords hplane
  refine ⟨hs, ?_⟩
  intro v hv
  apply hs v
  intro w
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  exact hv w

theorem space_finrank (m : ℕ) : Module.finrank F (Space F m) = 2 * m + 2 := by
  simp [Space, Module.finrank_prod, Module.finrank_pi_fintype, mul_comm]


/-- The span of the first vector in each hyperbolic plane. -/
def singularSubspace (m : ℕ) : Submodule F (Space F m) where
  carrier := {v | (∀ i, (v.1 i).2 = 0) ∧ v.2 = 0}
  zero_mem' := ⟨fun _ => rfl, rfl⟩
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    exact ⟨fun i => by simp [hv i, hw i], by simp [hv', hw']⟩
  smul_mem' := by
    rintro c v ⟨hv, hv'⟩
    exact ⟨fun i => by simp [hv i], by simp [hv']⟩

@[simp] theorem mem_singularSubspace (m : ℕ) (v : Space F m) :
    v ∈ singularSubspace F m ↔ (∀ i, (v.1 i).2 = 0) ∧ v.2 = 0 := Iff.rfl

/-- Coordinates on the displayed totally singular subspace. -/
def singularSubspaceEquiv (m : ℕ) : (Fin m → F) ≃ₗ[F] singularSubspace F m where
  toFun x := ⟨(fun i => (x i, 0), 0), ⟨fun _ => rfl, rfl⟩⟩
  invFun v := fun i => (v.1.1 i).1
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact Prod.ext rfl (v.2.1 i).symm
    · exact v.2.2.symm
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp
  map_smul' c x := by
    apply Subtype.ext
    ext <;> simp

theorem singularSubspace_finrank (m : ℕ) :
    Module.finrank F (singularSubspace F m) = m := by
  rw [← (singularSubspaceEquiv F m).finrank_eq]
  simp

theorem form_eq_zero_on_singularSubspace (m : ℕ) (a : F)
    (v : Space F m) (hv : v ∈ singularSubspace F m) : form F m a v = 0 := by
  simp [form_apply, hv.1, hv.2]

/-- The displayed totally singular subspace is maximal by inclusion.
The anisotropic last plane is essential in this proof. -/
theorem singularSubspace_maximal (m : ℕ) (a : F)
    (ha : ∀ t : F, t ^ 2 + t ≠ a) (W : Submodule F (Space F m))
    (hW : ∀ v ∈ W, form F m a v = 0) (hUW : singularSubspace F m ≤ W) :
    W = singularSubspace F m := by
  apply le_antisymm _ hUW
  intro v hv
  have hy : ∀ i, (v.1 i).2 = 0 := by
    intro i
    let u : Space F m := (Pi.single i (1,0), 0)
    have hu : u ∈ singularSubspace F m := by
      simp [u, Pi.single_apply, apply_ite]
    have hpolar : (form F m a).polarBilin v u = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        hW _ (W.add_mem hv (hUW hu)), hW _ hv, hW _ (hUW hu)]
      ring
    rw [form_polar] at hpolar
    simpa [u, Pi.single_apply, apply_ite, mul_ite] using hpolar
  refine ⟨hy, ?_⟩
  apply plane_anisotropic F a ha
  simpa [hy] using hW v hv


/-- Every totally singular subspace has dimension at most the number of
hyperbolic planes. This certifies the minus type, in every characteristic. -/
theorem singular_finrank_le (m : ℕ) (a : F)
    (ha : ∀ t : F, t ^ 2 + t ≠ a) (W : Submodule F (Space F m))
    (hW : ∀ v ∈ W, form F m a v = 0) : Module.finrank F W ≤ m := by
  classical
  let y : W →ₗ[F] (Fin m → F) :=
    { toFun := fun w i => (w.val.1 i).2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hplane (w : W) (hw : y w = 0) : w.val.2 = 0 := by
    apply plane_anisotropic F a ha
    have hy : ∀ i, (w.val.1 i).2 = 0 := fun i => congrFun hw i
    simpa [hy] using hW w.val w.property
  let x : y.ker →ₗ[F] (Fin m → F) :=
    { toFun := fun w i => (w.val.val.1 i).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hx : Function.Injective x := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply Prod.ext (congrFun hvw i)
      exact (congrFun v.property i).trans (congrFun w.property i).symm
    · exact (hplane v.val v.property).trans (hplane w.val w.property).symm
  let d := dotProductEquiv F (Fin m)
  have hann (v : y.range) : d v.val ∈ x.range.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro z ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := v.property
    have hy : ∀ i, (w.val.val.1 i).2 = 0 := fun i => congrFun w.property i
    have hp : (form F m a).polarBilin w.val.val u.val = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        hW _ (W.add_mem w.val.property u.property),
        hW _ w.val.property, hW _ u.property]
      ring
    rw [form_polar] at hp
    simp only [hy, zero_mul, add_zero, hplane w.val w.property,
      map_zero, LinearMap.zero_apply] at hp
    change ∑ i, v.val i * (w.val.val.1 i).1 = 0
    rw [← hu]
    convert hp using 1
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  let j : y.range →ₗ[F] x.range.dualAnnihilator :=
    (d.toLinearMap.comp y.range.subtype).codRestrict x.range.dualAnnihilator hann
  have hj : Function.Injective j := by
    intro v w h
    apply Subtype.ext
    exact d.injective (congrArg Subtype.val h)
  have hle := LinearMap.finrank_le_finrank_of_injective hj
  have hxrank := LinearMap.finrank_range_of_inj hx
  have hyRank := y.finrank_range_add_finrank_ker
  have hannRank := Subspace.finrank_add_finrank_dualAnnihilator_eq x.range
  have hdim : Module.finrank F (Fin m → F) = m := by simp
  omega

end ClassicalOrthogonal.Minus
