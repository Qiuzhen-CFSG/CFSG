module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Transvection directions in a binary linear subgroup

For a subgroup K of GL(V), call v a transvection direction when K contains
all maps x ↦ x + q(x)v with q(v) = 0. These vectors form a K-invariant
subspace: conjugation transports directions, and a transvection centered at
v sends an independent direction u to u + v. Over F₂, the dependent case
also preserves the set of directions.

In dimension four, if every vector is a direction, elementary-matrix
induction gives K = GL(V). The diagonal factors are trivial over F₂.
This is the generation step for the incident-flag overgroup calculation used
in Aschbacher–Smith 2.3.9(7)(g), printed pp.525–526 of `refs/quasithin.pdf`.
The matrix induction is Mathlib's Gaussian elimination theorem.
-/

@[expose] public section

namespace BinaryLinear.FourCentralizerOvergroups

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem scalar_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (scalar_cases a).resolve_left ha

private theorem add_self (v : V) : v + v = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun a => a • v) h

/-- All transvections with the given image direction lie in K. -/
def IsDirection (K : Subgroup (GL V)) (v : V) : Prop :=
  ∀ (f : V →ₗ[ZMod 2] ZMod 2) (hf : f v = 0), transvection v f hf ∈ K

private theorem direction_zero (K : Subgroup (GL V)) : IsDirection K 0 := by
  intro f hf
  have ht : transvection 0 f hf = 1 := by
    ext v
    simp [transvection]
  rw [ht]
  exact K.one_mem

/-- Conjugation by an element of K transports its transvection directions. -/
theorem direction_apply {K : Subgroup (GL V)} {v : V}
    (hv : IsDirection K v) {g : GL V} (hg : g ∈ K) : IsDirection K (g v) := by
  intro f hf
  let f' := f.comp g.toLinearMap
  have hf' : f' v = 0 := hf
  have he : transvection (g v) f hf = g * transvection v f' hf' * g⁻¹ := by
    ext x
    change x + f x • g v = g (g.symm x + f' (g.symm x) • v)
    simp [f']
  rw [he]
  exact K.mul_mem (K.mul_mem hg (hv f' hf')) (K.inv_mem hg)

private theorem direction_add {K : Subgroup (GL V)} {v w : V}
    (hv : IsDirection K v) (hw : IsDirection K w) : IsDirection K (v + w) := by
  by_cases hwv : w ∈ Submodule.span (ZMod 2) {v}
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hwv
    rcases scalar_cases a with rfl | rfl
    · simpa using hv
    · simpa only [one_smul, add_self] using direction_zero K
  · obtain ⟨f, hfw, hfv⟩ := Submodule.exists_le_ker_of_notMem hwv
    have hfv' : f v = 0 := hfv (Submodule.mem_span_singleton_self v)
    have h := direction_apply hw (hv f hfv')
    change IsDirection K (w + f w • v) at h
    simpa only [scalar_one hfw, one_smul, add_comm w v] using h

/-- The subspace of full transvection directions of K. -/
def directions (K : Subgroup (GL V)) : Submodule (ZMod 2) V where
  carrier := IsDirection K
  zero_mem' := by exact direction_zero K
  add_mem' := by exact direction_add
  smul_mem' a v hv := by
    change IsDirection K (a • v)
    rcases scalar_cases a with rfl | rfl
    · simpa using direction_zero K
    · simpa only [one_smul] using (show IsDirection K v from hv)

/-- K preserves its subspace of full transvection directions. -/
theorem le_parabolic_directions (K : Subgroup (GL V)) : K ≤ parabolic (directions K) := by
  intro g hg v
  constructor
  · intro hv
    have h := direction_apply hv (K.inv_mem hg)
    change IsDirection K v
    simpa using h
  · exact fun hv => direction_apply hv hg

/-- All full transvection directions generate the binary degree-four linear group. -/
theorem eq_top_of_directions_eq_top (K : Subgroup (GL (Fin 4 → ZMod 2)))
    (hK : directions K = ⊤) : K = ⊤ := by
  have ht (v : Fin 4 → ZMod 2) : IsDirection K v :=
    show v ∈ directions K from hK ▸ Submodule.mem_top
  have hsl (A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : A.toLin' ∈ K := by
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun A => A.toLin' ∈ K) A
    · intro i j hij c hc
      have he : Matrix.SpecialLinearGroup.diag2n hij c hc = 1 := by
        apply Subtype.ext
        simp [Matrix.SpecialLinearGroup.diag2n_coe, scalar_one hc]
      rw [he, map_one]
      exact K.one_mem
    · intro i j hij a
      let f : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := a • LinearMap.proj j
      have hf : f (Pi.single i 1) = 0 := by simp [f, hij.symm]
      have he : (Matrix.SpecialLinearGroup.transvection hij a).toLin' =
          transvection (Pi.single i 1) f hf := by
        apply LinearEquiv.ext
        intro v
        change ((1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + Matrix.single i j a).mulVec v =
          v + f v • Pi.single i 1
        simp [Matrix.add_mulVec, Matrix.single_mulVec_eq, f]
      rw [he]
      exact ht _ f hf
    · intro A B hA hB
      simpa only [map_mul] using K.mul_mem hA hB
  apply top_unique
  intro g _
  let M := LinearMap.toMatrix' g.toLinearMap
  let N := LinearMap.toMatrix' g.symm.toLinearMap
  have hinv : M * N = 1 := by
    change LinearMap.toMatrix' g.toLinearMap * LinearMap.toMatrix' g.symm.toLinearMap = 1
    rw [← LinearMap.toMatrix'_comp]
    simp
  have hd : M.det = 1 := by
    apply scalar_one
    intro hz
    have hh := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at hh
    exact zero_ne_one hh
  have he : Matrix.SpecialLinearGroup.toLin'
      (⟨M, hd⟩ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = g := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.toMatrix'_mulVec g.toLinearMap v
  rw [← he]
  exact hsl _

end BinaryLinear.FourCentralizerOvergroups

end
