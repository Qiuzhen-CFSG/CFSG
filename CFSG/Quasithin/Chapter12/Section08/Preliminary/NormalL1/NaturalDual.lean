module
public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The natural-to-dual obstruction in 12.8.8(5)

A transvection fixing one basis vector and adding another to a third forces
each entry of an invariant bilinear form to vanish in dimension at least
three. This proves genuine non-self-duality, and rules out every nonzero
equivariant map from a finite sum of natural modules to the dual natural
module. The source application to the actual tilded action is in `Dimension`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 12.8.8(5), printed p.852 (PDF p.869). The source dimensions three and
four are included without a finite matrix enumeration.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section08.NormalL1

/-- Every invariant bilinear form on the binary natural module of dimension
at least three vanishes. No symmetry hypothesis is needed. -/
theorem natural_invariant_bilinear_eq_zero {d : ℕ} (hd : 2 < d)
    (B : LinearMap.BilinForm (ZMod 2) (Fin d → ZMod 2))
    (hB : ∀ (g : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) (v w),
      B (g v) (g w) = B v w) : B = 0 := by
  let b := Pi.basisFun (ZMod 2) (Fin d)
  apply LinearMap.ext_basis b b
  intro i j
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hd
  let f : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj k
  have hfi : f (b i) = 0 := by simp [f, b, hki.symm]
  let g := BinaryLinear.transvection (b i) f hfi
  have hgk : g (b k) = b k + b i := by
    change b k + f (b k) • b i = _
    simp [f, b]
  have hgj : g (b j) = b j := by
    change b j + f (b j) • b i = _
    simp [f, b, hkj.symm]
  have he := hB g (b k) (b j)
  rw [hgk, hgj, map_add, LinearMap.add_apply] at he
  exact add_eq_left.mp he

/-- There is no nonzero intertwiner from the natural module to its dual. -/
theorem natural_to_dual_eq_zero {d : ℕ} (hd : 2 < d)
    (f : (Fin d → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin d → ZMod 2))
    (hf : ∀ (g : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) v w,
      f (g v) (g w) = f v w) : f = 0 :=
  natural_invariant_bilinear_eq_zero hd f hf

/-- A direct sum of natural modules has no nonzero equivariant map to the dual
natural module. This is the quotient obstruction used in 12.8.8(5). -/
theorem natural_power_to_dual_eq_zero {d r : ℕ} (hd : 2 < d)
    (f : (Fin r → Fin d → ZMod 2) →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Fin d → ZMod 2))
    (hf : ∀ (g : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) v w,
      f (fun i => g (v i)) (g w) = f v w) : f = 0 := by
  apply LinearMap.pi_ext'
  intro i
  let s := LinearMap.single (ZMod 2) (fun _ : Fin r => Fin d → ZMod 2) i
  have hz : f.comp s = 0 := by
    apply natural_to_dual_eq_zero hd
    intro g v w
    change f (Pi.single i (g v)) (g w) = f (Pi.single i v) w
    have hs : Pi.single i (g v) = fun a => g ((Pi.single i v : Fin r → Fin d → ZMod 2) a) := by
      ext a
      by_cases ha : a = i
      · subst a; simp
      · simp [Pi.single_eq_of_ne ha]
    rw [hs]
    exact hf g (Pi.single i v) w
  exact hz

/-- A nonzero equivariant map from a homogeneous natural module to the dual
forces natural dimension at most two. The decomposition is an actual linear
equivalence, and the action on each coordinate is retained. -/
theorem dimension_le_two_of_homogeneous_duality
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {d r : ℕ}
    (ρ : ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) →* (E ≃ₗ[ZMod 2] E))
    (e : E ≃ₗ[ZMod 2] (Fin r → Fin d → ZMod 2))
    (he : ∀ g u i, e (ρ g u) i = g (e u i))
    (f : E →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin d → ZMod 2))
    (hf : ∀ g u w, f (ρ g u) (g w) = f u w) (hne : f ≠ 0) : d ≤ 2 := by
  by_contra hd
  have hz : f.comp e.symm.toLinearMap = 0 := by
    apply natural_power_to_dual_eq_zero (by omega)
    intro g v w
    have heq : e.symm (fun i => g (v i)) = ρ g (e.symm v) := by
      apply e.injective
      ext i
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    change f (e.symm (fun i => g (v i))) (g w) = f (e.symm v) w
    rw [heq]
    exact hf g (e.symm v) w
  apply hne
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro w
  have h := congrArg (fun l : (Fin r → Fin d → ZMod 2) →ₗ[ZMod 2]
    Module.Dual (ZMod 2) (Fin d → ZMod 2) => l (e u) w) hz
  simpa using h

/-- In dimensions three and four the natural module is not self-dual.
The evaluation identity is equivariance for the contragredient action. -/
theorem natural_not_self_dual {d : ℕ} (hd : 2 < d)
    (e : (Fin d → ZMod 2) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin d → ZMod 2))
    (he : ∀ (g : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) v w,
      e (g v) (g w) = e v w) : False := by
  have hf := natural_to_dual_eq_zero hd e.toLinearMap he
  have hv := congrArg (fun f : (Fin d → ZMod 2) →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Fin d → ZMod 2) => f (fun _ => 1)) hf
  have hz : e (fun _ => 1) = e 0 := by simpa using hv
  have h := congrFun (e.injective hz) ⟨0, by omega⟩
  exact one_ne_zero h

end CFSG.Quasithin.Chapter12.Section08.NormalL1
