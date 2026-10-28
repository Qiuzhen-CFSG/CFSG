module

public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.Heptad
public import Theory.Representation.BinaryAlternatingSevenCohomology
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.FirstCohomologyDuality

/-!
# A fixed functional on a central extension of the heptad module

In the dual of an extension with fixed kernel, the annihilator of that
kernel is the dual of the actual heptad module and has trivial quotient.
Its first cohomology vanishes. The connecting-map formula therefore
expresses every functional as an annihilator functional plus a fixed one.
A functional nonzero on the kernel retains that value in its fixed part.
No fixed-point-free hypothesis on the whole dual extension is imposed.
-/

public section
noncomputable section
open Representation Representation.OneCohomology Module
namespace Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
open M23Geometry.ChapterHLocalActions

/-- A central extension of the actual heptad representation admits an
invariant functional taking value one on any prescribed nonzero kernel vector. -/
theorem exists_fixed_functional {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W)
    (p : σ.IntertwiningMap heptadRepresentation) (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed σ)
    (z : W) (hz : p z = 0) (hzne : z ≠ 0) :
    ∃ ψ : Module.Dual (ZMod 2) W, ψ z = 1 ∧
      ∀ (a : alternatingGroup (Fin 7)) (w : W), ψ (σ a w) = ψ w := by
  let d := dualIntertwining p
  let U : Subrepresentation σ.dual := d.range
  have hU : U.toSubmodule = p.toLinearMap.ker.dualAnnihilator :=
    p.toLinearMap.range_dualMap_eq_dualAnnihilator_ker
  have hd : Function.Injective d := LinearMap.dualMap_injective_of_surjective hp
  let e : Module.Dual (ZMod 2) Four ≃ₗ[ZMod 2] U.toSubmodule :=
    LinearEquiv.ofBijective d.toLinearMap.rangeRestrict
      ⟨fun x y h => hd (congrArg Subtype.val h), by
        rintro ⟨y, x, hx⟩
        exact ⟨x, Subtype.ext hx⟩⟩
  have he (a : alternatingGroup (Fin 7)) (v : Module.Dual (ZMod 2) Four) :
      e (heptadRepresentation.dual a v) = U.toRepresentation a (e v) := by
    apply Subtype.ext
    exact LinearMap.congr_fun (d.isIntertwining' a) v
  let : IsIrreducible heptadRepresentation := heptadRepresentation_irreducible
  let : IsIrreducible heptadRepresentation.dual := Representation.isIrreducible_dual
  have hdim : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Four) = 4 := by
    rw [Subspace.dual_finrank_eq]
    simp [Four]
  have hH : Module.finrank (ZMod 2) (H1 (k := ZMod 2)
      (G := alternatingGroup (Fin 7)) (W := U.toSubmodule) U.toRepresentation) = 0 := by
    rw [← (H1Congr (k := ZMod 2) (G := alternatingGroup (Fin 7))
      (H := alternatingGroup (Fin 7)) (V := Module.Dual (ZMod 2) Four)
      (W := U.toSubmodule) heptadRepresentation.dual U.toRepresentation
      (MulEquiv.refl _) e he).finrank_eq]
    exact binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four
      heptadRepresentation.dual hdim
  let : Subsingleton (H1 (k := ZMod 2) (G := alternatingGroup (Fin 7))
    (W := U.toSubmodule) U.toRepresentation) := Module.finrank_zero_iff.mp hH
  have ht : HasTrivialQuotient U := by
    intro a φ
    change σ.dual a φ - φ ∈ U.toSubmodule
    rw [hU, Submodule.mem_dualAnnihilator]
    intro w hw
    change φ (σ a⁻¹ w) - φ w = 0
    rw [hk hw a⁻¹, sub_self]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hzne
  have hs := (extensionClass_eq_zero_iff U ht φ).mp (Subsingleton.elim _ _)
  obtain ⟨l, hl, ψ, hψ, hsum⟩ := Submodule.mem_sup.mp hs
  have hlz : l z = 0 := by
    rw [hU] at hl
    rw [Submodule.mem_dualAnnihilator] at hl
    exact hl z hz
  refine ⟨ψ, ?_, ?_⟩
  · have h := congrArg (fun f : Module.Dual (ZMod 2) W => f z) hsum
    simpa only [LinearMap.add_apply, hlz, zero_add, hφ] using h
  · intro a w
    have h := congrArg (fun f : Module.Dual (ZMod 2) W => f w) (hψ a⁻¹)
    simpa only [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
      LinearMap.comp_apply] using h

end Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
