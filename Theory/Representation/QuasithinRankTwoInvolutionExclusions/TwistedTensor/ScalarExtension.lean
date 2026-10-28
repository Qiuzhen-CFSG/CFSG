module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.Representation.ScalarDescent

/-!
# Displacement rank under scalar extension

Flat scalar extension preserves kernels; rank-nullity and the dimension formula
for base change therefore preserve the rank of an endomorphism. Applying this
to the displacement operator gives the exact descent needed for the twisted
SL₂(8) tensor in G.11.2(11), used in 6.2.19 (printed pp.364 and 691).
The representation-equivalence wrapper retains the actual intertwiner.
-/

public section

namespace Representation.RankTwo

variable {k E G V : Type*} [Field k] [Field E] [Algebra k E] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Extension of the coefficient field preserves the rank of an endomorphism. -/
theorem finrank_range_baseChange (f : V →ₗ[k] V) :
    Module.finrank E (LinearMap.range (f.baseChange E)) =
      Module.finrank k (LinearMap.range f) := by
  have hk : Module.finrank E (LinearMap.ker (f.baseChange E)) =
      Module.finrank k (LinearMap.ker f) := by
    rw [← LinearMap.baseChange_ker_eq]
    rw [← (Submodule.toBaseChange.toLinearEquiv E (LinearMap.ker f)).finrank_eq]
    exact Module.finrank_baseChange
  have h₁ := LinearMap.finrank_range_add_finrank_ker f
  have h₂ := LinearMap.finrank_range_add_finrank_ker (f.baseChange E)
  rw [hk, Module.finrank_baseChange] at h₂
  omega

/-- Displacement dimension is unchanged by scalar extension. -/
theorem finrank_movedSpace_extendScalars (ρ : Representation k G V) (g : G) :
    Module.finrank E (movedSpace (extendScalars E ρ) g) =
      Module.finrank k (movedSpace ρ g) := by
  unfold movedSpace
  rw [extendScalars_apply, ← LinearMap.baseChange_one, ← LinearMap.baseChange_sub]
  exact finrank_range_baseChange _

omit [FiniteDimensional k V] in
/-- The identity has zero displacement dimension. -/
theorem finrank_movedSpace_one (ρ : Representation k G V) :
    Module.finrank k (movedSpace ρ 1) = 0 := by
  rw [movedSpace, map_one, sub_self, LinearMap.range_zero, finrank_bot]

omit [FiniteDimensional k V] in
/-- Core representation equivalences preserve displacement dimension. -/
theorem finrank_movedSpace_equiv {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (τ : Representation k G W) (f : ρ.Equiv τ) (g : G) :
    Module.finrank k (movedSpace ρ g) = Module.finrank k (movedSpace τ g) := by
  exact finrank_movedSpace_transport ρ τ (MulEquiv.refl G) f.toLinearEquiv
    (fun j z => congrArg (fun t => t z) (f.isIntertwining' j)) g

end Representation.RankTwo
