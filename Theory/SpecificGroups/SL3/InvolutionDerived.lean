module

public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Solvable

/-!
# The determinant kernel in the standard involution centralizer

The block isomorphism identifies the centralizer with GL₂. Composing it with
determinant gives an abelian quotient and identifies its kernel with SL₂.
In particular the kernel contains the commutator subgroup and hence the
terminal derived subgroup. Identifying this kernel with the prime-to-p
residual over a finite field is a separate generation calculation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.3.21(a), printed p. 55.
-/

public section

open Matrix

namespace Matrix.SL3
variable (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)

/-- The full centralizer of the standard involution. -/
abbrev standardCentralizer := Subgroup.centralizer ({standardInvolution F} : Set (SpecialLinearGroup (Fin 3) F))

/-- The determinant of the two-dimensional block of a centralizer element. -/
noncomputable def centralizerDet : standardCentralizer F →* Fˣ :=
  GeneralLinearGroup.det.comp (standardInvolutionCentralizerEquiv F h2).symm.toMonoidHom

/-- Compute the centralizer determinant through the full block isomorphism. -/
theorem centralizerDet_apply (x : standardCentralizer F) :
    centralizerDet F h2 x =
      GeneralLinearGroup.det ((standardInvolutionCentralizerEquiv F h2).symm x) := by rfl

/-- The determinant kernel in the centralizer is genuinely isomorphic to SL₂. -/
noncomputable def centralizerDetKernelEquiv : (centralizerDet F h2).ker ≃*
    SpecialLinearGroup (Fin 2) F := by
  let e := (standardInvolutionCentralizerEquiv F h2).symm
  have he : ((centralizerDet F h2).ker).map e.toMonoidHom =
      (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker := by
    ext A
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hA
      refine ⟨e.symm A, ?_, e.apply_symm_apply A⟩
      change GeneralLinearGroup.det (e (e.symm A)) = 1
      simpa using hA
  exact (e.subgroupMap _).trans ((MulEquiv.subgroupCongr he).trans
    (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm)

/-- The commutator subgroup has trivial block determinant. -/
theorem centralizer_commutator_le_detKernel :
    commutator (standardCentralizer F) ≤ (centralizerDet F h2).ker :=
  Abelianization.commutator_subset_ker _

/-- The terminal derived subgroup lies in the copy of SL₂. -/
theorem centralizer_terminalDerived_le_detKernel :
    (⨅ n : ℕ, derivedSeries (standardCentralizer F) n) ≤ (centralizerDet F h2).ker :=
  (iInf_le _ 1).trans (centralizer_commutator_le_detKernel F h2)

end Matrix.SL3

end
