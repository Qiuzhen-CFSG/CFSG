module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Spectral coordinates for the adjoint words in H.4.7

The spectral interface uses a basis of the actual trace-zero endomorphism
representation. Its weights have multiplicities two, three and three; no
existence or displacement bound is assumed by the definitions.

The projective lifting lemma derives the scalar-cube equation directly from
the quotient by the center and determinant one. It only gives ninth power one;
any stronger lifting or spectral assertion still requires proof.

Source: Aschbacher–Smith H.4.7, refs/quasithin.pdf, printed pp.382–383.
-/

@[expose] public section

open scoped MatrixGroups
open Representation.SL3.BinaryDefiningFactors
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum

variable {F K : Type*} [Field F] [Field K]

/-- The multiplicities 2, 3, 3 of the three cubic eigenvalues. -/
def adjointCubicExponent (i : Fin 8) : ℕ :=
  if i.val < 2 then 0 else if i.val < 5 then 1 else 2

/-- An actual eigenbasis of the trace-zero adjoint factor, with its precise
action. This structure specifies data and asserts no existence theorem. -/
structure AdjointCubicEigenbasis (ι : F →+* K) (g : SL(3,F)) (ω : K) where
  basis : Module.Basis (Fin 8) K (Space K .adjoint)
  action : ∀ i, factorRep ι .adjoint g (basis i) = ω ^ adjointCubicExponent i • basis i

/-- A genuine lift of a projective cubic is noncentral, its cube is scalar,
and its ninth power is one. No order-three lifting assumption is made. -/
theorem projective_cubic_lift (g : SL(3,F))
    (hg : orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3) :
    g ∉ Subgroup.center SL(3,F) ∧
      ∃ a : F, a ^ 3 = 1 ∧ (g ^ 3).val = Matrix.scalar (Fin 3) a ∧ g ^ 9 = 1 := by
  have hcube : g ^ 3 ∈ Subgroup.center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (Subgroup.center SL(3,F)) (g ^ 3) = 1
    rw [map_pow]
    simpa only [hg] using pow_orderOf_eq_one (QuotientGroup.mk' (Subgroup.center SL(3,F)) g)
  obtain ⟨a,ha,hmat⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcube
  have ha3 : a ^ 3 = 1 := by simpa using ha
  refine ⟨?_,a,ha3,hmat.symm,?_⟩
  · intro hc
    have hq : QuotientGroup.mk' (Subgroup.center SL(3,F)) g = 1 :=
      (QuotientGroup.eq_one_iff g).mpr hc
    simp only [hq, orderOf_one] at hg
    contradiction
  · apply Subtype.ext
    change (g ^ 9).val = (1 : Matrix (Fin 3) (Fin 3) F)
    rw [show 9 = 3 * 3 from rfl, pow_mul, Matrix.SpecialLinearGroup.coe_pow,
      ← hmat, ← map_pow, ha3, map_one]


end CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
