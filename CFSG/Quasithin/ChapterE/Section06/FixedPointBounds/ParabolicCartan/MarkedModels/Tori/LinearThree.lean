module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags

/-!
# Concrete torus in the marked LinearThree Borel

The matrices diag(a,a⁻¹,1) lie in the flag Borel. Their third diagonal
entry excludes a nonidentity scalar kernel after projection to PSL₃.

These proofs adapt the corresponding `BorelReduction/HigherRankTori/LinearThree`
module in Chapter 15, using only the underlying matrix mathematics and no
later source assumptions. Their consumer is `MarkedModels.Cyclic`.
Source: Aschbacher--Smith, E.2.2, printed pp.215--216; the rank-one matrices
are those of Huppert II.10.12 and Huppert--Blackburn XI.3.1--3.
-/

@[expose] public section

open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
variable (F : Type*) [Field F] [Finite F]

/-- The diagonal split torus in the special linear flag stabilizer. -/
def sl3Torus : Fˣ →* borelSL F where
  toFun a := ⟨pointTorus F a, pointTorus_mem_borel F a⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pointTorus]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm]

/-- The first diagonal entry recovers the unit. -/
theorem sl3Torus_injective : Function.Injective (sl3Torus F) := by
  intro a b h
  apply Units.ext
  exact congrArg (fun x : borelSL F => x.val.val 0 0) h

/-- Its image in the actual projective flag stabilizer. -/
def psl3Torus : Fˣ →* borel F :=
  ((projection F).subgroupMap (borelSL F)).comp (sl3Torus F)

/-- The third diagonal entry rules out every nonidentity scalar kernel. -/
theorem psl3Torus_injective : Function.Injective (psl3Torus F) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro a ha
  have hp : pointTorus F a ∈ (projection F).ker := congrArg Subtype.val ha
  rw [projection_ker] at hp
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hp
  have hr1 : r = 1 := by
    have h := congrArg (fun x : Matrix (Fin 3) (Fin 3) F => x 2 2) hr
    simpa [scalar, pointTorus] using h
  have ha1 : (a : F) = 1 := by
    have h := congrArg (fun x : Matrix (Fin 3) (Fin 3) F => x 0 0) hr
    simpa [scalar, pointTorus, hr1] using h.symm
  exact Units.ext ha1
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
