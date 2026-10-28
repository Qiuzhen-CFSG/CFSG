module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Relations
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModelPair
import Mathlib.Tactic.FinCases

/-! The four exact third-local overlap words, with computed projective coordinates. -/
@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup Subgroup.CosetWordCertificate

/-- The third-local sides of the literal universal relators 18 through 21. -/
def overlapWord : Fin 4 → Word Bool
  | 0 => [(true,true),(false,true),(true,false),(false,true),(true,true),(false,true),(false,true),(true,true)]
  | 1 => [(true,false),(false,false),(false,false),(false,false),(true,true),(false,true),(true,false)]
  | 2 => [(true,false),(false,false),(true,true),(true,true),(false,false),(true,true)]
  | 3 => [(false,true),(true,true),(false,false),(true,false),(false,false),(false,false),(false,false),(false,false),(false,false),(false,false)]

noncomputable def overlapElement (i : Fin 4) : Canonical :=
  eval (fun b : Bool => if b then canonicalSecond else canonicalFirst) (overlapWord i)

noncomputable def rawPair : Subgroup Canonical := closure ({overlapElement 0,overlapElement 1} : Set Canonical)
noncomputable def rawThird : Subgroup Canonical := closure ({overlapElement 2,overlapElement 3} : Set Canonical)

/-- Normalized representative matrices for the four actual overlap words. -/
def overlapMatrix (i : Fin 4) : GL9 := Matrix.GeneralLinearGroup.mkOfDetNeZero
  (match i with
  | 0 => !![1,1;0,2]
  | 1 => !![1,(⟨2,2⟩:F);2,2]
  | 2 => !![1,2;(⟨1,2⟩:F),2]
  | 3 => !![1,(⟨1,2⟩:F);(⟨2,1⟩:F),(⟨1,2⟩:F)]) (by
    fin_cases i <;> decide +kernel)

def overlapCubic : Fin 4 → Z
  | 0 => Multiplicative.ofAdd 2
  | 1 => 1
  | 2 => 1
  | 3 => Multiplicative.ofAdd 1

private def liftedOverlap (i : Fin 4) : ComputableModel :=
  eval (fun b : Bool => if b then second else first) (overlapWord i)

private theorem map_eval (w : Word Bool) :
    toCanonical (eval (fun b : Bool => if b then second else first) w) =
      eval (fun b : Bool => if b then canonicalSecond else canonicalFirst) w := by
  have h : toCanonical.comp (FreeGroup.lift (fun b : Bool => if b then second else first)) =
      FreeGroup.lift (fun b : Bool => if b then canonicalSecond else canonicalFirst) := by
    apply FreeGroup.ext_hom
    intro b
    simp only [MonoidHom.comp_apply,FreeGroup.lift_apply_of]
    cases b <;> rfl
  exact DFunLike.congr_fun h (FreeGroup.mk w)

private def overlapScalar : Fin 4 → F
  | 0 => ⟨2,1⟩
  | 1 => ⟨2,1⟩
  | 2 => ⟨2,2⟩
  | 3 => ⟨1,2⟩

private def overlapUnit (i : Fin 4) : Fˣ := Units.mk0 (overlapScalar i) (by
  have h : ∀ i, overlapScalar i ≠ 0 := by decide +kernel
  exact h i)

/-- Every word retains its complete cubic coordinate and projective matrix. -/
theorem overlapElement_coordinates (i : Fin 4) :
    overlapElement i = ⟨overlapCubic i,Matrix.ProjGenLinGroup.mk (overlapMatrix i)⟩ := by
  rw [overlapElement,←map_eval]
  apply SemidirectProduct.ext
  · change (liftedOverlap i).left = overlapCubic i
    fin_cases i <;> decide +kernel
  · change Matrix.ProjGenLinGroup.mk (liftedOverlap i).right = _
    apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨overlapUnit i, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
