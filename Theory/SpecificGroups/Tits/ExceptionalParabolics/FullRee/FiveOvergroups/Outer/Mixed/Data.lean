module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Core
public import GorensteinWalter.PGL2Twisted
public import GorensteinWalter.PGL2DeterminantSquare

/-! The concrete quadratic involution and nonsquare-determinant matrix give
the mixed semilinear outer actor. Small closed matrix identities match
the literal native action and square words of the order-eight actor.
Source: Aschbacher–Smith J.5.4, printed pp.445–446. -/

@[expose] public section
open Subgroup Matrix Theory.GroupTheory
noncomputable section
namespace Tits.Max4Outer.Mixed
open Max4Projective GorensteinWalter

def sigma : F ≃+* F := starRingAut

theorem sigma_apply (x : F) : sigma x=⟨x.re+x.im,-x.im⟩ := by
  change star x=_
  ext <;> simp [QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]

theorem sigma_square : sigma^2=1 := by
  ext x : 1
  exact star_star x

theorem sigma_ne : sigma≠1 := by
  intro he
  have h := congrArg (fun f : F ≃+* F => f ⟨0,1⟩) he
  have hn : sigma ⟨0,1⟩≠(⟨0,1⟩ : F) := by decide +kernel
  exact hn h

theorem sigma_order : orderOf sigma=2 := orderOf_eq_prime_iff.mpr ⟨sigma_square,sigma_ne⟩

instance fieldOdd : Fact (IsOddPrimePower (Nat.card F)) := ⟨by
  rw [field_card]
  exact ⟨5,2,by decide,by decide,by decide,rfl⟩⟩

def code (i : Fin 2) (b : Bool) : Fin 4 :=
  if b then ⟨i.val,by omega⟩ else ⟨i.val+2,by omega⟩

def unsigned (w : List (Fin 2 × Bool)) : List (Fin 4) := w.map (fun t=>code t.1 t.2)

def slGen : Fin 2 → SL := ![a,b]

def slWord (w : List (Fin 2 × Bool)) : SL :=
  evalWord (fun i=>(raw0Gen i).sl (raw0Gen_det i)) (unsigned w)

def rawWord (w : List (Fin 2 × Bool)) : Raw := evalRaw raw0Gen (unsigned w)

theorem slLetter (i : Fin 2) (b : Bool) : (raw0Gen (code i b)).sl (raw0Gen_det _)=
    if b then slGen i else (slGen i)⁻¹ := by
  fin_cases i <;> cases b
  · apply Subtype.ext
    change (raw0Gen 2).matrix=(raw0Gen 0).matrix.adjugate
    decide +kernel
  · rfl
  · apply Subtype.ext
    change (raw0Gen 3).matrix=(raw0Gen 1).matrix.adjugate
    decide +kernel
  · rfl

theorem slWord_eq (w : List (Fin 2 × Bool)) : slWord w=Max4Outer.eval slGen w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    rcases t with ⟨i,b⟩
    change (raw0Gen (code i b)).sl (raw0Gen_det _)*slWord w=_
    rw [slLetter,ih]
    rfl

theorem slWord_matrix (w : List (Fin 2 × Bool)) : (slWord w).val=(rawWord w).matrix :=
  (evalRaw_matrix raw0Gen raw0Gen_det (unsigned w)).symm

def matrixRaw : Raw := ⟨1,⟨0,1⟩,⟨1,4⟩,⟨2,2⟩⟩
def matrix := matrixRaw.matrix

theorem matrix_det : matrix.det=(⟨0,2⟩ : F) := by decide +kernel

theorem matrix_det_ne : matrix.det≠0 := by rw [matrix_det]; decide +kernel

theorem matrix_det_not_square : ¬ IsSquare matrix.det := by
  rintro ⟨x,hx⟩
  have h : ∀ x : F, x*x≠(⟨0,2⟩ : F) := by decide +kernel
  exact h x (hx.symm.trans matrix_det)

def M : GeneralLinearGroup (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero matrix matrix_det_ne

def rawStar (r : Raw) : Raw := ⟨sigma r.a,sigma r.b,sigma r.c,sigma r.d⟩

theorem rawStar_matrix (r : Raw) : (rawStar r).matrix=r.matrix.map sigma := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem action_matrix (i : Fin 2) : matrix*(slGen i).val.map sigma=
    if i=0 then -((slWord (actionWord i)).val*matrix) else (slWord (actionWord i)).val*matrix := by
  rw [slWord_matrix]
  fin_cases i
  all_goals apply Matrix.ext
  all_goals intro i j
  all_goals fin_cases i <;> fin_cases j <;> decide +kernel

def inverseSquareWord : List (Fin 2 × Bool) := FreeGroup.invRev squareWord

theorem square_matrix : matrix*(matrix.map sigma)=
    (⟨1,3⟩ : F) • (slWord inverseSquareWord).val := by
  rw [slWord_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

end Tits.Max4Outer.Mixed
