module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddSevenTernaryCover.Geometry

/-!
# Explicit minus-six complements in the higher ternary orthogonal spaces

The ternary minus-six space plus a negative line is the odd-seven space.
Adding a second negative line gives the split-eight space by the coordinates
(z,t) ↦ (z+t,z−t). Additional hyperbolic pairs give every higher odd or split
space. For the minus family, splitting hyperbolic pairs directly retains the
original anisotropic plane and its actual chosen parameter.

Every isometry uses the literal project quadratic forms. The displayed
complements are nonzero in the source ranges, so their fixed vectors prevent
nonidentity block elements from becoming scalar after projectivization.
Source: Aschbacher–Smith A.2.17 and I.2.1; GLS3 §2.7.
-/

open ClassicalOrthogonal.Fundamental.SplitOddBlocks
@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddSevenTernaryCover
variable {F : Type} [Field F]
variable {U V W : Type} [AddCommGroup U] [Module F U]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def prodAssocIsometry (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (S : QuadraticForm F W) :
    ((Q.prod R).prod S).IsometryEquiv (Q.prod (R.prod S)) where
  __ := LinearEquiv.prodAssoc F U V W
  map_app' _ := (add_assoc _ _ _).symm

variable [Finite F] [CharP F 3]

def oddHigherIsometry (hcard : Nat.card F = 3) (k : ℕ) :
    ((Minus.quadraticForm F 3).prod (negativeLine.prod (formD k F))).IsometryEquiv
      (formB (k+3) F) :=
  (prodAssocIsometry _ _ _).symm.trans
    (((spaceIsometry hcard).prod (QuadraticMap.IsometryEquiv.refl (formD k F))).trans
      ((QuadraticMap.IsometryEquiv.prodComm _ _).trans (splitBIsometry k 3).symm))

def oddPlusCoordinates : (VectorB 3 F × F) ≃ₗ[F] VectorD 4 F where
  toFun v := Sum.elim
    ![v.1.1 (.inl 0),v.1.1 (.inl 1),v.1.1 (.inl 2),v.1.2+v.2]
    ![v.1.1 (.inr 0),v.1.1 (.inr 1),v.1.1 (.inr 2),v.1.2-v.2]
  invFun v := ((Sum.elim (fun i => v (.inl i.castSucc)) (fun i => v (.inr i.castSucc)),
    (v (.inl 3)+v (.inr 3))/2), (v (.inl 3)-v (.inr 3))/2)
  left_inv v := by
    have h2 := ternary_two_ne_zero (F := F)
    apply Prod.ext
    · apply Prod.ext
      · funext i
        rcases i with i | i <;> fin_cases i <;> rfl
      · dsimp; field_simp; ring
    · dsimp; field_simp; ring
  right_inv v := by
    have h2 := ternary_two_ne_zero (F := F)
    funext i
    rcases i with i | i <;> fin_cases i <;> dsimp <;> try rfl
    all_goals field_simp; ring
  map_add' v w := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp <;> ring

def oddPlusIsometry : ((formB 3 F).prod negativeLine).IsometryEquiv (formD 4 F) where
  __ := oddPlusCoordinates (F := F)
  map_app' v := by
    change formD 4 F (oddPlusCoordinates v) = (formB 3 F).prod negativeLine v
    simp [formD_apply,formB_apply,negativeLine,oddPlusCoordinates,Fin.sum_univ_succ]
    ring

def plusEightIsometry (hcard : Nat.card F = 3) :
    ((Minus.quadraticForm F 3).prod (negativeLine.prod negativeLine)).IsometryEquiv
      (formD 4 F) :=
  (prodAssocIsometry _ _ _).symm.trans
    (((spaceIsometry hcard).prod (QuadraticMap.IsometryEquiv.refl negativeLine)).trans
      oddPlusIsometry)

def plusHigherIsometry (hcard : Nat.card F = 3) (k : ℕ) :
    ((Minus.quadraticForm F 3).prod
      ((negativeLine.prod negativeLine).prod (formD k F))).IsometryEquiv (formD (k+4) F) :=
  (prodAssocIsometry _ _ _).symm.trans
    (((plusEightIsometry hcard).prod (QuadraticMap.IsometryEquiv.refl (formD k F))).trans
      ((QuadraticMap.IsometryEquiv.prodComm _ _).trans (splitDIsometry k 4).symm))

def minusSplitCoordinates (k : ℕ) : Minus.Space F (2+(k+1)) ≃ₗ[F]
    Minus.Space F 2 × VectorD (k+1) F where
  toFun v := ((fun i => v.1 (Fin.castAdd (k+1) i), v.2),
    Sum.elim (fun i => (v.1 (Fin.natAdd 2 i)).1) (fun i => (v.1 (Fin.natAdd 2 i)).2))
  invFun v := (Fin.addCases v.1.1 (fun i => (v.2 (.inl i),v.2 (.inr i))),v.1.2)
  left_inv v := by
    apply Prod.ext
    · funext i
      exact Fin.addCases_castAdd_natAdd v.1 i
    · rfl
  right_inv v := by
    apply Prod.ext
    · apply Prod.ext
      · funext i; simp
      · rfl
    · funext i; rcases i with i | i <;> simp
  map_add' a v := by
    apply Prod.ext
    · rfl
    · funext i; cases i <;> rfl
  map_smul' a v := by
    apply Prod.ext
    · rfl
    · funext i; cases i <;> rfl

def minusHigherIsometry (k : ℕ) :
    ((Minus.quadraticForm F 3).prod (formD (k+1) F)).IsometryEquiv
      (Minus.quadraticForm F (k+4)) := by
  unfold Minus.quadraticForm
  rw [show k+4-1=2+(k+1) by omega]
  exact QuadraticMap.IsometryEquiv.symm {
    toLinearEquiv := minusSplitCoordinates k
    map_app' := by
      intro v
      simp only [Minus.form_apply,QuadraticMap.prod_apply,
        formD_apply,minusSplitCoordinates,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_add]
      ring }

end ClassicalOrthogonal.OddSevenTernaryCover
