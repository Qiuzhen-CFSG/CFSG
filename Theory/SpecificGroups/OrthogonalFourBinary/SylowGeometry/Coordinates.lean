module

public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry
public import Theory.SpecificGroups.OrthogonalFourBinary.NonsingularSix
public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines.Lines

/-!
# Coordinates on all binary four-dimensional quadratic isometries

Each isometry is a pair of permutations of the two definite planes, followed
by their optional interchange. The existing order computation and a checked
injection certify that these 72 actual linear isometries exhaust the group.
Small coordinate evaluation formulas keep subsequent finite checks independent
of the implementation of linear equivalences.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the quadratic
space on printed pp.1121--1122 and its use in 15.3.66, printed p.1152.
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000
abbrev Code := LineCode × LineCode × Bool

def planeEval (i : LineCode) (x : Plane) : Plane :=
  let y := if i.2 = 0 then x else (x.2, x.1)
  if i.1 = 0 then y else if i.1 = 1 then (y.2, y.1 + y.2) else (y.1 + y.2, y.1)
theorem planePermutation_eval : ∀ i : LineCode, ∀ x : Plane,
    planePermutation i x = planeEval i x := by decide +kernel

def eval (i : Code) (x : Space) : Space :=
  if i.2.2 then (planeEval i.1 x.2, planeEval i.2.1 x.1)
    else (planeEval i.1 x.1, planeEval i.2.1 x.2)
def candidate (i : Code) : Space ≃ₗ[F] Space :=
  (planePermutation i.1).prodCongr (planePermutation i.2.1) *
    (if i.2.2 then LinearEquiv.prodComm F Plane Plane else 1)
theorem candidate_eval (i : Code) (x : Space) : candidate i x = eval i x := by
  rcases i with ⟨i,j,b⟩
  cases b <;> exact Prod.ext (planePermutation_eval _ _) (planePermutation_eval _ _)
def q (x : Space) : F :=
  x.1.1*x.1.1 + x.1.1*x.1.2 + x.1.2*x.1.2 +
    (x.2.1*x.2.1 + x.2.1*x.2.2 + x.2.2*x.2.2)
theorem form_eval (x : Space) : form x = q x := rfl
theorem candidate_form (i : Code) (w : Space) :
    form (candidate i w) = form w := by
  rw [candidate_eval, form_eval, form_eval]
  exact (show ∀ i : Code, ∀ w : Space, q (eval i w) = q w by decide +kernel) i w
def codeMap (i : Code) : OrthogonalFourBinary.IsometryGroup :=
  ⟨candidate i, (mem_quadraticIsometrySubgroup form _).mpr (candidate_form i)⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem code_inj : ∀ i j : Code,
    (eval i ((1,0),(0,0)), eval i ((0,1),(0,0)),
      eval i ((0,0),(1,0)), eval i ((0,0),(0,1))) =
    (eval j ((1,0),(0,0)), eval j ((0,1),(0,0)),
      eval j ((0,0),(1,0)), eval j ((0,0),(0,1))) → i = j := by
  decide +kernel
theorem codeMap_bijective : Function.Bijective codeMap := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j h
    apply code_inj i j
    have he : candidate i = candidate j := congrArg Subtype.val h
    simp only [← candidate_eval, he]
  · rw [isometryGroup_card, Nat.card_eq_fintype_card]
    decide +kernel
noncomputable def codeEquiv : Code ≃ OrthogonalFourBinary.IsometryGroup :=
  Equiv.ofBijective codeMap codeMap_bijective


end OrthogonalFourBinary.SylowGeometry
