module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeXYArithmetic.Reduction

/-!
# Kernel checks separated at multiplicity pairs

The finite search is unchanged: `checkX_eq` and `checkY_eq` identify the pairwise
checks with the original searches definitionally. Separating the closed checks
at each pair lets the kernel release its reduction cache between computations.
The constant-polynomial row measured 7.9 GiB as one computation and 5.1 GiB
when checked by pairs. No computed candidate is assumed: all closed results
are proved by kernel reduction and the selected-row lists are checked in Lean.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY

@[expose] public def checkXPair (p : ℤ × (ℤ × ℤ)) (s t : ℤ × ℤ) : Bool :=
  if 1+p.2.1-s.1+t.1=16 then
    (denominators p.1 (p.1+1)).all fun P =>
      (rootsAt (p.2.1^2+p.1)
        (-p.2.1^2*p.1-p.2.1^2-s.1^2*p.1+t.1^2*p.1-p.1^2-p.1)
        (s.1^2*p.1*(p.1+1)-P) s.2).all fun y =>
        candidateCheck p.1 y (y-p.1-1) p.2 s t
  else true

@[expose] public def checkYPair (p : ℤ × (ℤ × ℤ)) (r t : ℤ × ℤ) : Bool :=
  if 1+r.1-p.2.1+t.1=16 then
    (denominators p.1 (p.1-1)).all fun P =>
      (rootsAt (p.2.1^2-p.1)
        (-r.1^2*p.1-p.2.1^2*p.1+p.2.1^2+t.1^2*p.1+p.1^2-p.1)
        (r.1^2*p.1*(p.1-1)-P) r.2).all fun x =>
        candidateCheck x p.1 (p.1-1-x) r p.2 t
  else true

public theorem checkX_eq (p : ℤ × (ℤ × ℤ)) :
    checkX p = (rows (-329) (-7)).all (fun s =>
      (rows 127 1).all (fun t => checkXPair p s t)) := rfl

public theorem checkY_eq (p : ℤ × (ℤ × ℤ)) :
    checkY p = (rows 78 2).all (fun r =>
      (rows 127 1).all (fun t => checkYPair p r t)) := rfl

public theorem checkXPair_of_value_ne {p : ℤ × (ℤ × ℤ)} {s t : ℤ × ℤ}
    (h : 1+p.2.1-s.1+t.1 ≠ 16) : checkXPair p s t = true := by
  exact if_neg h

public theorem checkYPair_of_value_ne {p : ℤ × (ℤ × ℤ)} {r t : ℤ × ℤ}
    (h : 1+r.1-p.2.1+t.1 ≠ 16) : checkYPair p r t = true := by
  exact if_neg h

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY
