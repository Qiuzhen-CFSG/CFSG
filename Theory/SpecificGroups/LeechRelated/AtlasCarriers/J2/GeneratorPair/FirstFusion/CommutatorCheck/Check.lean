module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Range

/-!
# The finite J₂ commutator test

For each published product, test its cube and the seventh power of its
product with `t` on points 0–3. A failed test contradicts the corresponding
group equality. If all eight point tests pass, check the fourth power of
`t*y*t*y*y` on every point. The soundness proof uses `y³ = 1` to replace
`y*y` by `y⁻¹`. Computations are certified in `Pairs0`–`Pairs2`.
Source: the actual ATLAS degree-100 carrier; GLS3, Table 5.3g motivates the
parent first-generator fusion argument.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck

def pairValue (i : Fin 1920) (j : Fin 315) (p : Fin 100) : Fin 100 :=
  centralValue i (repValue j p)

def involutionValue (p : Fin 100) : Fin 100 := OrbitData.value 0 p

def shortTest (y : Fin 100 → Fin 100) : Bool :=
  checkFin fun p : Fin 4 =>
    decide (y^[3] (p.castLE (by decide)) = p.castLE (by decide)) &&
    decide ((fun q => involutionValue (y q))^[7] (p.castLE (by decide)) =
      p.castLE (by decide))

def fourthTest (y : Fin 100 → Fin 100) : Bool :=
  checkFin fun p : Fin 100 => decide
    ((fun q => involutionValue (y (involutionValue (y (y q)))) )^[4] p = p)

def checkPair (i : Fin 1920) (j : Fin 315) : Bool :=
  let y := pairValue i j
  !shortTest y || fourthTest y

def rowCheck (i : Fin 1920) : Bool :=
  checkFin (fun j : Fin 315 => checkPair i j)

def checkRows (lo count : Nat) : Bool := checkRange rowCheck lo count

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck
