module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic

/-!
# Literal coordinates for the signed Ree simple blocks

The end-node block has the word `x₀(t)x₃(t^θ)`. Writing α and β for the
middle long and short simple roots, its word is
`x_α(t)x_β(t^θ)x_{α+2β}(u)x_{α+β}(t*t^θ+u^θ)`, with `θ = 2^m`.
Negating all roots gives the negative blocks. These are precisely the
type VI and type V words of GLS3, Table 2.4, in
`refs/KGroup/GLS3/chapter2.tex`.

`SuzukiCoordinates` states the remaining middle-block matrix and intersection
calculations: membership, injectivity, coverage of both full fixed
intersections, and the nonabelian product law. It is an explicit proof
obligation, not a construction axiom. The linear block is established in
`LinearCoordinates`. Field naturality follows from the integral root curves.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds
variable {m : ℕ}
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The inverse Tits power occurring on a long root in `d.twist_root`. -/
def theta (m : ℕ) : CoefficientField m →+* CoefficientField m :=
  iterateFrobenius (CoefficientField m) 2 m

theorem theta_apply (t : CoefficientField m) : theta m t = t ^ (2 ^ m) := rfl

def signedRoot (positive : Bool) (r : F4Chevalley.Root) : F4Chevalley.Root :=
  if positive then r else -r

def linearRoots (positive : Bool) : Fin 2 → F4Chevalley.Root :=
  ![signedRoot positive (typeF4SimpleRootIndex 0),
    signedRoot positive (typeF4SimpleRootIndex 3)]

/-- Long, short, high, mixed: the order in Table 2.4, type V. -/
def suzukiRoots (positive : Bool) : Fin 4 → F4Chevalley.Root :=
  ![signedRoot positive (typeF4SimpleRootIndex 1),
    signedRoot positive (typeF4SimpleRootIndex 2),
    signedRoot positive (typeF4RootPairing.reflectionPerm
      (typeF4SimpleRootIndex 2) (typeF4SimpleRootIndex 1)),
    signedRoot positive (typeF4RootPairing.reflectionPerm
      (typeF4SimpleRootIndex 1) (typeF4SimpleRootIndex 2))]

def linearWord (m : ℕ) (positive : Bool) (t : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (linearRoots positive 0) t *
    rootGeneratorInGroup m (linearRoots positive 1) (theta m t)

def suzukiWord (m : ℕ) (positive : Bool) (t u : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (suzukiRoots positive 0) t *
    rootGeneratorInGroup m (suzukiRoots positive 1) (theta m t) *
    rootGeneratorInGroup m (suzukiRoots positive 2) u *
    rootGeneratorInGroup m (suzukiRoots positive 3) (t * theta m t + theta m u)

theorem linearWord_coe (positive : Bool) (t : CoefficientField m) :
    (linearWord m positive t).val =
      F4Chevalley.rootCurve (linearRoots positive 0) t *
        F4Chevalley.rootCurve (linearRoots positive 1) (theta m t) := rfl

theorem suzukiWord_coe (positive : Bool) (t u : CoefficientField m) :
    (suzukiWord m positive t u).val =
      F4Chevalley.rootCurve (suzukiRoots positive 0) t *
        F4Chevalley.rootCurve (suzukiRoots positive 1) (theta m t) *
        F4Chevalley.rootCurve (suzukiRoots positive 2) u *
        F4Chevalley.rootCurve (suzukiRoots positive 3) (t * theta m t + theta m u) := rfl

/-- Both signed Suzuki coordinates must cover the actual intersections, with no omitted central parameter. -/
structure SuzukiCoordinates (d : LocalBlockInput m) : Prop where
  suzuki_fixed : ∀ positive t u, suzukiWord m positive t u ∈ d.fixedGroup
  suzuki_mem : ∀ positive t u,
    suzukiWord m positive t u ∈ splitSimpleBlock m .suzuki positive
  suzuki_injective : ∀ positive,
    Function.Injective (fun p : CoefficientField m × CoefficientField m =>
      suzukiWord m positive p.1 p.2)
  suzuki_cover : ∀ positive (x : d.fixedGroup), x ∈ simpleBlock d .suzuki positive →
    ∃ t u, suzukiWord m positive t u = x.val
  suzuki_mul : ∀ positive t u v w,
    suzukiWord m positive t u * suzukiWord m positive v w =
      suzukiWord m positive (t + v) (u + w + (theta m t) ^ 2 * v)

theorem theta_field (σ : CoefficientField m ≃+* CoefficientField m)
    (t : CoefficientField m) : σ (theta m t) = theta m (σ t) := map_pow σ t _

theorem matrixFieldMap_root (σ : CoefficientField m ≃+* CoefficientField m)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    matrixFieldMap σ (F4Chevalley.rootCurve r t) = F4Chevalley.rootCurve r (σ t) :=
  rootCurve_map m σ.toRingHom r t

theorem matrixFieldMap_linearWord (σ : CoefficientField m ≃+* CoefficientField m)
    (positive : Bool) (t : CoefficientField m) :
      matrixFieldMap σ (linearWord m positive t).val = (linearWord m positive (σ t)).val := by
  simp only [linearWord_coe, map_mul, matrixFieldMap_root, theta_field]

theorem matrixFieldMap_suzukiWord (σ : CoefficientField m ≃+* CoefficientField m)
    (positive : Bool) (t u : CoefficientField m) :
    matrixFieldMap σ (suzukiWord m positive t u).val =
      (suzukiWord m positive (σ t) (σ u)).val := by
  simp only [suzukiWord_coe, map_mul, matrixFieldMap_root, map_add, theta_field]
end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
end
