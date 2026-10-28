module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.Coordinates

/-!
# Parameter-dependent matrices on all 52 F₄ coordinates

The coordinates are the four simple Cartan vectors followed by the 48 roots
in the proved enumeration `AmbientComputation.basisEquiv`. The two incidence
tables specify the coefficients of t and t² in the proposed middle simple
root matrices. Their order is long+, short+, long−, short−. The reflected
high and mixed roots are defined by the literal simple Weyl conjugations.

These are explicit comparison matrices over every coefficient field, including
all Cartan columns. `simpleComparison` in `Ambient.Comparison` identifies them with the actual
Geck root curves coefficient by coefficient. `GaussIdentity` states the remaining
finite matrix calculation. `Ambient` transfers these two inputs to the requested
split-group equation. No four-dimensional faithfulness assertion is involved.

Source: the integral simple-root and divided-power formulas in
`RootPairing.IntegralGeckConstruction`, and GLS3 Table 2.4 type V,
`refs/KGroup/GLS3/chapter2.tex`. At a root column, the linear coefficient is
p+1 and the quadratic coefficient is (p+2 choose 2), reduced modulo two;
the Cartan columns use the absolute Cartan entries. No binary specialization
is used to infer equality for arbitrary parameters.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient
open BlockParameters.FieldRecovery
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

/-- Positions with coefficient one in degree 1, in signed simple-root order. -/
def linearSupport : Fin 4 → List (Fin 52 × Fin 52) :=
  ![[(1,26), (6,5), (9,8), (13,12), (17,16), (20,19), (23,22), (27,25), (29,0), (30,28), (33,32), (36,35), (39,38), (43,42), (47,46), (50,49)],
    [(2,27), (7,6), (12,11), (14,13), (16,15), (18,17), (21,20), (25,24), (28,1), (28,3), (30,29), (34,33), (38,37), (40,39), (42,41), (44,43), (48,47)],
    [(1,29), (5,6), (8,9), (12,13), (16,17), (19,20), (22,23), (25,27), (26,0), (28,30), (32,33), (35,36), (38,39), (42,43), (46,47), (49,50)],
    [(2,28), (7,8), (11,12), (13,14), (15,16), (17,18), (21,22), (25,26), (27,1), (27,3), (30,31), (34,35), (37,38), (39,40), (41,42), (43,44), (48,49)]]

/-- Positions with coefficient one in degree 2, in signed simple-root order. -/
def quadraticSupport : Fin 4 → List (Fin 52 × Fin 52) :=
  ![[(29,26)],
    [(8,6), (22,20), (26,24), (28,27), (31,29), (35,33), (49,47)],
    [(26,29)],
    [(6,8), (20,22), (24,26), (27,28), (29,31), (33,35), (47,49)]]

/-- The index of a signed middle simple root in the coefficient tables. -/
def simpleIndex (p : Bool) (i : Fin 2) : Fin 4 :=
  if p then ![0,1] i else ![2,3] i

/-- An incidence matrix over an arbitrary coefficient ring. -/
def incidence {R : Type*} [Zero R] [One R] (s : List (Fin 52 × Fin 52)) :
    Matrix (Fin 52) (Fin 52) R := fun r c => if (r,c) ∈ s then 1 else 0

/-- The proposed simple root curve, with its full quadratic term retained. -/
def simpleMatrix {R : Type*} [CommRing R] (p : Bool) (i : Fin 2) (t : R) :
    Matrix (Fin 52) (Fin 52) R :=
  1 + t • incidence (linearSupport (simpleIndex p i)) +
    t^2 • incidence (quadraticSupport (simpleIndex p i))

/-- The three-factor Weyl word at a middle simple root. -/
def weylMatrix {R : Type*} [Field R] (i : Fin 2) (t : R) :
    Matrix (Fin 52) (Fin 52) R :=
  simpleMatrix true i t * simpleMatrix false i t⁻¹ * simpleMatrix true i t

/-- The representative at parameter one. -/
def reflectionMatrix {R : Type*} [Field R] (i : Fin 2) :
    Matrix (Fin 52) (Fin 52) R := weylMatrix i 1

/-- Long, short, high, mixed root matrices. The last two use exact Weyl words. -/
def rootMatrix {R : Type*} [Field R] (p : Bool) (i : Fin 4) (t : R) :
    Matrix (Fin 52) (Fin 52) R :=
  ![simpleMatrix p 0 t, simpleMatrix p 1 t,
    reflectionMatrix 1 * simpleMatrix p 0 t * reflectionMatrix 1,
    reflectionMatrix 0 * simpleMatrix p 1 t * reflectionMatrix 0] i

/-- The literal four-root Suzuki word on the complete coordinate set. -/
def wordMatrix {m : ℕ} (p : Bool) (t u : CoefficientField m) :
    Matrix (Fin 52) (Fin 52) (CoefficientField m) :=
  rootMatrix p 0 t * rootMatrix p 1 (theta m t) * rootMatrix p 2 u *
    rootMatrix p 3 (t * theta m t + theta m u)

/-- The literal panel Weyl word [1,2,1,2]. -/
def panelMatrix {R : Type*} [Field R] : Matrix (Fin 52) (Fin 52) R :=
  reflectionMatrix 0 * reflectionMatrix 1 * reflectionMatrix 0 * reflectionMatrix 1

/-- The literal long coroot at π(n), followed by the short coroot at n. -/
def torusMatrix {m : ℕ} (n : (CoefficientField m)ˣ) :
    Matrix (Fin 52) (Fin 52) (CoefficientField m) :=
  (weylMatrix 0 (titsEnd m (n : CoefficientField m)) * reflectionMatrix 0) *
    (weylMatrix 1 (n : CoefficientField m) * reflectionMatrix 1)

/-- Relabel all coordinates; this is an isomorphism of full matrix algebras. -/
def fullMatrixEquiv (m : ℕ) :
    Matrix (Fin 52) (Fin 52) (CoefficientField m) ≃+* MatrixCarrier m :=
  Matrix.reindexRingEquiv (CoefficientField m)
    Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation.basisEquiv

/-- The four full simple-root comparisons, for arbitrary field parameters. -/
def SimpleComparison (m : ℕ) : Prop :=
  ∀ (p : Bool) (i : Fin 2) (t : CoefficientField m),
    (F4Chevalley.rootCurve (signedRoot p (typeF4SimpleRootIndex (if i = 0 then 1 else 2))) t).val =
      fullMatrixEquiv m (simpleMatrix p i t)

/-- A finite calculation on every coordinate, independent of the ambient comparison. -/
def GaussIdentity (m : ℕ) : Prop :=
  ∀ (t u : CoefficientField m) (hn : norm t u ≠ 0),
    panelMatrix * wordMatrix false t u =
      wordMatrix false (negativeFirst t u) (negativeSecond t u) *
        torusMatrix (Units.mk0 (norm t u) hn) *
          wordMatrix true (positiveFirst t u) (positiveSecond t u)

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient
end
