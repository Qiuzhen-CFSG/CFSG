module

public import Theory.SpecificGroups.Lyons.Atlas111SimplicitySetup
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product00
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product01
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product02
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product03
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product04
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product05
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product06
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product07
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product08
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product09
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product10
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product11
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product12
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product13
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product14
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product15
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product16
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Product17

/-!
# Three certified word relations in the concrete Lyons group

For the fixed ATLAS generators we prove `b^5 = 1`, `(ab)^14 = 1` and
`((ab)^3 b)^67 = 1`. Carry-free, kernel-checked row certificates establish
the intermediate matrix products. Short addition chains assemble the powers,
and the faithful matrix representation transfers the identities to LyonsGroup.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Ly/ (standard generators).
The original matrices and attribution are in `Atlas111Source/`; the independent
certificate generator is `Atlas111WordSource/Generate.py`.
These identities do not assume the ambient group's order or simplicity.
-/

namespace Lyons.Atlas111WordCertificate

private theorem square_power {M : Type*} [Monoid M] (x y z : M) (n : ℕ)
    (h : x ^ n = y) (hm : y * y = z) : x ^ (n * 2) = z :=
  (pow_mul x n 2).trans ((congrArg (fun t : M => t ^ 2) h).trans
    ((pow_two y).trans hm))

private theorem step_power {M : Type*} [Monoid M] (x y z : M) (n : ℕ)
    (h : x ^ n = y) (hm : y * x = z) : x ^ (n + 1) = z :=
  (pow_succ x n).trans ((congrArg (fun t : M => t * x) h).trans hm)

/-- The second source matrix satisfies the fifth-power identity. -/
public theorem matrixB_pow_five : atlasBMatrix ^ 5 = 1 := by
  have h2 : bMatrix ^ 2 = b2Matrix := (pow_two _).trans mul_b2
  have h4 : bMatrix ^ 4 = b4Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 2 h2 mul_b4
  have h5 : bMatrix ^ 5 = oneMatrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 4 h4 mul_b5
  exact (congrArg (fun t : AtlasMatrix => t ^ 5) bMatrix_eq.symm).trans
    (h5.trans oneMatrix_eq)

private theorem matrixAB_eq : atlasAMatrix * atlasBMatrix = abMatrix :=
  (congrArg₂ (fun x y : AtlasMatrix => x * y) aMatrix_eq.symm bMatrix_eq.symm).trans mul_ab

private theorem matrixAB_cube : abMatrix ^ 3 = ab3Matrix := by
  have h2 : abMatrix ^ 2 = ab2Matrix := (pow_two _).trans mul_ab2
  simpa only [Nat.reduceAdd] using step_power _ _ _ 2 h2 mul_ab3

/-- The product of the two source matrices satisfies the fourteenth-power identity. -/
public theorem matrixAB_pow_fourteen : (atlasAMatrix * atlasBMatrix) ^ 14 = 1 := by
  have h6 : abMatrix ^ 6 = ab6Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 3 matrixAB_cube mul_ab6
  have h7 : abMatrix ^ 7 = ab7Matrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 6 h6 mul_ab7
  have h14 : abMatrix ^ 14 = oneMatrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 7 h7 mul_ab14
  exact (congrArg (fun t : AtlasMatrix => t ^ 14) matrixAB_eq).trans
    (h14.trans oneMatrix_eq)

private theorem matrixWord_eq :
    (atlasAMatrix * atlasBMatrix) ^ 3 * atlasBMatrix = wMatrix :=
  (congrArg₂ (fun x y : AtlasMatrix => x * y)
    ((congrArg (fun t : AtlasMatrix => t ^ 3) matrixAB_eq).trans matrixAB_cube)
    bMatrix_eq.symm).trans mul_w

/-- The ATLAS word `abababb` satisfies the sixty-seventh-power identity. -/
public theorem matrixWord_pow_sixty_seven :
    ((atlasAMatrix * atlasBMatrix) ^ 3 * atlasBMatrix) ^ 67 = 1 := by
  have h2 : wMatrix ^ 2 = w2Matrix := (pow_two _).trans mul_w2
  have h4 : wMatrix ^ 4 = w4Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 2 h2 mul_w4
  have h8 : wMatrix ^ 8 = w8Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 4 h4 mul_w8
  have h16 : wMatrix ^ 16 = w16Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 8 h8 mul_w16
  have h32 : wMatrix ^ 32 = w32Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 16 h16 mul_w32
  have h33 : wMatrix ^ 33 = w33Matrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 32 h32 mul_w33
  have h66 : wMatrix ^ 66 = w66Matrix := by
    simpa only [Nat.reduceMul] using square_power _ _ _ 33 h33 mul_w66
  have h67 : wMatrix ^ 67 = oneMatrix := by
    simpa only [Nat.reduceAdd] using step_power _ _ _ 66 h66 mul_w67
  exact (congrArg (fun t : AtlasMatrix => t ^ 67) matrixWord_eq).trans
    (h67.trans oneMatrix_eq)

end Lyons.Atlas111WordCertificate

namespace Lyons.SimplicityCertificate

/-- The second fixed generator satisfies the fifth-power identity. -/
public theorem generatorB_pow_five : generatorB ^ 5 = 1 := by
  apply matrixRepresentation_injective
  simp only [map_pow, map_one, matrixRepresentation_generatorB]
  exact Atlas111WordCertificate.matrixB_pow_five

/-- The product of the fixed generators satisfies the fourteenth-power identity. -/
public theorem generatorAB_pow_fourteen : (generatorA * generatorB) ^ 14 = 1 := by
  apply matrixRepresentation_injective
  simp only [map_pow, map_mul, map_one, matrixRepresentation_generatorA,
    matrixRepresentation_generatorB]
  exact Atlas111WordCertificate.matrixAB_pow_fourteen

/-- The fixed word `abababb` satisfies the sixty-seventh-power identity. -/
public theorem perfectWord_pow_sixty_seven : perfectWord ^ 67 = 1 := by
  apply matrixRepresentation_injective
  simp only [perfectWord, map_pow, map_mul, map_one, matrixRepresentation_generatorA,
    matrixRepresentation_generatorB]
  exact Atlas111WordCertificate.matrixWord_pow_sixty_seven

end Lyons.SimplicityCertificate
