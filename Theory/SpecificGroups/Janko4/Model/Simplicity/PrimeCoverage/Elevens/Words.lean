module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction

/-!
# Explicit words for the proposed Sylow eleven subgroup of J₄

`normalizerWords` transcribes the ATLAS straight-line program J4G1-max7W1,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max7W1
(retrieved 2026-10-03; ATLAS authors R. A. Wilson, S. J. Nickerson and J. N. Bray;
individual program contributor not recorded).
The output registers 1 and 2 give the words `u` and `v` below. The proposed
Sylow generators are `x = (u * v ^ 15) ^ 2`, `y = v⁻¹ * x * v`, and their
commutator `z = x⁻¹ * y⁻¹ * x * y`.

This module only defines words and a generated subgroup. In particular, it
asserts neither the ATLAS subgroup structure nor any unverified matrix identity.
The intended proof certifies the 1331 normal forms and the normalizer action,
then connects the central and noncentral cyclic representatives to the source
words at indices 5 and 6 of `primeRepresentative`.
-/

@[expose] public section

namespace Janko4.Simplicity.Elevens

/-- Outputs of the ATLAS program, in register order 1, 2. -/
def normalizerWords {G : Type*} [Group G] (a b : G) : G × G :=
  let t1 := a * b
  let t2 := t1 * b
  let t3 := t1 * t2
  let t4 := t1 * t3
  let t5 := t4 * t2
  let t6 := t2 ^ 4
  let t7 := t5 ^ 8
  let t8 := t7⁻¹
  let t9 := t8 * t6
  let t10 := t9 * t7
  let t11 := a * t10
  let t12 := t11 * t10
  let t13 := t12 ^ 3
  let t14 := t11 * t11
  let t15 := t13 * t14
  let t16 := t11 ^ 6
  let t17 := t16 * t15
  let t18 := t17 ^ 20
  let t19 := t18 * b
  let t20 := b * t18
  let t21 := t20⁻¹
  let t22 := t21 * t19
  let t23 := t22 ^ 3
  let t24 := t17 * t23
  let t25 := t17 * t24
  let t26 := t25 ^ 7
  let t27 := t17⁻¹
  let t28 := t27 * t23
  let t29 := t23 * t28
  let t30 := t17 ^ 8
  let t31 := t30 * t29
  let t32 := t31⁻¹
  let t33 := a * t17
  let t34 := t32 * t26
  let t35 := t34 * t31
  (t35, t33)

/-- The proposed noncentral element of order eleven. -/
def localX {G : Type*} [Group G] (a b : G) : G :=
  let uv := normalizerWords a b
  (uv.1 * uv.2 ^ 15) ^ 2

/-- A second proposed Sylow generator. -/
def localY {G : Type*} [Group G] (a b : G) : G :=
  (normalizerWords a b).2⁻¹ * localX a b * (normalizerWords a b).2

/-- The commutator, proposed to generate the center of the Sylow subgroup. -/
def localZ {G : Type*} [Group G] (a b : G) : G :=
  (localX a b)⁻¹ * (localY a b)⁻¹ * localX a b * localY a b

/-- Candidate cyclic representatives, central first and noncentral second. -/
def localRepresentative {G : Type*} [Group G] (a b : G) : Fin 2 → G :=
  ![localZ a b, localX a b]

/-- The concrete subgroup whose order and fusion are certified separately. -/
def localSubgroup (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Subgroup Model :=
  Subgroup.closure {localX (a hA) (b hB), localY (a hA) (b hB)}

end Janko4.Simplicity.Elevens
