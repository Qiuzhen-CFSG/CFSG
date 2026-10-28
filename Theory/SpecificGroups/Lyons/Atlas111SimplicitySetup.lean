module

public import Theory.SpecificGroups.Lyons.Atlas111Group
public import Theory.SpecificGroups.Lyons.Atlas111OrderSetup
public import Theory.GroupTheory.NormalGeneratorCentralizerSimplicity
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Normal generation and perfectness for the concrete Lyons carrier

Write `a, b` for the fixed ATLAS matrices. The relations `b⁵ = (ab)¹⁴ = 1`
make `a` a normal generator: killing it gives coprime orders for `b`.
In an abelian image, `a² = 1` also makes `b¹⁴ = 1`, hence kills `b`.
The relation `((ab)³b)⁶⁷ = 1` then kills `a`, proving perfectness.

The involution identity is proved from the stored inverse. The other three
matrix identities remain explicit hypotheses here. We use only individual
relations, without claiming that they form a defining presentation.
The generator centralizer is defined independently of them, so its local
structure can be certified in a separate module.

Source: ATLAS of Finite Group Representations, Lyons standard generators,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Ly/ . Matrix provenance is in
`Atlas111Source/`. The argument follows the same elementary quotient method as
`Theory.SpecificGroups.HaradaNorton.Simplicity.Reduction`.
-/

namespace Lyons.SimplicityCertificate

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem matrixA_eq_inverse : atlasAMatrix = atlasAInvMatrix := by
  decide +kernel

/-- The first fixed matrix generator is an involution. -/
public theorem generatorA_sq : generatorA ^ 2 = 1 := by
  rw [pow_two]
  apply matrixRepresentation_injective
  simp only [map_mul, map_one, matrixRepresentation_generatorA]
  conv_lhs => rhs; rw [matrixA_eq_inverse]
  exact atlasAMatrix_mul_inverse

/-- Its already certified failure to commute rules out the identity. -/
public theorem generatorA_ne_one : generatorA ≠ 1 := by
  intro h
  apply generators_not_commute
  simp only [h, one_mul, mul_one]

/-- The first fixed generator has order exactly two. -/
public theorem orderOf_generatorA : orderOf generatorA = 2 :=
  orderOf_eq_prime generatorA_sq generatorA_ne_one

/-- The centralizer of the first fixed matrix generator. -/
@[expose] public def generatorCentralizer : Subgroup LyonsGroup :=
  Subgroup.centralizer {generatorA}

/-- The ATLAS word `abababb`. -/
@[expose] public def perfectWord : LyonsGroup :=
  (generatorA * generatorB) ^ 3 * generatorB

/-- Homomorphisms out of the concrete carrier are determined by its generators. -/
public theorem hom_ext {G : Type*} [Group G] {f g : LyonsGroup →* G}
    (ha : f generatorA = g generatorA) (hb : f generatorB = g generatorB) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense OrderCertificate.closure_generators
  intro x hx
  rcases hx with rfl | hx
  · exact ha
  · rcases hx with rfl
    exact hb

/-- Killing `a` kills the whole group under the two specified word identities. -/
public theorem hom_eq_one_of_generatorA_eq_one {G : Type*} [Group G]
    (hb5 : generatorB ^ 5 = 1) (hab14 : (generatorA * generatorB) ^ 14 = 1)
    (f : LyonsGroup →* G) (ha : f generatorA = 1) : f = 1 := by
  have hb5' : f generatorB ^ 5 = 1 := by
    simpa only [map_pow, map_one] using congrArg f hb5
  have hb14' : f generatorB ^ 14 = 1 := by
    simpa only [map_pow, map_mul, map_one, ha, one_mul] using congrArg f hab14
  have hb : f generatorB = 1 :=
    (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 5 14)).mp ⟨hb5', hb14'⟩
  exact hom_ext ha hb

/-- The first generator normally generates, conditional on the displayed relations. -/
public theorem normal_eq_top_of_generatorA_mem
    (hb5 : generatorB ^ 5 = 1) (hab14 : (generatorA * generatorB) ^ 14 = 1)
    (N : Subgroup LyonsGroup) [N.Normal] (ha : generatorA ∈ N) : N = ⊤ := by
  have hf := hom_eq_one_of_generatorA_eq_one hb5 hab14 (QuotientGroup.mk' N)
    ((QuotientGroup.eq_one_iff _).mpr ha)
  apply top_unique
  intro x _
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun hf x

/-- The four ATLAS relations annihilate every commutative image. -/
public theorem hom_to_commGroup_eq_one {G : Type*} [CommGroup G]
    (hb5 : generatorB ^ 5 = 1)
    (hab14 : (generatorA * generatorB) ^ 14 = 1) (hw67 : perfectWord ^ 67 = 1)
    (f : LyonsGroup →* G) : f = 1 := by
  have ha2' : f generatorA ^ 2 = 1 := by
    simpa only [map_pow, map_one] using congrArg f generatorA_sq
  have hb5' : f generatorB ^ 5 = 1 := by
    simpa only [map_pow, map_one] using congrArg f hb5
  have hb14' : f generatorB ^ 14 = 1 := by
    have h := congrArg f hab14
    simpa only [map_pow, map_mul, map_one, mul_pow,
      pow_eq_pow_mod 14 ha2', Nat.reduceMod, pow_zero, one_mul] using h
  have hb : f generatorB = 1 :=
    (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 5 14)).mp ⟨hb5', hb14'⟩
  have hwf : f perfectWord = f generatorA := by
    simp only [perfectWord, map_mul, map_pow, hb, mul_one,
      pow_eq_pow_mod 3 ha2', Nat.reduceMod, pow_one]
  have ha67 : f generatorA ^ 67 = 1 := by
    simpa only [map_pow, map_one, hwf] using congrArg f hw67
  have ha : f generatorA = 1 :=
    (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 2 67)).mp ⟨ha2', ha67⟩
  exact hom_ext ha hb

/-- Perfectness follows from actual identities of the fixed matrices. -/
public theorem isPerfect_of_relations
    (hb5 : generatorB ^ 5 = 1)
    (hab14 : (generatorA * generatorB) ^ 14 = 1) (hw67 : perfectWord ^ 67 = 1) :
    Group.IsPerfect LyonsGroup where
  commutator_eq_top := by
    rw [← Abelianization.ker_of, hom_to_commGroup_eq_one hb5 hab14 hw67 Abelianization.of]
    simp

/-- The centralizer is proper, by the already certified noncommutativity. -/
public theorem generatorCentralizer_ne_top : generatorCentralizer ≠ ⊤ := by
  intro h
  have hb : generatorB ∈ generatorCentralizer := by rw [h]; trivial
  exact generators_not_commute (Subgroup.mem_centralizer_singleton_iff.mp hb).symm

end Lyons.SimplicityCertificate
