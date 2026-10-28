module

public import Theory.SpecificGroups.HaradaNorton.Generators
public import Theory.GroupTheory.NormalGeneratorCentralizerSimplicity
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Normal generation and perfectness from HN word identities

The certified matrices already give `a² = b³ = 1` and generation. The additional
relation `(ab)²² = 1` makes `a` a normal generator, since killing `a` gives both
`b³ = 1` and `b²² = 1`. In an abelian image, the class-25A word
`perfectWord = (ab)⁵b` reduces to `a⁵ b⁶ = a`. Its twenty-fifth-power relation
therefore kills `a` as well and proves perfectness.

The two extra matrix identities remain explicit hypotheses here. These are
individual relations, not a claim that the ATLAS semi-presentation is a defining
presentation. Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HN/,
standard generators and class-25A representative; matrix provenance is in
`../MatrixSources.md`.
-/

namespace HaradaNorton

/-- The ATLAS class-25A word, whose abelian image is the image of `a`. -/
@[expose] public def perfectWord : HN :=
  (a * b) ^ 5 * b

/-- Homomorphisms are determined by the two certified generators. -/
public theorem hom_ext {G : Type*} [Group G] {f g : HN →* G}
    (ha : f a = g a) (hb : f b = g b) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense closure_generators
  intro x hx
  rcases hx with rfl | hx
  · exact ha
  · rcases hx with rfl
    exact hb

/-- The relation `(ab)²² = 1` makes `a` a normal generator. -/
public theorem hom_eq_one_of_a_eq_one {G : Type*} [Group G]
    (hab : (a * b) ^ 22 = 1) (f : HN →* G) (ha : f a = 1) : f = 1 := by
  have hb3 : f b ^ 3 = 1 := by simpa only [map_pow, map_one] using congrArg f b_cube
  have hb22 : f b ^ 22 = 1 := by
    simpa only [map_pow, map_mul, map_one, ha, one_mul] using congrArg f hab
  have hb : f b = 1 := by
    rw [pow_eq_pow_mod 22 hb3] at hb22
    simpa using hb22
  exact hom_ext ha hb

/-- Every normal subgroup containing `a` is the whole group, provided `(ab)²² = 1`. -/
public theorem normal_eq_top_of_a_mem (hab : (a * b) ^ 22 = 1)
    (N : Subgroup HN) [N.Normal] (ha : a ∈ N) : N = ⊤ := by
  have hf := hom_eq_one_of_a_eq_one hab (QuotientGroup.mk' N)
    ((QuotientGroup.eq_one_iff _).mpr ha)
  apply top_unique
  intro x _
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun hf x

/-- Two ATLAS relations annihilate every commutative image. -/
public theorem hom_to_commGroup_eq_one {G : Type*} [CommGroup G]
    (hab : (a * b) ^ 22 = 1) (hw : perfectWord ^ 25 = 1) (f : HN →* G) : f = 1 := by
  have ha2 : f a ^ 2 = 1 := by simpa only [map_pow, map_one] using congrArg f a_sq
  have hb3 : f b ^ 3 = 1 := by simpa only [map_pow, map_one] using congrArg f b_cube
  have hwf : f perfectWord = f a := by
    simp only [perfectWord, map_mul, map_pow]
    calc
      _ = f a ^ 5 * f b ^ 6 := by simp only [pow_succ, pow_zero, one_mul]; ac_rfl
      _ = f a := by rw [pow_eq_pow_mod 5 ha2, pow_eq_pow_mod 6 hb3]; simp
  have ha25 : f a ^ 25 = 1 := by
    simpa only [map_pow, hwf, map_one] using congrArg f hw
  have ha : f a = 1 := by
    rw [pow_eq_pow_mod 25 ha2] at ha25
    simpa using ha25
  exact hom_eq_one_of_a_eq_one hab f ha

/-- Perfectness follows from the two specified ATLAS word identities. -/
public theorem isPerfect_of_relations (hab : (a * b) ^ 22 = 1) (hw : perfectWord ^ 25 = 1) :
    Group.IsPerfect HN where
  commutator_eq_top := by
    rw [← Abelianization.ker_of, hom_to_commGroup_eq_one hab hw Abelianization.of]
    simp

/-- The centralizer of the standard involution. -/
@[expose] public def generatorCentralizer : Subgroup HN := Subgroup.centralizer {a}

/-- The two certified units do not commute. -/
public theorem a_mul_b_ne_b_mul_a : a * b ≠ b * a := by
  intro h
  apply aMatrix_mul_bMatrix_ne
  simpa only [map_mul, matrixHom_a, matrixHom_b] using congrArg matrixHom h

/-- The first certified generator is nonidentity. -/
public theorem a_ne_one : a ≠ 1 := by
  intro h
  apply a_mul_b_ne_b_mul_a
  simp only [h, one_mul, mul_one]

/-- Nontriviality witnessed by the first generator. -/
public instance hn_nontrivial : Nontrivial HN := ⟨⟨a, 1, a_ne_one⟩⟩

/-- Noncommutativity makes the generator centralizer proper. -/
public theorem generatorCentralizer_ne_top : generatorCentralizer ≠ ⊤ := by
  intro h
  have hb : b ∈ generatorCentralizer := by rw [h]; trivial
  exact a_mul_b_ne_b_mul_a (Subgroup.mem_centralizer_singleton_iff.mp hb).symm

end HaradaNorton
