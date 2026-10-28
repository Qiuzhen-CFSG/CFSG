module
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
-- Internal proof split: access the hidden seed-range definition only in proofs.
-- The public seed interface and every existing module remain unchanged.
import all Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection.Words
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection.LeviReduction

/-!
# Radical commutator squares detect the linear Ree seed and torus

For m ≥ 1, a nontrivial internal end-node torus element and the positive
middle Suzuki word give a radical–seed commutator with nonidentity square.
For an arbitrary element with trivial SL₂ projection, the proved
radical–complementary-torus factorization and the same square calculation
force its torus factor to be identity whenever all radical commutators
square to one. Every commutator in the final statements is intrinsic to
the full linear parabolic.

The calculation includes arbitrary radical factors in the actor. Its
nonzero degree-two Cartan entry depends only on the degree-one matrix
layer, which inner radical conjugation preserves. The final rigidity
assembly for arbitrary subnormal two-perfect subgroups remains in the
parent module; these theorems discharge precisely its two square premises.

Sources: the linear parabolic and perfect seed of Aschbacher–Smith
F.1.12(I)(5) and (II), printed pp.263–264; the Ree exclusion in 2.3.9(7),
p.526; and the invariant-parabolic argument in E.6.8, pp.247–248,
`refs/quasithin.pdf`. The concrete middle-root word law is GLS3 Table 2.4(V).
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace ReeF4.ConverseParabolics.CoreActionRigidity
open LargeLocalSeeds FullLeviRepresentation SquareDetection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration

private theorem exists_unit_ne_one {m : ℕ} (hm : 1 ≤ m) :
    ∃ a : (CoefficientField m)ˣ, a ≠ 1 := by
  have hcard : 2 < Nat.card (CoefficientField m) := by
    rw [field_card]
    have h := Nat.pow_lt_pow_right (a := 2) (by omega) (show 1 < 2 * m + 1 by omega)
    simpa using h
  have : Nontrivial (CoefficientField m)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]
    omega)
  exact exists_ne 1

/-- A radical commutator with an element of the actual perfect seed has
nonidentity square, inside the full linear parabolic. -/
theorem linear_exists_seed_commutator_square_ne_one {m : ℕ} (hm : 1 ≤ m) :
    ∃ q ∈ intrinsicRadical m .linear, ∃ b ∈ linearSeed m,
      (⁅q, b⁆ : parabolic m .linear) ^ 2 ≠ 1 := by
  obtain ⟨a, ha⟩ := exists_unit_ne_one hm
  have hqR : middleWord (1 : CoefficientField m) 0 ∈ radical m .linear := by
    rw [radical_eq_rootRadical]
    exact middleWord_mem_radical 1 0
  let q : parabolic m .linear := ⟨middleWord 1 0, radical_le_parabolic m .linear hqR⟩
  obtain ⟨s, hs⟩ := internal_torus_mem a
  let s' : standardSeed (canonicalLocalBlockInput m) .linear :=
    ⟨s.val, fixedLevi_le_seed _ .linear s.property⟩
  let b := seedInclusion m .linear s'
  have hb : b ∈ linearSeed m := by
    change b ∈ (seedInclusion m .linear).range
    exact ⟨s', rfl⟩
  have hbval : b.val = torusElement (a ^ 2) a⁻¹ := hs
  refine ⟨q, hqR, b, hb, ?_⟩
  have hn := radical_torus_commutator_square_ne_one (1 : Model m)
    (Parabolics.radical m .linear).one_mem (a ^ 2) a⁻¹ (by simpa using ha)
  rw [one_mul] at hn
  intro hz
  apply hn
  have he := congrArg (parabolic m .linear).subtype hz
  simpa only [map_pow, map_commutatorElement, map_one, MonoidHom.coe_coe, Subgroup.coe_subtype,
    hbval] using he

/-- Once the SL₂ coordinate vanishes, square-one radical commutators force
the complementary torus coordinate to vanish as well. -/
theorem linear_torus_eq_one_of_commutator_squares {m : ℕ} (hm : 1 ≤ m)
    (b : parabolic m .linear) (hb : (linearProjection hm b).1 = 1)
    (hsquare : ∀ q ∈ intrinsicRadical m .linear,
      (⁅q, b⁆ : parabolic m .linear) ^ 2 = 1) :
    (linearProjection hm b).2 = 1 := by
  obtain ⟨r, hr, c, he⟩ := exists_radical_torus_factors hm b hb
  have hc : c = 1 := by
    by_contra hc
    have hqR : middleWord (1 : CoefficientField m) 0 ∈ radical m .linear := by
      rw [radical_eq_rootRadical]
      exact middleWord_mem_radical 1 0
    let q : parabolic m .linear := ⟨middleWord 1 0, radical_le_parabolic m .linear hqR⟩
    have hn := radical_torus_commutator_square_ne_one r
      (by rwa [← radical_eq_rootRadical]) 1 c hc
    apply hn
    have hz := congrArg (parabolic m .linear).subtype (hsquare q hqR)
    simpa only [map_pow, map_commutatorElement, map_one, MonoidHom.coe_coe,
      Subgroup.coe_subtype, he] using hz
  have hbR : b ∈ intrinsicRadical m .linear := by
    change b.val ∈ radical m .linear
    rw [he, hc]
    have ht : torusElement (1 : (CoefficientField m)ˣ) 1 = 1 := (torusHom m).map_one
    rwa [ht, mul_one]
  have hz : linearProjection hm b = 1 := by
    apply (linearProjection hm).mem_ker.mp
    rwa [linearProjection_ker]
  exact congrArg Prod.snd hz

end ReeF4.ConverseParabolics.CoreActionRigidity
