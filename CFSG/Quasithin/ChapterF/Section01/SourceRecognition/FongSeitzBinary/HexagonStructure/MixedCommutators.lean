module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MixedCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.MiddleIsolation

/-!
# The unequal-linear commutators on the original marking and triality consumer

Both nonzero commutators are now proved. Together with odd-Cartan isolation
and the four vanishing commutators, they give all seven subgroup identities
of Fong--Seitz I (6E)(b) on the literal original Sylow image. The arbitrary
marked-amalgam application includes the universal/geometric carrier; the
SourceQuotient application retains Q.q and the actual image of S.

The triality StructuralRow now has every field discharged from the unequal
linear local models and earlier kernel inclusions. Its published consumer
supplies all ten positive commuting pairs on the same RankOnePair and
WeylPlacement. No nonzero commutator is an input to these new applications.
The binary smaller field, acting field four and exponent six are included.

This is the commutator part of the unequal branch. The companion
Irreducibility module supplies the actual irreducible action, and CubicRatio
supplies the field ratio. Nonlinear/solvable effective sections and Suzuki/unitary
exclusions remain obligations of the full hexagon family. Actual local
model and kernel inputs remain with their existing earlier-source producers.
Compatible pinnings and later mixed polynomial equations remain with the
triality source-relation owner.

Source: Fong--Seitz I (6E)(b), printed pp.43--45; II (9.22), pp.217--220.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F E : Type*} [Field F] [Finite F] [CharP F 2]
  [Field E] [Finite E] [CharP E 2]

/-- All four fields of the actual triality structural consumer are proved;
there is no remaining derived or mixed-commutator hypothesis. -/
theorem triality_structuralRow_of_unequal_linear
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    TrialitySource.StructuralRow Q split j i :=
  triality_structuralRow_of_long_commutator Q split hm i j hij hKi hKj μi μj ha hab hE hF
    (unequal_linear_long_commutator Q split hm i j hij hKi hKj μi μj
      (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
      ha hab hE hF)

/-- Apply the proved structural row to the published positive-commutation
consumer with its original simple-root ranges and both endpoint placements. -/
theorem triality_positiveCommutations_of_unequal_linear
    {σ : F ≃+* F}
    (p : Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.RankOnePair σ (X ⧸ Q.D))
    (w : Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.WeylPlacement Q p)
    (shortBase : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
    (longBase : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
    (hm : rotationOrder Q = 6)
    (hKi : simpleRemainder Q split (w.indices 1) ≤ localKernel Q (w.indices 1))
    (hKj : simpleRemainder Q split (w.indices 0) ≤ localKernel Q (w.indices 0))
    (μi : localGroup Q split (w.indices 1) ≃* PSL(2,E))
    (μj : localGroup Q split (w.indices 0) ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    p.PositiveCommutations :=
  TrialitySource.StructuralApplication.positiveCommutations Q split p w shortBase longBase hm
    (triality_structuralRow_of_unequal_linear Q split hm (w.indices 1) (w.indices 0)
      (w.indices.injective.ne (by decide)) hKi hKj μi μj ha hab hE hF)

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

/-- All seven literal subgroup identities of (6E)(b) on the same original
or geometric Sylow image. Models and kernel inclusions are earlier inputs. -/
theorem marked_unequal_commutator_relations
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    let si := UnitarySource.actorReflection Q split i
    let sj := UnitarySource.actorReflection Q split j
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U (sj.val : X ⧸ Q.D)
    let A := simpleRoot Q split i
    let B := rightConjugate (simpleRoot Q split j) (si.val : X ⧸ Q.D)
    let C := rightConjugate A (sj.val*si.val : Q.tits.N)
    let D := rightConjugate (simpleRoot Q split j) (si.val*sj.val : Q.tits.N)
    let E₀ := rightConjugate A (sj.val : X ⧸ Q.D)
    ⁅V,V⁆ = C ∧ ⁅A,E₀⁆ = C ∧ ⁅B,D⁆ = C ∧
      ⁅A,C⁆ = ⊥ ∧ ⁅C,E₀⁆ = ⊥ ∧ ⁅A,D⁆ = ⊥ ∧ ⁅B,E₀⁆ = ⊥ := by
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  dsimp only
  rw [← marked_radical_eq h Q e split j sj.val sj.class_eq,
    ← rootAt_eq Q split j (Q.simple i) si.val si.class_eq,
    ← rootAt_eq Q split i (Q.simple j*Q.simple i) (sj.val*si.val)
      (by rw [map_mul,sj.class_eq,si.class_eq]),
    ← rootAt_eq Q split j (Q.simple i*Q.simple j) (si.val*sj.val)
      (by rw [map_mul,si.class_eq,sj.class_eq]),
    ← rootAt_eq Q split i (Q.simple j) sj.val sj.class_eq]
  exact ⟨unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF,
    unequal_linear_long_commutator Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF,
    unequal_linear_short_commutator Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF,
    unequal_linear_zero_relations Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The same seven identities for the literal image of S under Q.q. -/
theorem quotient_unequal_commutator_relations
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    let si := UnitarySource.actorReflection Q split i
    let sj := UnitarySource.actorReflection Q split j
    let U := (S.subgroupOf (generated L S)).map Q.q
    let V := U ⊓ rightConjugate U (sj.val : (generated L S) ⧸ Q.D)
    let A := simpleRoot Q split i
    let B := rightConjugate (simpleRoot Q split j) (si.val : (generated L S) ⧸ Q.D)
    let C := rightConjugate A (sj.val*si.val : Q.tits.N)
    let D := rightConjugate (simpleRoot Q split j) (si.val*sj.val : Q.tits.N)
    let E₀ := rightConjugate A (sj.val : (generated L S) ⧸ Q.D)
    ⁅V,V⁆ = C ∧ ⁅A,E₀⁆ = C ∧ ⁅B,D⁆ = C ∧
      ⁅A,C⁆ = ⊥ ∧ ⁅C,E₀⁆ = ⊥ ∧ ⁅A,D⁆ = ⊥ ∧ ⁅B,E₀⁆ = ⊥ := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := marked_unequal_commutator_relations Q split (originalMarkedIso Q) h hm i j hij
    hKi hKj μi μj ha hab hE hF
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
