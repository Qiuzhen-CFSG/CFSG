module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.StructuralCommutation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.RootGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.FieldMarkingApplication

/-!
# Triality source application from structural commutators and module matrices

The four retained subgroup assertions are literal clauses of Fong--Seitz
I (6E)(b), printed p.43, on the same canonical radical and right-conjugated
roots. They imply all ten positive commuting pairs by StructuralCommutation.
The faithful long rank-one map supplies highest-root injectivity, and the
actual cubic field supplies the basis. The earlier matrices (9.27), (9.29),
the unnormalized long action and torus covariance then feed the existing
coefficient reconstruction, including q=2.

RootGeometry proves positive generation from the two simple-root markings.
Consequently the original and geometric PositiveRootData consumers no
longer require a separate six-root placement assertion, ten commuting
pairs, highest-root injectivity, or cubic spanning. The signed construction
and source normal-generation argument give the same conditional Bruhat
consumer, retaining Q.q, the full Borel and the supplied endpoint marking.

This is a checked reduction of source premises, not the completed source
reconstruction. Compatible rank-one pinnings (including their braid and
orthogonal stabilizers), simple-root identifications, Weyl placement,
source matrix equations and mixed torus equations are still required.
The four structural assertions are supplied by the earlier 6E(b) row
producer and ultimately discharged by source assembly. No later normalized
coefficient, group recognition or simplicity assertion is assumed.

Source: Fong--Seitz I (6E)(b); II (9.22), (9.27)--(9.35), printed
pp.217--220; DGS Theorem D, printed p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
open PinnedApplication
variable {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F}
  {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

/-- Four subgroup assertions selected from 6E(b), on the actual canonical
radical and roots. Here i is the cubic/short endpoint and j the fixed/long
endpoint (source labels 2 and 1 respectively). This is not the complete row:
its rank-one isomorphisms and irreducible module still have to be supplied. -/
structure StructuralRow (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (i j : Fin 2) : Prop where
  radical_derived : ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ =
    rootAt Q split j (Q.simple i * Q.simple j)
  long_commutator : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ =
    rootAt Q split j (Q.simple i * Q.simple j)
  long_central : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i * Q.simple j)⁆ = ⊥
  orthogonal : ⁅rootAt Q split i (Q.simple j),rootAt Q split j (Q.simple i)⁆ = ⊥

namespace StructuralApplication
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (shortBase : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
  (longBase : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (w.indices 0) (w.indices 1))

include shortBase longBase hm row in
/-- The ten positive commutations follow from the literal 6E(b) radical,
its long-root commutator and its two indicated centralizations. -/
theorem positiveCommutations : p.PositiveCommutations := by
  apply p.positiveCommutations_of_radical (simpleRemainder Q split (w.indices 0))
  · rw [longBase]
    exact simpleRoot_le_other_remainder Q split hm (w.indices 1) (w.indices 0)
      (w.indices.injective.ne (by decide))
  · rw [RootGeometry.short_one_rootAt Q split p w shortBase]
    exact (show rootAt Q split (w.indices 0) (Q.simple (w.indices 1)) ≤
      middleRoots Q split (w.indices 1) (w.indices 0) from le_sup_left.trans le_sup_left).trans
        (middleRoots_le_remainder Q split hm (w.indices 1) (w.indices 0)
          (w.indices.injective.ne (by decide)))
  · rw [ModuleApplication.long_two_rootAt Q split p w longBase, row.radical_derived]
  · rw [longBase, ModuleApplication.long_one_rootAt Q split p w longBase,
      ModuleApplication.long_two_rootAt Q split p w longBase]
    exact row.long_commutator
  · rw [longBase, ModuleApplication.long_two_rootAt Q split p w longBase]
    exact row.long_central
  · rw [RootGeometry.short_one_rootAt Q split p w shortBase,
      ModuleApplication.long_one_rootAt Q split p w longBase]
    exact row.orthogonal
end StructuralApplication

section Matrices
variable {Y : Type*} [Group Y] (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ) (θ : F)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

/-- The remaining earlier matrix calculations, before coefficient normalization.
These are still source reconstruction obligations. Commutation, injectivity,
and the cubic spanning property are proved separately from structural inputs. -/
structure EarlierModuleEquations where
  f : F → F → K
  g : F → K → K
  τ : K ≃+* K
  basis_pairing : ∀ (a : F) (b : K) (i : Fin 3),
    rightCommutator (p.s 2 (b.val*θ^i.val)) (p.s 0 a) =
      p.l 1 (e.trace (a*(b.val*θ^i.val)))
  short_short : ∀ a b, rightCommutator (p.s 1 b) (p.s 0 a) =
    p.s 2 (σ a * σ (σ b) + σ (σ a) * σ b) *
      p.l 1 (e.trace (σ a * σ (σ a) * b)) * p.l 2 (f a b)
  mixed : ∀ a b, rightCommutator (p.l 0 b) (p.s 0 a) =
    p.s 1 (a*b.val) * p.s 2 (σ a * σ (σ a) * b.val) *
      p.l 1 (e.norm a * b) * p.l 2 (g a b)
  long_twisted : ∀ a b, rightCommutator (p.l 1 b) (p.l 0 a) = p.l 2 (b * τ a)
  covariance : CoefficientCovariance e g

namespace EarlierModuleEquations
variable {p e θ} (d : EarlierModuleEquations p e θ)

/-- The genuine rank-one embedding supplies coefficient injectivity; the
structural commutation theorem supplies every commuting pair. -/
def cubicEquations (hfaith : Function.Injective p.longMap) (hcomm : p.PositiveCommutations) :
    CubicModuleEquations p e θ where
  f := d.f
  g := d.g
  τ := d.τ
  highest_injective := p.longOrbit_injective hfaith 2
  short0_long1 := hcomm.short0_long1
  short0_long2 := hcomm.short0_long2
  long0_short1 := hcomm.long0_short1
  long0_short2 := hcomm.long0_short2
  long0_long2 := hcomm.long0_long2
  short1_long1 := hcomm.short1_long1
  short1_long2 := hcomm.short1_long2
  short2_long1 := hcomm.short2_long1
  short2_long2 := hcomm.short2_long2
  long1_long2 := hcomm.long1_long2
  basis_pairing := d.basis_pairing
  short_short := d.short_short
  mixed := d.mixed
  long_twisted := d.long_twisted
  covariance := d.covariance
end EarlierModuleEquations
end Matrices

namespace StructuralApplication
variable [Finite F] {n : ℕ} {hn : 0 < n}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (shortBase : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
  (longBase : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (w.indices 0) (w.indices 1))
  (hfaith : Function.Injective p.longMap)
  (e : ScalarMarking (binaryParameters n hn) σ) (θ : F) (hθ : σ θ ≠ θ)
  (d : EarlierModuleEquations p e θ)

/-- The coefficient stage now uses the actual structural radical and its
commutators, without ten commutation premises or a highest-root certificate. -/
def moduleStage : ModuleStage p e :=
  (d.cubicEquations hfaith
    (positiveCommutations Q split p w shortBase longBase hm row)).moduleStage hθ

/-- Construct the literal positive data using only the two simple-root
placements; the remaining four placements and positive generation are proved. -/
def positiveData : TrialityPresentation.PositiveRootData Q split n hn σ where
  scalars := e
  shortRoot := (rawRoots p).markedShort
  longRoot := p.longOrbit
  relations := (ModuleApplication.coefficientStage Q split p w longBase e hm
    (moduleStage Q split p w shortBase longBase hm row hfaith e θ hθ d)).relations
  positive := RootGeometry.positiveClosure_eq_unipotent Q split p w shortBase longBase e hm

/-- The signed roots and Weyl actions use exactly the same source pinning. -/
def signedData : TrialityPresentation.SignedRootData
    (positiveData Q split p w shortBase longBase hm row hfaith e θ hθ d) where
  negativeShort i := p.dihedral.W.toMonoidHom.comp (p.markedShort i)
  negativeLong i := p.dihedral.W.toMonoidHom.comp (p.longOrbit i)
  actions := p.actions e

@[simp] theorem signedData_roots :
    (signedData Q split p w shortBase longBase hm row hfaith e θ hθ d).roots =
      p.signedRoots e := rfl

/-- Preserve the supplied original/geometric marking and its exact S image. -/
theorem nativeHom_range_marked {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split p w shortBase longBase hm row hfaith e θ hθ d).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  (positiveData Q split p w shortBase longBase hm row hfaith e θ hθ d).nativeHom_range_marked marking h

/-- The same signed generation proof now needs no six-root placement premise.
The mixed torus equations remain a source obligation. -/
def bruhatData {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S)
    (t : (p.signedRoots e).TorusRelations) :
    TrialityPresentation.BruhatRootData
      (positiveData Q split p w shortBase longBase hm row hfaith e θ hθ d) where
  signed := signedData Q split p w shortBase longBase hm row hfaith e θ hθ d
  weyl := p.weylRelations e
    (positiveData Q split p w shortBase longBase hm row hfaith e θ hθ d).root_relations
  torus := t
  generates := by
    change (p.signedRoots e).signedClosure = ⊤
    rw [w.signedClosure_eq_unipotentClosure Q split p e
      (RootGeometry.positiveClosure_eq_unipotent Q split p w shortBase longBase e hm)]
    exact A2Source.unipotent_normalClosure_eq_top Q marking h split

include split w shortBase longBase hm row hfaith θ hθ d in
/-- The full source Borel and original quotient map remain literal. -/
theorem quotient_bruhat {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S)
    (t : (p.signedRoots e).TorusRelations) (x : X) :
    ∃ (u v : X ⧸ Q.D) (a : Bool) (k : ℕ),
      u ∈ Q.tits.B ∧ v ∈ Q.tits.B ∧ k ≤ 6 ∧
      Q.q x = u * (p.signedRoots e).alternating a k * v :=
  (bruhatData Q split p w shortBase longBase hm row hfaith e θ hθ d marking h t).source_bruhat (Q.q x)

/-- For the original generated numerator, keep the exact original quotient
image of S. No universal-to-original quotient descent is assumed. -/
theorem nativeHom_range_original
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h₀ : HypothesisF11 L S) (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (p₀ : RankOnePair σ ((generated L S) ⧸ Q₀.D)) (w₀ : WeylPlacement Q₀ p₀)
    (shortBase₀ : (p₀.shortOrbit 0).range = simpleRoot Q₀ split₀ (w₀.indices 0))
    (longBase₀ : (p₀.longOrbit 0).range = simpleRoot Q₀ split₀ (w₀.indices 1))
    (hm₀ : rotationOrder Q₀ = 6)
    (row₀ : StructuralRow Q₀ split₀ (w₀.indices 0) (w₀.indices 1))
    (hfaith₀ : Function.Injective p₀.longMap)
    (e₀ : ScalarMarking (binaryParameters n hn) σ) (θ₀ : F) (hθ₀ : σ θ₀ ≠ θ₀)
    (d₀ : EarlierModuleEquations p₀ e₀ θ₀) :
    (positiveData Q₀ split₀ p₀ w₀ shortBase₀ longBase₀ hm₀ row₀ hfaith₀ e₀ θ₀ hθ₀ d₀).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q₀.q :=
  TrialityPresentation.nativeHom_range_original h₀ Q₀ split₀
    (positiveData Q₀ split₀ p₀ w₀ shortBase₀ longBase₀ hm₀ row₀ hfaith₀ e₀ θ₀ hθ₀ d₀)
end StructuralApplication
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
