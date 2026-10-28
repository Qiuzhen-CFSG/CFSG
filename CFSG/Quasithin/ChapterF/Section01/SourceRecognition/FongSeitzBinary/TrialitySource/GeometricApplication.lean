module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.GeometricPinning
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.CartanApplication

/-!
# Source triality applications with constructed geometric pinnings

Choose actual reflections inside both canonical rank-one factors. The local
PSL₂ identifications, over the cubic field and its actual fixed subfield,
and the exchanged-root clause of 6E(b) construct RankOnePair and its Weyl
placements. The existing structural argument then gives all ten positive
commutations and positive generation. Both endpoint squares, the whole
signed generation statement, and the two coroots in the full Cartan now
use those constructed maps. Full-Cartan abelianness discharges the earlier
independent cross-commutation premise and gives torus multiplicativity.

The original and geometric positive-image applications preserve the exact
quotient map and supplied amalgam marking. The existing module-coordinate
and coefficient reconstruction is applied to these maps without adding
new relation certificates. Its EarlierModuleEquations premise remains a
source obligation: the two local scalar labelings must still be chosen
compatibly with the twisted-tensor/natural-module comparison. The mixed
torus characters also remain open, so this module does not claim complete
source recognition. All constructions include q=2 and q=4 and retain
both endpoint orientations and the full Borel.

Source: Fong--Seitz I (5C), (6E)(b); II §7, (9.22)--(9.35), printed
pp.217--220; DGS Theorem D, printed p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricApplication
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : F ≃+* F) (indices : Fin 2 ≃ Fin 2)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
variable
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2, ScalarMarking.SourceFixed (σ := σ)))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (indices 0) (indices 1))

/-- Choose the reflections inside the two actual root-generated factors and
construct their entire rank-one pinnings. The orthogonal clause of 6E(b)
proves their braid and orthogonal actions, including the nonperfect binary case. -/
def pair : RankOnePair σ (X ⧸ Q.D) :=
  GeometricPinning.pair Q split σ indices hVi hVj μi μj
    (UnitarySource.actorReflection Q split (indices 0))
    (UnitarySource.actorReflection Q split (indices 1)) hm row.orthogonal

local notation "p" => pair Q split σ indices hVi hVj μi μj hm row

/-- The same chosen Weyl elements have the literal marked endpoint classes. -/
def placement : WeylPlacement Q p :=
  GeometricPinning.placement Q split σ indices hVi hVj μi μj
    (UnitarySource.actorReflection Q split (indices 0))
    (UnitarySource.actorReflection Q split (indices 1)) hm row.orthogonal

local notation "w" => placement Q split σ indices hVi hVj μi μj hm row

theorem short_range : ((p).shortOrbit 0).range = simpleRoot Q split (indices 0) :=
  GeometricPinning.short_range Q split σ indices hVi hVj μi μj _ _ hm row.orthogonal

theorem long_range : ((p).longOrbit 0).range = simpleRoot Q split (indices 1) :=
  GeometricPinning.long_range Q split σ indices hVi hVj μi μj _ _ hm row.orthogonal

theorem long_injective : Function.Injective (p).longMap :=
  GeometricPinning.long_injective Q split σ indices hVi hVj μi μj _ _ hm row.orthogonal

local notation "hs" => short_range Q split σ indices hVi hVj μi μj hm row
local notation "hl" => long_range Q split σ indices hVi hVj μi μj hm row
local notation "hf" => long_injective Q split σ indices hVi hVj μi μj hm row

/-- No pinning or commuting-pair certificate is needed for the ten source
commutations: they follow from the four literal 6E(b) assertions. -/
theorem positiveCommutations : (p).PositiveCommutations :=
  StructuralApplication.positiveCommutations Q split p w hs hl hm row

variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

/-- The constructed positive root ranges generate the actual split U. -/
theorem positiveClosure_eq_unipotent :
    ((p).signedRoots e).positive.positiveClosure = split.U :=
  RootGeometry.positiveClosure_eq_unipotent Q split p w hs hl e hm

/-- Both source endpoint maps send the original representative to the same
short Weyl word in the literal quotient. -/
theorem short_word_endpoint :
    ∃ x : P (indices 0), Q.q x = ((p).signedRoots e).nA 1 ∧
      (Q.endpointEquiv (indices 0) x : X ⧸ Q.D) = ((p).signedRoots e).nA 1 :=
  RootGeometry.short_word_endpoint Q split p w hs e

theorem long_word_endpoint :
    ∃ x : P (indices 1), Q.q x = ((p).signedRoots e).nB 1 ∧
      (Q.endpointEquiv (indices 1) x : X ⧸ Q.D) = ((p).signedRoots e).nB 1 :=
  RootGeometry.long_word_endpoint Q split p w hl e

/-- The entire signed closure is the normal closure of the same split U. -/
theorem signedClosure_eq_unipotentClosure :
    ((p).signedRoots e).signedClosure = split.unipotentClosure :=
  (w).signedClosure_eq_unipotentClosure Q split p e
    (positiveClosure_eq_unipotent Q split σ indices hVi hVj μi μj hm row e)

/-- Original source normal generation gives signed-root generation of the
whole literal quotient, for either supplied amalgam marking. -/
theorem signedClosure_eq_top {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    ((p).signedRoots e).signedClosure = ⊤ := by
  rw [signedClosure_eq_unipotentClosure Q split σ indices hVi hVj μi μj hm row e]
  exact A2Source.unipotent_normalClosure_eq_top Q marking h split

/-- The first actual coroot lies in the original full Cartan. -/
theorem hA_mem_cartan (t : (ExtensionField (binaryParameters n hn))ˣ) :
    ((p).signedRoots e).hA t ∈ Q.tits.B ⊓ Q.tits.N := by
  let t' : Fˣ := Units.map e.extension.symm.toMonoidHom t
  have ht : Units.map e.extension.toMonoidHom t' = t := by
    ext
    simp [t']
  rw [← ht, (p).hA_parameter]
  exact GeometricPinning.short_cartan Q split σ indices hVi hVj μi μj _ _ hm row.orthogonal t'

/-- The second coroot uses the restriction of the same extension marking. -/
theorem hB_mem_cartan (t : (fixedField (binaryParameters n hn))ˣ) :
    ((p).signedRoots e).hB t ∈ Q.tits.B ⊓ Q.tits.N := by
  let t' : Kˣ := Units.map e.fixed.symm.toMonoidHom t
  have ht : Units.map e.fixed.toMonoidHom t' = t := by
    ext
    simp [t']
  rw [← ht, (p).hB_parameter]
  exact GeometricPinning.long_cartan Q split σ indices hVi hVj μi μj _ _ hm row.orthogonal t'

/-- Full-Cartan abelianness proves the cross-commutation of the two coroots. -/
theorem torus_factors_commute (a : (ExtensionField (binaryParameters n hn))ˣ)
    (b : (fixedField (binaryParameters n hn))ˣ) :
    Commute (((p).signedRoots e).hA a) (((p).signedRoots e).hB b) := by
  let := split.abelian
  exact congrArg Subtype.val (mul_comm
    (⟨_,hA_mem_cartan Q split σ indices hVi hVj μi μj hm row e a⟩ : ↥(Q.tits.B ⊓ Q.tits.N))
    (⟨_,hB_mem_cartan Q split σ indices hVi hVj μi μj hm row e b⟩ : ↥(Q.tits.B ⊓ Q.tits.N)))

/-- The literal two-parameter torus is multiplicative without an extra
cross-commutation hypothesis. Mixed root weights remain to be proved. -/
theorem torus_mul (a b : TorusParameters n hn) :
    ((p).signedRoots e).torus (a*b) = ((p).signedRoots e).torus a * ((p).signedRoots e).torus b := by
  apply StructuralApplication.signed_torus_mul_of_cross_commuting
  exact torus_factors_commute Q split σ indices hVi hVj μi μj hm row e

variable (θ : F) (hθ : σ θ ≠ θ) (d : EarlierModuleEquations (pair Q split σ indices hVi hVj μi μj hm row) e θ)

/-- The module-stage consumer now takes constructed pinnings and Weyl
placements. The genuine earlier matrix equations remain explicit obligations. -/
def positiveData : TrialityPresentation.PositiveRootData Q split n hn σ :=
  StructuralApplication.positiveData Q split p w hs hl hm row hf e θ hθ d

/-- The signed roots and their full Weyl action table use the same source maps. -/
def signedData : TrialityPresentation.SignedRootData
    (positiveData Q split σ indices hVi hVj μi μj hm row e θ hθ d) :=
  StructuralApplication.signedData Q split p w hs hl hm row hf e θ hθ d

/-- Preserve the literal original or geometric amalgam marking and its S image. -/
theorem nativeHom_range_marked {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split σ indices hVi hVj μi μj hm row e θ hθ d).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  TrialityPresentation.PositiveRootData.nativeHom_range_marked _ marking h

include θ hθ d in
/-- The full Borel and each original quotient representative remain unchanged;
the mixed torus actions are still required before full recognition. -/
theorem quotient_bruhat {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S)
    (t : ((p).signedRoots e).TorusRelations) (x : X) :
    ∃ (u v : X ⧸ Q.D) (a : Bool) (k : ℕ),
      u ∈ Q.tits.B ∧ v ∈ Q.tits.B ∧ k ≤ 6 ∧
      Q.q x = u * ((p).signedRoots e).alternating a k * v :=
  StructuralApplication.quotient_bruhat Q split p w hs hl hm row hf e θ hθ d marking h t x

/-- The original generated numerator keeps its exact quotient image of S,
with no descent assumption from a universal completion. -/
theorem nativeHom_range_original {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h₀ : HypothesisF11 L S) (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hVi₀ : simpleRemainder Q₀ split₀ (indices 0) ≤ localKernel Q₀ (indices 0))
    (hVj₀ : simpleRemainder Q₀ split₀ (indices 1) ≤ localKernel Q₀ (indices 1))
    (μi₀ : localGroup Q₀ split₀ (indices 0) ≃* PSL(2,F))
    (μj₀ : localGroup Q₀ split₀ (indices 1) ≃* PSL(2,K))
    (hm₀ : rotationOrder Q₀ = 6)
    (row₀ : StructuralRow Q₀ split₀ (indices 0) (indices 1))
    (d₀ : EarlierModuleEquations
      (pair Q₀ split₀ σ indices hVi₀ hVj₀ μi₀ μj₀ hm₀ row₀) e θ) :
    (positiveData Q₀ split₀ σ indices hVi₀ hVj₀ μi₀ μj₀ hm₀ row₀ e θ hθ d₀).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q₀.q :=
  TrialityPresentation.nativeHom_range_original h₀ Q₀ split₀ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricApplication
