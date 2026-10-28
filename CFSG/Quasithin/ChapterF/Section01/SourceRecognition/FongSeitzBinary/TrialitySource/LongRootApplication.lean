module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.LongAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.GeometricScalars

/-!
# The long-root source relations on the original quotient

The long commutator clause of Fong--Seitz I (6E)(b) supplies the actual
central-commutator containment. Canonical hexagon roots give disjointness,
and the structural row gives the required commuting pairs. LongAction
therefore determines the long–long coefficient and the six signed
long-root weights of the long coroot, in either source orientation and
without excluding q=2 or q=4.

The construction is applied to the geometric pinning after relabeling the
entire long actor. It uses the same quotient, chosen Weyl lifts and actual
fixed-field inclusion as GeometricScalars. The right-commutator conversion
is proved from the involutions in each characteristic-two root group.

The existing EarlierModuleEquations interface now has a constructor that
discharges its long_twisted field, and feeds the literal positive-image
consumer. Basis trace pairings, the lifted short–short and full mixed
products, and covariance remain explicit obligations of this same owner.
Neither this constructor nor its conditional positive consumer asserts
the complete source recognition.

Source: Fong--Seitz I (6E)(b), printed p.43; II §7 and (9.27)--(9.31),
printed p.219; DGS Theorem D, printed p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open scoped commutatorElement MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.LongRootApplication
variable {X F : Type*} [Group X] [Field F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {σ : F ≃+* F} (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (hs : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
  (hl : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (w.indices 0) (w.indices 1))
  (hf : Function.Injective p.longMap)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "c" => StructuralApplication.positiveCommutations Q split p w hs hl hm row
local notation "hd" => ModuleApplication.long_ranges_disjoint Q split p w hl hm

include hl row in
/-- The actual central-commutator containment is the long-root clause of 6E(b). -/
theorem commutator_mem (a b : K) : ⁅p.l 1 b,p.l 0 a⁆ ∈ (p.longOrbit 2).range := by
  have he : ⁅(p.longOrbit 0).range,(p.longOrbit 1).range⁆ = (p.longOrbit 2).range := by
    rw [hl,ModuleApplication.long_one_rootAt Q split p w hl,
      ModuleApplication.long_two_rootAt Q split p w hl]
    exact row.long_commutator
  rw [← he,Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator ⟨.ofAdd b,rfl⟩ ⟨.ofAdd a,rfl⟩

local notation "hc" => commutator_mem Q split p w hl row

include hs hl hm row hf in
/-- The complete long–long right commutator on the original quotient.
Its coefficient is proved from the source action, without a twisted-action premise. -/
theorem long_long (a b : K) : rightCommutator (p.l 1 b) (p.l 0 a) = p.l 2 (a*b) := by
  have hi (i : Fin 3) (x : K) : (p.l i x)⁻¹ = p.l i x := by
    rw [← map_inv,← ofAdd_neg,CharTwo.neg_eq]
  have hh := LongAction.commutator p c hf hd hc a b
  simpa only [rightCommutator,commutatorElement_def,hi] using hh

include hs hl hm row hf in
/-- The fifth ordered exchange in the native positive-root convention. -/
theorem long_exchange (a b : K) : p.l 0 a*p.l 1 b = p.l 1 b*p.l 0 a*p.l 2 (a*b) :=
  LongAction.exchange p c hf hd hc a b

variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)
include hs hl hm row hf in
/-- All six signed long-root characters use the same source fixed-field marking. -/
theorem hB_signed_long (t : Kˣ) (positive : Bool) (i : Fin 3) (a : K) :
    (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t)*
      (p.signedRoots e).longSigned positive i (e.fixed a)*
      ((p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
    (p.signedRoots e).longSigned positive i
      (e.fixed ((if positive then ![t.val^2,t.val⁻¹,t.val] i
        else (![t.val^2,t.val⁻¹,t.val] i)⁻¹)*a)) :=
  LongAction.hB_signed_long p c hf hd hc e t positive i a

section RemainingEquations
variable (θ : F) (f : F → F → ScalarMarking.SourceFixed (σ := σ))
  (g : F → ScalarMarking.SourceFixed (σ := σ) → ScalarMarking.SourceFixed (σ := σ))
  (hpair : ∀ (a : F) (b : ScalarMarking.SourceFixed (σ := σ)) (i : Fin 3),
    rightCommutator (p.s 2 (b.val*θ^i.val)) (p.s 0 a) = p.l 1 (e.trace (a*(b.val*θ^i.val))))
  (hshort : ∀ a b, rightCommutator (p.s 1 b) (p.s 0 a) =
    p.s 2 (σ a*σ (σ b)+σ (σ a)*σ b)*p.l 1 (e.trace (σ a*σ (σ a)*b))*p.l 2 (f a b))
  (hmixed : ∀ a b, rightCommutator (p.l 0 b) (p.s 0 a) =
    p.s 1 (a*b.val)*p.s 2 (σ a*σ (σ a)*b.val)*p.l 1 (e.norm a*b)*p.l 2 (g a b))
  (hcov : CoefficientCovariance e g)

/-- Discharge the long-twisted field of the existing source module interface.
The trace pairings, lifted short and mixed products and covariance remain
explicit source obligations; no field automorphism for this long action remains. -/
def earlierModuleEquations : EarlierModuleEquations p e θ where
  f := f
  g := g
  τ := RingEquiv.refl K
  basis_pairing := hpair
  short_short := hshort
  mixed := hmixed
  long_twisted a b := by
    simpa only [RingEquiv.refl_apply,mul_comm] using long_long Q split p w hs hl hm row hf a b
  covariance := hcov

variable [Finite F] (hθ : σ θ ≠ θ)

/-- Feed the proved long equation into the actual positive-root consumer.
This still requires the four explicitly displayed unresolved module equations. -/
def positiveData : TrialityPresentation.PositiveRootData Q split n hn σ :=
  StructuralApplication.positiveData Q split p w hs hl hm row hf e θ hθ
    (earlierModuleEquations Q split p w hs hl hm row hf e θ f g hpair hshort hmixed hcov)

/-- The same conditional data retains the literal original/geometric S image. -/
theorem nativeHom_range_marked {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split p w hs hl hm row hf e θ f g hpair hshort hmixed hcov hθ).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  (positiveData Q split p w hs hl hm row hf e θ f g hpair hshort hmixed hcov hθ).nativeHom_range_marked
    marking h
end RemainingEquations
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.LongRootApplication

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricLongRoots
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : F ≃+* F) (indices : Fin 2 ≃ Fin 2)
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2,ScalarMarking.SourceFixed (σ := σ)))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (indices 0) (indices 1))
  {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "p" => GeometricApplication.pair Q split σ indices hVi hVj μi μj hm row
local notation "η" => GeometricScalars.scalarAutomorphism Q split σ indices hVi hVj μi μj hm row e
local notation "q" => GeometricScalars.alignedPair Q split σ indices hVi hVj μi μj hm row e
local notation "w" => GeometricScalars.alignedPlacement Q split σ indices hVi hVj μi μj hm row e
local notation "hs" => GeometricScalars.aligned_short_range Q split σ indices hVi hVj μi μj hm row e
local notation "hl" => GeometricScalars.aligned_long_range Q split σ indices hVi hVj μi μj hm row e

/-- The entire aligned long actor remains faithful after its field relabeling. -/
theorem aligned_long_injective : Function.Injective (q).longMap :=
  (GeometricApplication.long_injective Q split σ indices hVi hVj μi μj hm row).comp
    (Theory.PSL2.sl2FieldAut (η).symm).injective

local notation "hf" => aligned_long_injective Q split σ indices hVi hVj μi μj hm row e

/-- The normalized long–long equation on the geometrically constructed,
whole-actor-aligned pinning, including q=2 and both orientations. -/
theorem long_long (a b : K) : rightCommutator ((q).l 1 b) ((q).l 0 a) = (q).l 2 (a*b) :=
  LongRootApplication.long_long Q split q w hs hl hm row hf a b

/-- Every signed long-root weight for that same aligned pinning. -/
theorem hB_signed_long (t : Kˣ) (positive : Bool) (i : Fin 3) (a : K) :
    ((q).signedRoots e).hB (Units.map e.fixed.toMonoidHom t)*
      ((q).signedRoots e).longSigned positive i (e.fixed a)*
      (((q).signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
    ((q).signedRoots e).longSigned positive i
      (e.fixed ((if positive then ![t.val^2,t.val⁻¹,t.val] i
        else (![t.val^2,t.val⁻¹,t.val] i)⁻¹)*a)) :=
  LongRootApplication.hB_signed_long Q split q w hs hl hm row hf e t positive i a

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricLongRoots
