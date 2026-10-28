module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.SignedTorusApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.Application

/-!
# Full marked recognition from the reconstructed triality source roots

The positive tensor/module reconstruction and the complete signed torus
calculation now instantiate every field of BruhatRootData. The original
normal-generation premise supplies signed generation. The actual geometric
Weyl lifts give both literal simple quotient classes, in either orientation.
The existing presentation comparison then identifies the original quotient,
its complete Borel and both standard parabolics with the genuine triality
carrier. The original F.1.1 hypothesis discharges normal generation for
any supplied original or geometric amalgam marking.

No source module, coefficient, signed action or torus relation is assumed.
The earlier split geometry, actual local field models and structural 6E(b)
row remain explicit source inputs. All positive binary exponents are retained.
Source: Fong--Seitz I (6E)(b), II §9B; DGS Theorem D, printed p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Representation Representation.SL2.BinarySmall
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.FullApplication
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
local notation "i" => indices 0
local notation "j" => indices 1
local notation "si" => UnitarySource.actorReflection Q split i
local notation "q" => GeometricScalars.alignedPair Q split σ indices hVi hVj μi μj hm row e
local notation "w" => GeometricScalars.alignedPlacement Q split σ indices hVi hVj μi μj hm row e
local notation "hs" => GeometricScalars.aligned_short_range Q split σ indices hVi hVj μi μj hm row e
local notation "hl" => GeometricScalars.aligned_long_range Q split σ indices hVi hVj μi μj hm row e
local notation "cc" => StructuralApplication.positiveCommutations Q split (q) (w) (hs) (hl) hm row

local notation "pos" => TensorPositiveApplication.positiveData Q split σ indices hVi hVj μi μj hm row e


/-- All source relations and generation, using the literal ambient normal-generation premise. -/
def bruhatData (hgen : split.unipotentClosure = ⊤) : TrialityPresentation.BruhatRootData (pos) where
  signed := TensorPositiveApplication.signedData Q split σ indices hVi hVj μi μj hm row e
  weyl := (q).weylRelations e (pos).root_relations
  torus := SignedTorusApplication.torusRelations Q split σ indices hVi hVj μi μj hm row e
  generates := by
    change ((q).signedRoots e).signedClosure = ⊤
    rw [(w).signedClosure_eq_unipotentClosure Q split (q) e (pos).positive,hgen]


/-- Complete source data for the existing marked-presentation comparison.
No module, coefficient, signed-root or torus equations remain as inputs. -/
def rootData (hgen : split.unipotentClosure = ⊤) :
    TrialityPresentation.RootData Q split n hn σ (indices 0) where
  positive := pos
  bruhat := bruhatData Q split σ indices hVi hVj μi μj hm row e hgen
  arms_mem := by
    change ((q).signedRoots e).nA 1 ∈ Q.tits.N
    rw [(q).nA_one,← (w).short]
    exact ((w).lift 0).property
  arms_class := by
    have he : (⟨((q).signedRoots e).nA 1,by
        rw [(q).nA_one,← (w).short]; exact ((w).lift 0).property⟩ : Q.tits.N) = (w).lift 0 := by
      apply Subtype.ext
      exact ((q).nA_one e).trans (w).short.symm
    change QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
      ⟨((q).signedRoots e).nA 1,_⟩ = Q.simple (indices 0)
    rw [he]
    exact (w).simple 0
  central_mem := by
    change ((q).signedRoots e).nB 1 ∈ Q.tits.N
    rw [(q).nB_one,← (w).long]
    exact ((w).lift 1).property
  central_class := by
    have he : (⟨((q).signedRoots e).nB 1,by
        rw [(q).nB_one,← (w).long]; exact ((w).lift 1).property⟩ : Q.tits.N) = (w).lift 1 := by
      apply Subtype.ext
      exact ((q).nB_one e).trans (w).long.symm
    have hij : indices 1 = 1-indices 0 := by
      exact (show ∀ a b : Fin 2, a ≠ b → b = 1-a by decide) _ _
        (indices.injective.ne (by decide))
    change QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
      ⟨((q).signedRoots e).nB 1,_⟩ = Q.simple (1-indices 0)
    rw [he,← hij]
    exact (w).simple 1


section Marked
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (marking : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

/-- Original F.1.1 discharges normal generation on this quotient, including q=2. -/
def markedRootData : TrialityPresentation.RootData Q split n hn σ (indices 0) :=
  rootData Q split σ indices hVi hVj μi μj hm row e
    (A2Source.unipotent_normalClosure_eq_top Q marking h split)


local notation "d" => markedRootData Q split σ indices hVi hVj μi μj hm row e marking h

/-- The actual full triality comparison, preserving the supplied original or geometric marking. -/
def comparison := (d).comparison marking

include Q split σ indices hVi hVj μi μj hm row e marking h in
/-- The completed source reconstruction supplies the literal catalogue consumer. -/
theorem concreteComparison : Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  (d).concreteComparison marking

/-- The same ambient equivalence carries the complete source Borel onto the model Borel. -/
theorem full_borel : Q.tits.B.map (d).bruhat.quotientEquiv.toMonoidHom =
    Parabolics.borel (binaryParameters n hn) := (d).bruhat.quotientEquiv_borel

/-- The source Sylow image uses the original marking and the very same ambient equivalence. -/
theorem source_sylow_image :
    (MarkedLocal.sylowMap Q marking h).range.map (d).bruhat.quotientEquiv.toMonoidHom =
      Parabolics.unipotent (binaryParameters n hn) :=
  TrialityPresentation.source_sylow_image marking h (d)

/-- Both endpoint maps are restrictions of the same ambient equivalence. -/
theorem both_endpoints (r : Fin 2) :
    (Q.tits.standardParabolic {Q.simple r}).map (d).bruhat.quotientEquiv.toMonoidHom =
      TrialityPresentation.flagVertex n hn (indices 0) r := (d).quotientEquiv_vertex r

/-- The entire common Borel follows the literal original middle map. -/
theorem commonBorel_apply (b : commonBorel L S) :
    (((d).comparison marking).middle ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b) :
      BinaryCarrier n hn) = (d).bruhat.quotientEquiv (MarkedLocal.borelMap Q marking h b) :=
  TrialityPresentation.comparison_commonBorel_apply marking h (d) b

end Marked
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.FullApplication
