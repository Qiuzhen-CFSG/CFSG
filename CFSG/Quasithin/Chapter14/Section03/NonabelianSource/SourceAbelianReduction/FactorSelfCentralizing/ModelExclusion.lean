module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Quotient
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.SmallModels
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# Assembly of the remaining marked model exclusions in 14.3.20

The actual elementary factor excludes the alternating and odd rows. The
remaining tasks are the quaternion extension in the quotient centralizer,
the even model rows, and the sporadic model rows. Their interfaces retain
the same marked point, quotient, Sylow placement and conjugation action.
The two model tasks may use the local extension explicitly and proceed
independently of its construction; final assembly must discharge all three.

This module proves the conditional reduction and its actual factor consumer.
It does not assert that any of the three source obligations is proved.
Source: Aschbacher--Smith, 14.3.20, p.998 and 1.1.5(3), pp.501--503.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

namespace MarkedPoint
variable {F : InvariantFlag T V 2} {L A : Subgroup G} (P : MarkedPoint F L A)

/-- The source extension in the actual quotient centralizer. The normal kernel
is the central product of two quaternion eights, and the quotient is S₃ × S₃.
No splitting, abstract order-only description or replacement centralizer is used. -/
def QuotientCentralizerStructure (z : P.globalCentralizer) : Prop :=
  ∃ W : Subgroup (centralizer ({P.pointQuotientMap z} : Set P.PointQuotient)),
    W.index ≤ 2 ∧ ∃ (Q : Subgroup W) (_ : Q.Normal),
      Nonempty (QuaternionCentralProductData Q) ∧
      Nonempty ((W ⧸ Q) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

end MarkedPoint

/-- The local extension calculation in the final paragraph of 14.3.20.
This specification is an outstanding obligation, not a source theorem. -/
def QuotientCentralizerSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ∀ hA : ElementaryFactor F L A, A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G) (hz : F.Vi 1 = zpowers z),
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      P.globalCentralizer.pCoreIn 2 = zpowers P.element →
      P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz)

/-- The remaining even rows, conditional on the independent local extension.
It retains the original component, model equivalence and action. -/
def EvenExclusionSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ∀ hA : ElementaryFactor F L A, A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G) (hz : F.Vi 1 = zpowers z),
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      P.globalCentralizer.pCoreIn 2 = zpowers P.element →
      P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz) →
      P.EvenComponent z → False

/-- The remaining sporadic rows, conditional on the independent local extension.
The actual two-core quotient and two-central action remain explicit. -/
def SporadicExclusionSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ∀ hA : ElementaryFactor F L A, A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G) (hz : F.Vi 1 = zpowers z),
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      P.globalCentralizer.pCoreIn 2 = zpowers P.element →
      P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz) →
      P.SporadicComponent z → False

/-- Assemble the local structure and the two surviving genuine model families.
The alternating and odd branches are discharged by the actual elementary factor. -/
theorem modelExclusionSource_of_local_inputs
    (F : InvariantFlag T V 2) (L : Subgroup G)
    (hlocal : QuotientCentralizerSource F L)
    (heven : EvenExclusionSource F L) (hsporadic : SporadicExclusionSource F L) :
    ModelExclusionSource F L := by
  intro A hA hlt P z hz hgeom hSylow hcore hmodel
  have hstructure := hlocal A hA hlt P z hz hgeom hSylow hcore
  rcases P.classifiedComponent_cases hA z hmodel with h | h
  · exact heven A hA hlt P z hz hgeom hSylow hcore hstructure h
  · exact hsporadic A hA hlt P z hz hgeom hSylow hcore hstructure h

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The original factor consumer, with only the explicit local/model obligations
in addition to its independent four-center and global-core inputs. -/
theorem factorSelfCentralizing_of_local_model_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hgeometry : FourCenterSource F (sourceResidual M Mc))
    (hcore : CoreComponentSource F (sourceResidual M Mc))
    (hlocal : QuotientCentralizerSource F (sourceResidual M Mc))
    (heven : EvenExclusionSource F (sourceResidual M Mc))
    (hsporadic : SporadicExclusionSource F (sourceResidual M Mc)) :
    FactorSelfCentralizing F (sourceResidual M Mc) :=
  factorSelfCentralizing_of_source_inputs hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hs hgeometry hcore
    (modelExclusionSource_of_local_inputs F (sourceResidual M Mc) hlocal heven hsporadic)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
