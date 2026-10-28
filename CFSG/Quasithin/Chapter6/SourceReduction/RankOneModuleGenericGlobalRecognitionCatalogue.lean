module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionRee
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionExceptional
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryFive

/-!
# Complete model comparisons for the diagram branch of 5.2.6

`ConcreteAmalgamComparison` records actual inclusion-amalgam isomorphisms
in either orientation to the seven source Lie rows, including the degree-two
unitary extension and special U₅(4) row. The fixed exceptional catalogue
uses parabolic equivalence, retaining the weaker Hall–Janko convention.
This definition is an output contract, not an exhaustive classification theorem.

The original diagram-selected factor is nonshort, has binary PSL₂ quotient,
and has two noncentral layers in its literal residual-core intersection.
The proved comparisons exclude every constructor on this same factor:
natural blocks, unitary radicals, G₂ and triality chief layers, Suzuki and
SU₃ quotients, and solvable exceptional parabolics. The Chapter12 consumer
uses this complete exclusion to identify R with all of O²(H), conditional
on genuine classification and the separate core bound and uniqueness inputs.

The source construction of a comparison and ambient completion recognition
remain with qt-d-1222-rankone-generic-global. The final source owners are
qt-d-1222-rankone-generic and qt-d-1361-source; uniqueness retains its
independent producer. This module asserts no global model isomorphism.
Source: Aschbacher–Smith 5.2.6, printed pp.650–651, and F.1.12, pp.262–264
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook

/-- Actual comparisons with the concrete source catalogue. This is an output
contract for the remaining exhaustive classification, not that theorem. -/
inductive ConcreteAmalgamComparison {X B Y : Type*} [Group X] [Group B] [Group Y]
    (α : RankTwoAmalgam X B Y) : Prop
  | linear (F : Type) [Field F] [Finite F] [CharP F 2]
      (m : ℕ) (hm : 0 < m) (hF : Nat.card F = 2^m)
      (he : Nonempty (RankTwoAmalgam.Iso α (LieModels.LinearThree.amalgam F)) ∨
        Nonempty (RankTwoAmalgam.Iso α (LieModels.LinearThree.amalgam F).reverse))
  | symplectic (F : Type) [Field F] [Finite F] [CharP F 2]
      (m : ℕ) (hm : 0 < m) (hF : Nat.card F = 2^m)
      (he : Nonempty (RankTwoAmalgam.Iso α (LieModels.SymplecticFour.amalgam F)) ∨
        Nonempty (RankTwoAmalgam.Iso α (LieModels.SymplecticFour.amalgam F).reverse))
  | g2 (F : Type) [Field F] [Finite F] [CharP F 2]
      (he : Nonempty (RankTwoAmalgam.Iso α (LieModels.G2.amalgam (F := F))) ∨
        Nonempty (RankTwoAmalgam.Iso α (LieModels.G2.amalgam (F := F)).reverse))
  | triality (m : ℕ) (hm : 0 < m)
      (he : Nonempty (RankTwoAmalgam.Iso α
          (LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
        Nonempty (RankTwoAmalgam.Iso α
          (LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse))
  | ree (m : ℕ)
      (he : Nonempty (RankTwoAmalgam.Iso α (LieModels.ReeFour.amalgam m)) ∨
        Nonempty (RankTwoAmalgam.Iso α (LieModels.ReeFour.amalgam m).reverse))
  | unitary (m : ℕ) (hm : 1 ≤ m)
      (he : Nonempty (RankTwoAmalgam.Iso α (LieModels.UnitaryFour.amalgam m hm)) ∨
        Nonempty (RankTwoAmalgam.Iso α (LieModels.UnitaryFour.amalgam m hm).reverse))
  | unitaryExtension (m : ℕ) (hm : 1 ≤ m)
      (he : Nonempty (RankTwoAmalgam.Iso α (LieModels.UnitaryFour.Extension.amalgam m hm)) ∨
        Nonempty (RankTwoAmalgam.Iso α (LieModels.UnitaryFour.Extension.amalgam m hm).reverse))
  | unitaryFive (M : UnitaryFive.Model 4)
      (he : Nonempty (RankTwoAmalgam.Iso α M.amalgam) ∨
        Nonempty (RankTwoAmalgam.Iso α M.amalgam.reverse))
  | exceptional (c : ExceptionalModels.Case)
      (he : ExceptionalModels.ParabolicModel c α ∨ ExceptionalModels.ParabolicModel c α.reverse)

/-- A selected diagram factor is incompatible with every listed concrete
comparison. All factor, layer and field hypotheses concern the same R. -/
theorem Preparation.not_diagram_comparison
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n f : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R) (hlin : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f))
    (hnot : ¬ ChapterC.IsShort R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R)) :
    ¬ ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  intro hc
  cases hc with
  | linear F m hm hF he =>
    exact hnot (d.linear_amalgam_blocks h hTH hp F hm hF he).2.2.2.1
  | symplectic F m hm hF he =>
    exact hnot (d.symplectic_amalgam_blocks h hTH hp F hm hF he).2.2.2.1
  | g2 F he =>
    have hn := d.not_g2_amalgams (F := F) h hTH hN hp hl
    exact he.elim hn.1 hn.2
  | triality m hm he =>
    have hn := d.not_triality_amalgams h hTH hp hl m hm
    exact he.elim hn.1 hn.2
  | ree m he =>
    have hn := d.not_ree_amalgams h hTH hp hlin m
    exact he.elim hn.1 hn.2
  | unitary m hm he =>
    have hn := d.not_unitary_amalgams h.sylow_normalizes hN hp hl m hm
    exact he.elim hn.1 hn.2.1
  | unitaryExtension m hm he =>
    have hn := d.not_unitary_amalgams h.sylow_normalizes hN hp hl m hm
    exact he.elim hn.2.2.1 hn.2.2.2
  | unitaryFive M he =>
    have hn := d.not_unitaryFive_amalgams h hTH hp hlin M
    exact he.elim hn.1 hn.2
  | exceptional c he =>
    have hn := d.not_exceptional_parabolic_models h hp c
    exact he.elim hn.1 hn.2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
