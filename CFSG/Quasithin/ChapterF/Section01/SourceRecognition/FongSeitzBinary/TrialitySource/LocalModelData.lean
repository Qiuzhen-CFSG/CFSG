module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.SourceFieldApplication

/-!
# Earlier local inputs for reconstructed triality recognition

Bundle only the earlier local models, their field sizes, the radical/kernel
containments and the structural 6E(b) row. The bundle contains no root maps,
module equations, signed relations or comparison. SourceFieldApplication
constructs those from these inputs. This stable boundary lets a geometric
consumer apply the reconstruction without unfolding its universal quotient
inside every local permutation-group isomorphism type.

The ambient F.1.1 marking proves normal generation on the same quotient.
Source: Fong--Seitz I (6E)(b); II (9.22)--(9.26), printed pp.217--218.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
variable {X F K₀ : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  [Field K₀] [Finite K₀] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (indices : Fin 2 ≃ Fin 2)
  (n : ℕ)

/-- Genuine earlier source inputs, without any desired triality relation or comparison. -/
structure LocalModelData where
  short_kernel : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0)
  long_kernel : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1)
  short_model : localGroup Q split (indices 0) ≃* PSL(2,F)
  long_model : localGroup Q split (indices 1) ≃* PSL(2,K₀)
  rotation : rotationOrder Q = 6
  structural : StructuralRow Q split (indices 0) (indices 1)
  cubic_card : Nat.card F = (2^n)^3
  fixed_card : Nat.card K₀ = 2^n

namespace LocalModelData
variable {Q split indices n} (d : LocalModelData (F := F) (K₀ := K₀) Q split indices n)
  {hn : 0 < n}

/-- Construct the entire source pinning and every relation from the earlier data. -/
def rootData (hgen : split.unipotentClosure = ⊤) :
    TrialityPresentation.RootData Q split n hn (SourceFieldApplication.sourceFrobenius F n) (indices 0) :=
  SourceFieldApplication.rootData Q split indices d.short_kernel d.long_kernel d.short_model d.long_model
    d.rotation d.structural d.cubic_card d.fixed_card hgen

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (marking : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

/-- Discharge ambient generation using the actual original or geometric marking. -/
def markedRootData :
    TrialityPresentation.RootData Q split n hn (SourceFieldApplication.sourceFrobenius F n) (indices 0) :=
  d.rootData (A2Source.unipotent_normalClosure_eq_top Q marking h split)
end LocalModelData
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
