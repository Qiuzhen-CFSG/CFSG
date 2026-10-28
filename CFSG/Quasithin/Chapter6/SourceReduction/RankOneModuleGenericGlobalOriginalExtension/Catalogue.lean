module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.ReducedRows
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Linear
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Triality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Ree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.BinaryTypes
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.SymplecticNativeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2NativeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityAllDegrees
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFiveNativeApplication

/-!
# Original and reduced marked alternatives at the generic catalogue consumer

For every prepared perfect selected R, the original normalized Borel removes
the outer extensions in the ordinary rows. The U₄ branch retains its actual
degree-two graph extension, and the quasithin U₅ sieve is applied before
restricting to field four. Binary local and full-endpoint quotient clauses
are excluded separately; exceptional rows use only parabolic equivalence.
The reduced version first restores the whole original inclusion diagram.

The two alternative predicates below specify genuine earlier recognition
inputs. No exhaustiveness theorem is asserted. In particular the reduced
comparisons concern S₀ = O₂(B), while the conclusion concerns the original
S = O₂(N_G(L) ∩ H). Equality of these subgroups is proved only in the rows
where it is valid. Every regular comparison retains both endpoint squares
and the whole odd Borel. Neither R = O²(H) nor S = T is assumed.

Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`); DGS, *Groups and Graphs*, (15.1)--(15.3),
pp.226--231 (`refs/groups-and-graphs.pdf`). Exhaustiveness remains with
qt-dgs85-source-assembly; final generic assembly remains with this owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.Source.DGS85.OriginalExtension
open ChapterF.GreenBook
namespace OriginalExtension

/-- Broad original marked extension data, including the weaker exceptional
and binary type clauses. This is an input contract, not classification. -/
inductive Alternatives {G : Type*} [Group G] (L R S : Subgroup G) : Prop
  | linear (F : Type) [Field F] [Finite F] [CharP F 2]
      (m : ℕ) (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
      (e : Nonempty (OriginalLinear.Marking L R S F point))
  | symplectic (F : Type) [Field F] [Finite F] [CharP F 2]
      (m : ℕ) (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
      (e : Nonempty (OriginalSymplectic.Marking F point L R S))
  | g2 (F : Type) [Field F] [Finite F] [CharP F 2] (short : Bool)
      (e : Nonempty (OriginalG2.Marking F short L R S))
  | triality (m : ℕ) (hm : 0 < m) (a : _root_.Triality.Standard.Parabolics.Node)
      (e : Nonempty (OriginalTriality.Marking m hm a L R S))
  | ree (m : ℕ) (a : ReeF4.LargeLocalSeeds.Side)
      (e : Nonempty (OriginalRee.Marking m a L R S))
  | unitaryFour (m : ℕ) (hm : 1 ≤ m) (point : Bool)
      (e : Nonempty (OriginalUnitaryFour.Marking m hm point L R S))
  | unitaryFive (q : ℕ) (hq : IsPrimePow q) (heven : Even q)
      (M : UnitaryFive.Model q) (line : Bool)
      (hi : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier))
      (e : Nonempty (OriginalUnitaryFive.Marking M line L R S))
  | exceptional (c : ExceptionalModels.Case)
      (he : ExceptionalModels.ParabolicModel c (sourceParabolicAmalgam ![L,R] S) ∨
        ExceptionalModels.ParabolicModel c (sourceParabolicAmalgam ![L,R] S).reverse)
  | binaryLocal (i : Fin 2) (he : ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 2)
  | binaryParabolic (i : Fin 2) (he : ClassicalGroup.IsPSL
      (ChapterF.Source.parabolic ![L,R] S i ⧸ pCore 2 (ChapterF.Source.parabolic ![L,R] S i)) 2 2)

/-- Actual reduced model comparisons in both orientations, all positive
field degrees, and the original binary structural quotient conventions.
No original model comparison or extension collapse is included as a premise. -/
inductive ReducedAlternatives {G : Type*} [Group G] (L R S : Subgroup G) : Prop
  | linear (F : Type) [Field F] [Finite F] [CharP F 2]
      (m : ℕ) (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![L,R] S) (LinearNative.amalgam F point)))
  | symplectic (F : Type) [Field F] [Finite F] [CharP F 2]
      (m : ℕ) (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![L,R] S) (SymplecticNative.amalgam F point)))
  | g2 (F : Type) [Field F] [Finite F] [CharP F 2] (short : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![L,R] S) (G2Native.amalgam F short)))
  | triality (m : ℕ) (hm : 0 < m) (point : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![L,R] S) (TrialityNative.amalgam m hm point)))
  | ree (m : ℕ) (point : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![L,R] S) (ReeNative.amalgam m point)))
  | unitaryFour (m : ℕ) (hm : 1 ≤ m) (point : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![L,R] S) (UnitaryFourNative.amalgam m hm point)))
  | unitaryFive (q : ℕ) (hq : IsPrimePow q) (heven : Even q)
      (M : UnitaryFive.Model q) (line : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![L,R] S) (UnitaryFiveNative.amalgam M line)))
  | exceptional (c : ExceptionalModels.Case)
      (he : ExceptionalModels.ParabolicModel c (reducedAmalgam ![L,R] S) ∨
        ExceptionalModels.ParabolicModel c (reducedAmalgam ![L,R] S).reverse)
  | binaryLocal (i : Fin 2) (he : ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 2)
  | binaryJoin (i : Fin 2) (he : ClassicalGroup.IsPSL
      ((![L,R] i ⊔ ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] S : Subgroup G) ⧸
        pCore 2 (![L,R] i ⊔ ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] S : Subgroup G)) 2 2)
  | binaryParabolic (i : Fin 2) (he : ClassicalGroup.IsPSL
      (ChapterF.Source.parabolic ![L,R] (ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] S) i ⧸
        pCore 2 (ChapterF.Source.parabolic ![L,R]
          (ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] S) i)) 2 2)
end OriginalExtension

namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
include d h hTH hp

/-- Consumer-specific restriction of every broad original marked extension.
All extra endpoint-action and extension-collapse premises are discharged. -/
theorem concreteComparison_of_original_alternatives
    (ha : OriginalExtension.Alternatives L R (sourceS L H)) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  cases ha with
  | linear F m hm hF point e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_original_linear h hTH hp F hm hF point e
  | symplectic F m hm hF point e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_original_symplectic h hTH hp F hm hF point e
  | g2 F short e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_original_g2 h hTH hp F short e
  | triality m hm a e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_original_triality h hTH hp m hm a e
  | ree m a e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_original_ree h hTH hp m a e
  | unitaryFour m hm point e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_original_unitaryFour h hTH hp m hm point e
  | unitaryFive q hq heven M line hi e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_original_unitaryFive h hTH hp hq heven M line hi e
  | exceptional c he =>
    have hn := d.not_exceptional_parabolic_models h hp c
    exact (he.elim hn.1 hn.2).elim
  | binaryLocal i he => exact (d.not_binary_factor_quotient h hTH hp i he).elim
  | binaryParabolic i he => exact (d.not_binary_parabolic_quotient h hp i he).elim

/-- The literal reduced catalogue restores a comparison for EVERY prepared
perfect selected R, retaining the original S and whole odd overlap. -/
theorem concreteComparison_of_reduced_alternatives
    (ha : OriginalExtension.ReducedAlternatives L R (sourceS L H)) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  cases ha with
  | linear F m hm hF point e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_reduced_linear h hTH hp F hm hF point e
  | symplectic F m hm hF point e =>
    obtain ⟨e⟩ := e
    exact concreteComparison_of_reduced_symplectic d h hTH hp F hm hF point e
  | g2 F short e =>
    obtain ⟨e⟩ := e
    exact concreteComparison_of_reduced_g2 d h hTH hp F short e
  | triality m hm point e =>
    obtain ⟨e⟩ := e
    exact concreteComparison_of_reduced_triality_all_degrees d h hTH hp m hm point e
  | ree m point e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_reduced_ree h hTH hp m point e
  | unitaryFour m hm point e =>
    obtain ⟨e⟩ := e
    exact d.concreteComparison_of_reduced_unitaryFour h hTH hp m hm point e
  | unitaryFive q hq heven M line e =>
    obtain ⟨e⟩ := e
    exact concreteComparison_of_reduced_unitaryFive d h hTH hp hq heven M line e
  | exceptional c he =>
    exact (not_reduced_exceptional_parabolicModels d h hTH hp c he).elim
  | binaryLocal i he => exact (d.not_binary_factor_quotient h hTH hp i he).elim
  | binaryJoin i he => exact (d.not_binary_reduced_localJoin_quotient h hTH hp i he).elim
  | binaryParabolic i he => exact (d.not_binary_reduced_parabolic_quotient h hTH hp i he).elim
end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
