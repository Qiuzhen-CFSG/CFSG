module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.LongRoot
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Nonfusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Marked
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FullLongCentralizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.NativeInvolutions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Classes
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FieldTransfer
public import Theory.GroupTheory.PResidual.PerfectImage

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientClasses

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.CommonCentralizers

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.TorusSplitting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OuterSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphConjugate
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedSylowGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.InnerSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OddOuter
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.EndpointFusion

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedCosets

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.ShortSpace
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.ShortNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.ShortCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Order
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Completion

/-!
# Ambient geometry and Sylow equality for the prepared U₅(4) row

The original parabolic cores have the required normalizers. The long-root
center is TI, its full ambient centralizers agree with those in the same
marked extension, and the two Hermitian involution classes remain distinct.
The full-Sylow Thompson identity controls plane-center fusion.

For a represented outer involution, the original Hermitian module detects
the long-root intersection of the derived center of the full C_T(t).
Its invariance and the local saturation place C_T(t) in Syl₂(C_G(t)).
The numerical contradiction compares its order at most 1024 with the
ambient lower bound 65536. Applying the accepted actor representation to
the same action, lift and whole-middle map therefore proves S=T.

This same extension has odd outer degree. Its literal endpoint maps
preserve both involution class predicates on the entire original full
normalizers. Both source orientations and the whole residual H are retained.
Commuting-class incidence proves the actual unique fixed cosets for the
selected short root. The F.4.42 quotient arguments give its full ambient
centralizer containment; comparing both involution centralizers proves the
F.4.43 order for this same extension. Its literal completion and recognition
close the source branch.

Source: Aschbacher–Smith 5.3.1–4 and F.4.31–43, printed pp.658–659,291–296.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original ambient group satisfies the core-center normalizer, long-root
centralizer and two-residual clauses, with the actual root TI group. -/
theorem Preparation.unitaryFive_ambient_local_conditions
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    pResidual 2 G = ⊤ ∧
      (∀ i : Fin 2,
        let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
        P.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
        normalizer ((center (P.pCoreIn 2)).map (P.pCoreIn 2).subtype : Set G) =
          normalizer (![L,residual H] i : Set G)) ∧
      (∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        centralizer ({z} : Set G) ≤ normalizer (residual H : Set G)) ∧
      Nat.card (center (residual H)) = 4 ∧
      IsElementaryAbelian 2 ((center (residual H)).map (residual H).subtype) ∧
      ChapterI.Section06To08.IsTISubgroup ((center (residual H)).map (residual H).subtype) ∧
      normalizer ((center (residual H)).map (residual H).subtype : Set G) =
        normalizer (residual H : Set G) := by
  have hperfect : pResidual 2 G = ⊤ := by
    let := h.qtke.simple
    let : Group.IsPerfect G := ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (_root_.commutator G) inferInstance).resolve_left
        (fun he => h.qtke.nonabelian ((commutator_eq_bot_iff G).mp he))⟩
    exact pResidual_eq_top_of_isPerfect 2
  exact ⟨hperfect,d.unitaryFive_parabolic_core_centers h hH hp U hc,
    d.unitaryFive_central_involution_centralizers h hH hp U hc 1,
    d.unitaryFive_right_center_card h hH hp U hc,
    d.unitaryFive_right_center_fusion h hH hp U hc⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
