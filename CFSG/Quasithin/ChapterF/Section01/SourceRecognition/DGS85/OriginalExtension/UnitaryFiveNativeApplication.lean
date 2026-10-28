module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFiveNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ResidualMarking
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFive

/-!
# Reduced U₅ markings at the original selected-factor consumer

The actual quasithin field sieve and native restoration construct the original
residual and full-endpoint marking. The existing normalized-Borel argument
then makes the same original S inner and contained in both selected factors.
It supplies both original core equalities and a compatible original comparison
for every perfect selected R, without identifying R with the whole residual.

Both orientations and arbitrary even prime powers enter the sieve. The
constructed isomorphism includes the full original overlap, so odd Borel
elements survive its later restriction. Reduced recognition remains explicit.
Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith F.1.12, pp.263–264,
and 5.2.6, pp.650–651.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric GreenBook.UnitaryFive

/-- Construct the original marking from the literal reduced pair after the
proved quasithin sieve. No original-marking or inner-action premise is used. -/
theorem exists_original_unitaryFive_marking_of_reduced_iso
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    {L R S : Subgroup G} (h : HypothesisF11 ![L,R] S)
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : Model q) (line : Bool)
    (e : Iso (reducedAmalgam ![L,R] S) (UnitaryFiveNative.amalgam M line)) :
    Nonempty (Global.OriginalUnitaryFive.Marking M line L R S) := by
  have hq4 := UnitaryFiveNative.field_eq_four_of_reduced_iso hG hq heven M line e
  subst q
  obtain ⟨E,F,hl,hr,_⟩ := UnitaryFiveNative.exists_original_extension_iso h M line e
  exact ⟨residualMarkingOfRestoredIso h E F e.left e.right hl hr⟩

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : Model q) (line : Bool)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (UnitaryFiveNative.amalgam M line))
include d h hTH hp hq heven e

/-- The actual selected factors force the source field, orientation and local
quotients, starting only with the marked reduced row. -/
theorem unitaryFive_original_parameters_of_reduced_iso :
    q = 4 ∧ line = false ∧ n = 4 ∧ IsSU (R ⧸ pCore 2 R) 3 4 := by
  have hq4 := UnitaryFiveNative.field_eq_four_of_reduced_iso
    h.qtke.quasithin hq heven M line e
  subst q
  obtain ⟨f⟩ := exists_original_unitaryFive_marking_of_reduced_iso
    h.qtke.quasithin (d.hypothesisF11 h hTH) hq heven M line e
  exact ⟨rfl,d.original_unitaryFive_marked_orientation h hTH hp M line f,
    d.original_unitaryFive_marked_parameters h hTH hp M line f⟩

/-- The same original S lies in both selected factors, and adjoining it
changes neither original two-core. -/
theorem unitaryFive_original_collapse_of_reduced_iso :
    Global.sourceS L H ≤ R ∧ Global.sourceS L H ≤ L ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧
      (L ⊔ Global.sourceS L H).pCoreIn 2 = L.pCoreIn 2 := by
  have hq4 := UnitaryFiveNative.field_eq_four_of_reduced_iso
    h.qtke.quasithin hq heven M line e
  subst q
  obtain ⟨f⟩ := exists_original_unitaryFive_marking_of_reduced_iso
    h.qtke.quasithin (d.hypothesisF11 h hTH) hq heven M line e
  have ho := d.original_unitaryFive_marked_orientation h hTH hp M line f
  subst line
  have hs := d.original_unitaryFive_sourceS_le h hTH hp M f
  exact ⟨hs.1,hs.2,d.original_unitaryFive_core_eq h hTH hp M f⟩

/-- Discharge the original-marking premise of the existing concrete catalogue
consumer for the same arbitrary perfect selected R. -/
theorem concreteComparison_of_reduced_unitaryFive :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hq4 := UnitaryFiveNative.field_eq_four_of_reduced_iso
    h.qtke.quasithin hq heven M line e
  subst q
  obtain ⟨f⟩ := exists_original_unitaryFive_marking_of_reduced_iso
    h.qtke.quasithin (d.hypothesisF11 h hTH) hq heven M line e
  exact d.concreteComparison_of_original_unitaryFive h hTH hp hq heven M line
    (SourceCompletion.UnitaryNonbinary.five_conj_injective M) f

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
