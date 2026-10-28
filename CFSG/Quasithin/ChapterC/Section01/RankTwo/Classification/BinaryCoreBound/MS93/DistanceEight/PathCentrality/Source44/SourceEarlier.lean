module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Radius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Product
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.RegularSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.SourceCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCentralFour

/-!
# Source (4.4) and the Earlier record from prescribed replacement

The proved source natural-section theorem supplies critical-prefix control
and the regular extended path. The radius-image calculation uses only those
actual prefixes and endpoint actors; the selected-product calculation uses
the same restricted controls. Together they prove distance eight, the full
radius natural section, local centrality and both edge indices, filling the
literal Earlier record for (4.5).

Only prescribed replacement remains independent. Its source-specific wrapper
reduces this premise further to normalization of the escaping radius image
of order two, retaining the full failed-span hypotheses. No universal local
commutator control or arbitrary-pair orientation is assumed.

The final consumer includes H_alpha back into the original binary MS ambient
group and derives its elementary order-four structure. Centrality under the
original two-core remains the separate characteristic-replacement transport
problem; no such action statement is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)--(4.4.5), pp.890--895,
and (4.5.1), p.896; Aschbacher--Smith C.1.34(4), pp.136--137.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Construct every Earlier field from the original source facts and prescribed replacement. -/
theorem earlier (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p) : CoreFactors.Earlier R geometry := by
  have extended := RegularSource.extended_of_replacement common hb replacement
  obtain ⟨e⟩ := extended (alpha R) rfl
  have hsix := RegularSource.six_lt common hb
  have hn := fun c hc => Radius.natural_section common hsix e (c := c) hc
  obtain ⟨hd,hc,hi⟩ := Product.conclusions common hsix
    (RegularSource.criticalPrefixControl common hb) replacement hn e
  exact {
    distance := hd
    natural_section := hn
    centrality := hc
    edge_Z_index := fun a t ha hat => (hi a t ha hat).1
    edge_Q_index := fun a t ha hat => (hi a t ha hat).2
    extended := extended
    replacement := fun _ _ p hp => replacement p hp }

/-- The literal image-two normalization is sufficient for the independent replacement step. -/
theorem earlier_of_two_image_normalized (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (hnorm : Replacement.SourceCritical.FailedSpanTwoImageNormalization R geometry) :
    CoreFactors.Earlier R geometry :=
  earlier common hb
    (Replacement.SourceCritical.prescribedReplacement_of_two_image_normalized common hb hnorm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L T : Subgroup J} {h : Input κ L T} (t : InputSetup h)
open DistanceEight.PathCentrality DistanceEight.PathCentrality.Source44

theorem reducedCentralFour_of_replacement
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (replacement : ∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) :
    Nat.card t.reducedCentralFour = 4 ∧ IsElementaryAbelian 2 t.reducedCentralFour ∧
      t.reducedCentralFour ≤ commutatorCore L ∧
      t.reducedCentralFour ≤ centralizer (L : Set J) := by
  have earlier := SourceEarlier.earlier common hb replacement
  exact ⟨t.reducedCentralFour_card common earlier,
    t.reducedCentralFour_elementary common earlier,
    t.reducedCentralFour_le_commutatorCore common earlier,
    t.reducedCentralFour_centralizes_component earlier⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
