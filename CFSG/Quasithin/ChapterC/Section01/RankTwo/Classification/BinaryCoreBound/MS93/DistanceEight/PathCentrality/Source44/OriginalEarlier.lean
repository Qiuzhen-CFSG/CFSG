module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource

/-!+# Original distance-eight inputs for MS93 (4.5)

The proved prescribed replacement closes the source-specific construction of
the marked extended path. Critical-prefix control, the radius calculation and
the selected-product calculation then supply every field of `CoreFactors.Earlier`
from `LocalSource`, `CommonFacts` and b > 4. No replacement, local-control,
nonnatural-exclusion or extended-path premise remains.

The applications retain the actual core factors and the image of H_alpha in
the original MS group. In particular the four-group centralizes the original
component; centralization by the original two-core is a separate later result.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4)--(4.4.5), printed pp.890--895, and (4.5.1), p.896.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- All preceding source inputs for (4.5), with prescribed replacement discharged. -/
theorem earlier (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    CoreFactors.Earlier R geometry :=
  SourceEarlier.earlier common hb (Replacement.OriginalSource.prescribedReplacement common hb)

/-- The original (4.4) conclusions on the actual quotient action and edge indices. -/
theorem conclusions (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    geometry.b R = 8 ∧
      (∀ a, color R a = false → Nonempty (Escape.NaturalSectionAt a (V R a) (Z R a))) ∧
      (∀ a, color R a = false → ⁅V R a, Q R a⁆ ≤
        (center (stabilizer R a)).map (stabilizer R a).subtype) ∧
      (∀ a t, color R a = false → Adjacent R a t →
        (Z R t).relIndex (Z R a) = 2 ∧ (Q R a).relIndex (Q R t) = 4) := by
  have h := earlier common hb
  exact ⟨h.distance, h.natural_section, h.centrality,
    fun a t ha hat => ⟨h.edge_Z_index a t ha hat, h.edge_Q_index a t ha hat⟩⟩

/-- Apply the constructed Earlier input to the literal core factors. -/
theorem factor_inclusions (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    H R (alpha R) ≤ core R (alpha R) ⊓
        centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) ∧
      U R (alpha R) ⊔ H R (alpha R) ≤
        (center (core R (alpha R))).map (core R (alpha R)).subtype ∧
      Disjoint (U R (alpha R)) (H R (alpha R)) :=
  (earlier common hb).factor_inclusions common

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L T : Subgroup J} {h : Input κ L T} (t : InputSetup h)
open DistanceEight.PathCentrality.Source44

/-- The original MS four-group application, with every Earlier premise discharged. -/
theorem reducedCentralFour_of_original_source
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) :
    Nat.card t.reducedCentralFour = 4 ∧ IsElementaryAbelian 2 t.reducedCentralFour ∧
      t.reducedCentralFour ≤ commutatorCore L ∧
      t.reducedCentralFour ≤ centralizer (L : Set J) := by
  have earlier := OriginalEarlier.earlier common hb
  exact ⟨t.reducedCentralFour_card common earlier,
    t.reducedCentralFour_elementary common earlier,
    t.reducedCentralFour_le_commutatorCore common earlier,
    t.reducedCentralFour_centralizes_component earlier⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
