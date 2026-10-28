module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.LinearCovered
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.SymplecticCovered
/-!
# Cartan construction at the actual model exponent

The marked Bender, exchanged and diagram-active rows construct Cartan
witnesses at their field exponent c. The complete covered-Borel theorems
supply Hall control in both diagram families when c>1. No equality between
c and the original generation parameter is used or asserted.

Source: Aschbacher–Smith E.2.2 and E.6.27, printed pp.215–216,257.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Subgroup ChapterB
variable {X : Type*} [Group X] [Finite X]
theorem bender_intrinsic_at (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {c : ℕ} (hcpos : 0 < c) {K : Subgroup X} (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hm : BenderModel (minimalParabolicMax S hP) K c) :
    Nonempty (IntrinsicHallCartanData S hP c) :=
  intrinsic_of_cyclic_and_hallControl S hP hcpos (bender_hallControl S hP hK hc hm) hm.cyclic

theorem exchanged_intrinsic_at (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {c : ℕ} (hcpos : 0 < c) {K : Subgroup X} (hK : K.IsCComponent)
    (hqs : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K))
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S)
    (hm : ExchangedModel (minimalParabolicMax S hP) K c) :
    Nonempty (IntrinsicHallCartanData S hP c) := by
  obtain ⟨N,hNM,hn,hgen,hd⟩ := ExchangedHall.normal_section hc hK hqs
    (minimalParabolicMax_spec S hP).2 (ExchangedHall.model_overlap_commutator hm)
  exact intrinsic_of_cyclic_and_hallControl S hP hcpos
    (ExchangedHall.hallControl_of_normal_section S hP N hNM hn hgen hd) hm.cyclic

theorem diagram_intrinsic_at (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {c : ℕ} (hcpos : 1 < c) {K : Subgroup X} (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hm : DiagramModel (minimalParabolicMax S hP) K S c) :
    Nonempty (IntrinsicHallCartanData S hP c) := by
  apply intrinsic_of_cyclic_and_hallControl S hP (by omega) _ hm.cyclic
  rcases hm with ⟨F,hF,hfin,hchar,_,hcard,e,he,_⟩ | ⟨F,hF,hfin,hchar,_,hcard,e,he,_⟩
  · exact DiagramHall.linear_hallControl hcpos hcard S hP K hK hc e he
  · exact DiagramHall.symplectic_hallControl S hP hK hc hcpos hcard e he

/-- Every characteristic-two marked row gives an actual Cartan witness at its
field exponent, including the original covered Borel. -/
theorem ReducedCases.intrinsic_at (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {c : ℕ} (hcpos : 1 < c) {K : Subgroup X} (hK : K.IsCComponent)
    (hqs : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K))
    (hr : ReducedCases (minimalParabolicMax S hP) K S c) :
    Nonempty (IntrinsicHallCartanData S hP c) := by
  cases hr with
  | exchanged hc hm => exact exchanged_intrinsic_at S hP (by omega) hK hqs hc hm
  | bender hc hm => exact bender_intrinsic_at S hP (by omega) hK hc hm
  | diagram hc hm => exact diagram_intrinsic_at S hP hcpos hK hc hm
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
