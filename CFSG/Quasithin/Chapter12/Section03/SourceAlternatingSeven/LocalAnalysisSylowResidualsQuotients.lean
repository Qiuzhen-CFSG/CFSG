module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResiduals
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsTransport
public import Theory.SpecificGroups.Alternating.SixCoverInSeven
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsQuotientsSource

/-!
# The simple two-core quotients for the A₇ Sylow-normalizer argument

The contrary-normalizer branch and the original natural coordinates give
L/O₂(L) ≅ A₇ by the source block construction. The literal perfect residual
C_L(e₆)^∞ lies in L. Its two-core quotient has order dividing 2520, excluding
the triple A₆ cover; the marked central quotient therefore gives the actual
A₆ two-core quotient.

The final consumer removes both quotient premises from the ambient-residual
constructor. Only its independent coset C-component input remains explicit;
this module does not construct those ambient component identities or the
escaping omega-centre action. The original residual subgroup and quotient
conventions are retained throughout.

Source: Aschbacher--Smith, 3.3.6--8 and 3.3.22, pp.587--588,597, with the
C.1.24(a) block construction, pp.130--131.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- The actual embedded weight-six residual has simple two-core quotient
once the original component has its simple two-core quotient. -/
theorem six_twoCore_quotient_of_seven
    (M : P.Models) (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    Nonempty ((P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) := by
  let i : P.sixGroup →* L := inclusion ((pointResidual_le L (P.six : G)).trans inf_le_left)
  exact Theory.SpecificGroups.Alternating.six_core_quotient_of_injective_seven_extension
    i (inclusion_injective _) eL
    ((centralPreimageQuotientEquiv (pCore 2 P.sixGroup)).symm.trans M.six_quotient)

/-- Actual application to the existing residual constructor. Only the A₇
simple quotient and the independent coset component theorem remain explicit. -/
theorem ambientResiduals_of_seven_quotient
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (C : P.CosetComponents) : P.AmbientResiduals := by
  obtain ⟨e6⟩ := P.six_twoCore_quotient_of_seven M eL
  exact P.ambientResiduals_of_coset_components structural eL e6 C

/-- The same quotient reduction feeds the literal Sylow-normalizer obstruction. -/
theorem no_transport_of_seven_quotient
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (C : P.CosetComponents) {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  SylowNormalizer.no_transport M (P.ambientResiduals_of_seven_quotient structural M eL C)
    S.chosen.sylow_normalizes_component hg

/-- Both source simple quotients, with no additional source callbacks.
The module-classification and centralizer-escape inputs are not needed once
these original natural coordinates and local models have been supplied. -/
theorem twoCore_quotients_of_contrary_normalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) ∧
      Nonempty ((P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨eL⟩ := E.seven_twoCore_quotient structural hescape
  exact ⟨⟨eL⟩, P.six_twoCore_quotient_of_seven M eL⟩

/-- Literal application to the source residual constructor, now discharging
both its eL and e6 premises. The independent coset-component construction
remains with the ambient-residual assembly owner. -/
theorem ambientResiduals_of_contrary_normalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (C : P.CosetComponents) : P.AmbientResiduals := by
  obtain ⟨⟨eL⟩, ⟨e6⟩⟩ := P.twoCore_quotients_of_contrary_normalizer structural M hescape
  exact P.ambientResiduals_of_coset_components structural eL e6 C

/-- The quotient construction feeds the original Sylow-normalizer obstruction
on the same marked points and the same embedded residual subgroup. -/
theorem no_transport_of_contrary_normalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (C : P.CosetComponents) {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  SylowNormalizer.no_transport M
    (P.ambientResiduals_of_contrary_normalizer structural M hescape C)
    S.chosen.sylow_normalizes_component hg

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
