module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.DegreeWindows
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models

/-!
# Exhausting the genuine Theorem C sporadic list

The source list has eleven entries: five Mathieu groups, J1, J2, J4, HS, He,
and Ru. Six representation exclusions leave five central quotients. The M22
quotient still permits the simple and triple covers: no assertion here replaces
the subsequent cover and module recognition.

This conditional sieve is an assembly step, not a proof of the exclusions or
of GM02's representation catalogue. Every alternative is an actual equivalence
from the literal component quotient. Source: Aschbacher–Smith, K.4, p.457,
using the genuine Theorem C(5), p.33.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
universe u v

/-- The five surviving quotient models; recognizing their covers and modules
remains separate, in particular the two possible M22 covers. -/
def IsSurvivingCentralQuotient (L : Type u) [Group L] : Prop :=
  Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier) ∨
  Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m22.Carrier) ∨
  Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m23.Carrier) ∨
  Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier) ∨
  Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier)

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)

include ρ h

/-- Exhaust all eleven source entries, keeping each actual quotient equivalence.
The six exclusion implications are explicit remaining source obligations. -/
theorem survivingCentralQuotient_of_source_exclusions
    (hmodel : ChapterA.Section02.IsTheoremCSporadicModel
      (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hm11 : SourceExclusion.{u,v} .m11) (hj1 : SourceExclusion.{u,v} .j1)
    (hj4 : SourceExclusion.{u,v} .j4) (hhs : SourceExclusion.{u,v} .hs)
    (hhe : SourceExclusion.{u,v} .he) (hru : SourceExclusion.{u,v} .ru) :
    IsSurvivingCentralQuotient (generalizedFitting G) := by
  rcases hmodel with ⟨name, hne, he⟩ | he
  · cases name with
    | m11 => exact (hm11 ρ h he).elim
    | m12 => exact Or.inl he
    | m22 => exact Or.inr (Or.inl he)
    | m23 => exact Or.inr (Or.inr (Or.inl he))
    | m24 => exact Or.inr (Or.inr (Or.inr (Or.inl he)))
    | j2 => exact Or.inr (Or.inr (Or.inr (Or.inr he)))
    | j3 => exact (hne rfl).elim
    | j4 => exact (hj4 ρ h he).elim
    | hs => exact (hhs ρ h he).elim
    | he => exact (hhe ρ h he).elim
    | ru => exact (hru ρ h he).elim
  · exact (hj1 ρ h he).elim

/-- The actual K.4 consumer of the degree-window reductions: all four numerical
premises are discharged here, while their independent model calculations remain
explicit. The two other exclusions retain the full source hypotheses. -/
theorem survivingCentralQuotient_of_bounded_exclusions
    (hmodel : ChapterA.Section02.IsTheoremCSporadicModel
      (generalizedFitting G ⧸ center (generalizedFitting G)))
    (gmj1 : SimpleGeometry .j1 3) (gmru : SimpleGeometry .ru 6)
    (gmj4 : SimpleGeometry .j4 11)
    (hm11 : BoundedSourceExclusion.{u,v} .m11 12)
    (hj1 : BoundedSourceExclusion.{u,v} .j1 18)
    (hru : BoundedSourceExclusion.{u,v} .ru 36)
    (hj4 : BoundedSourceExclusion.{u,v} .j4 66)
    (hhs : SourceExclusion.{u,v} .hs) (hhe : SourceExclusion.{u,v} .he) :
    IsSurvivingCentralQuotient (generalizedFitting G) :=
  survivingCentralQuotient_of_source_exclusions ρ h hmodel
    (sourceExclusion_m11_of_bounded hm11) (sourceExclusion_j1_of_bounded gmj1 hj1)
    (sourceExclusion_j4_of_bounded gmj4 hj4) hhs hhe
    (sourceExclusion_ru_of_bounded gmru hru)

end CFSG.Quasithin.ChapterK.SporadicCatalogue
