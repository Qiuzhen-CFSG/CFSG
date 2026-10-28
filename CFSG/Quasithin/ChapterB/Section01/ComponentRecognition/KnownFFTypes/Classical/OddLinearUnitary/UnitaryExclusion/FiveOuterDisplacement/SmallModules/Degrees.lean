module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.SmallModules.AbsoluteInputs
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.SU3.FiveSmallModules.Degrees
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration
public import Theory.SpecificGroups.PSU3.UniversalCover.PrimeFiveLift
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Source assembly for the absolute PSU₃(5) degree exclusions

The original faithful irreducible binary action makes the source component's
two-core trivial. The field-five odd-part descent then gives a surjection
from the actual SU₃(5), preserving the given PSU₃(5) quotient map. Its kernel
is central by that projection triangle. Pulling back the absolute action
preserves irreducibility; the lower-layer proof transports the Hermitian
form, constructs the induced-module quotient from a Borel eigenline, and
applies the principal-series filtration to rule out degrees 22–24.

The unconditional `five_absolute_small_degree_window` discharges both
representation inputs and the source cover lift. The separate conditional
universality-based API is retained. The 20-dimensional lower bound remains
the parent's input. The field in the source's `IsPSU` witness has universe
zero, independently of the source component and coefficient-space universes.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- Universality of the literal SU-to-PSU projection at five, including the
quasisimplicity witnesses required by the covering interface. This is the
specialization of the existing PSU₃ universal-cover producer, not a new
cover-recognition assumption about the source component. -/
def FiveUniversalSpecialCover : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∃ (hS : IsQuasisimple J.specialSubgroup)
      (hP : IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)),
      letI := hS
      letI := hP
      Covering.IsUniversal.{0, 0, u}
        ({ toMonoidHom := J.specialToProjective,
           surjective := J.specialToProjective_surjective } :
          Covering J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))

/-- Universal-cover lifting, the root eigenline calculation, and the concrete
principal-series filtrations supply exactly the source degree-window predicate.
This conditional route retains all three inputs; the source-specialized
unconditional theorem below instead uses the original binary action. -/
theorem five_absolute_small_degree_window_of_borel_inputs
    (hcover : FiveUniversalSpecialCover.{u})
    (hline : SU3.FiveSmallModules.Degrees.RootEigenlineInput.{0, v})
    (hseries : SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltrations.{0, v}) :
    FiveAbsoluteSmallDegreeWindow.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ h K _ _ _ U _ _ _ τ hf hi hlo hhi
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h.quotient
  obtain ⟨hS, hP, huni⟩ := hcover F J hc hconj
  let := hS
  let := hP
  let q : Covering L (ProjectiveSpecialUnitaryMatrixGroup J) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  let f : Covering J.specialSubgroup L := huni.lift q
  exact SU3.FiveSmallModules.Degrees.degree_window_of_central_cover
    hline hseries J hc hconj f.toMonoidHom f.surjective f.ker_le_center
      τ hf hi hlo hhi

/-- Every faithful absolutely irreducible characteristic-two representation
of a source cover of PSU₃(5) with degree 20–24 has degree 20 or 21.
The original binary action supplies the two-core hypothesis for the exact
scalar-cover lift, and both representation calculations are discharged. -/
theorem five_absolute_small_degree_window : FiveAbsoluteSmallDegreeWindow.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ h K _ _ _ U _ _ _ τ hf hi hlo hhi
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hcore : pCore 2 L = ⊥ := by
    have hk := normal_p_subgroup_le_ker (ρ.comp L.subtype) (pCore 2 L) pCore_isPGroup
    have hz : (ρ.comp L.subtype).ker = ⊥ :=
      (ρ.comp L.subtype).ker_eq_bot_iff.mpr (h.faithful.comp L.subtype_injective)
    exact bot_unique (hz ▸ hk)
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h.quotient
  let π : L →* ProjectiveSpecialUnitaryMatrixGroup J :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  obtain ⟨k, hks, hkπ⟩ := HermitianForm.UniversalCover.PrimeFiveLift.exists_lift
    J hc hconj π (e.surjective.comp (QuotientGroup.mk'_surjective _)) hcore
  have hk : k.ker ≤ center J.specialSubgroup := by
    apply le_trans _ J.specialToProjective_ker_le_center
    rw [← hkπ]
    intro x hx
    change π (k x) = 1
    rw [MonoidHom.mem_ker.mp hx, map_one]
  exact SU3.FiveSmallModules.Degrees.degree_window_of_central_cover
    SU3.FiveSmallModules.Degrees.root_eigenline_input
    SU3.FiveSmallModules.Degrees.principal_series_filtrations
    J hc hconj k hks hk τ hf hi hlo hhi

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
