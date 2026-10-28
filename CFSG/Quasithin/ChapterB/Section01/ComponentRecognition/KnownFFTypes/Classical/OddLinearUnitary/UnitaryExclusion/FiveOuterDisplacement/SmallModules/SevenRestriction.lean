module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.SmallModules.AbsoluteInputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra
public import Theory.SpecificGroups.PSU3.UniversalCover.OddPartDescent
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic

/-!
# Source assembly of the absolute order-seven restriction

The original faithful irreducible binary action gives trivial two-core in the
source component. At parameter five, the proved odd-primary kernel bounds
therefore descend the universal cover to a surjection from SU₃ of the supplied
Hermitian form. Its exact triangle with the original central quotient proves
that the surjection has central kernel, retaining the possible scalar kernel.

The lower-layer argument pulls back the given module, transports the form,
and uses the proved principal-series subquotient equivalence and spectral
calculation. The characteristic polynomial gives the integer fixed dimension
and displacement. `five_absolute_seven_restriction` discharges all these inputs;
the earlier conditional universal-cover API is preserved. The source SQTK,
generalized-Fitting, and original binary-action hypotheses remain in the target
predicate, as do both actor-order hypotheses.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

open Subgroup Theory.GroupTheory Representation BenderSuzuki.MatrixGroups
open HermitianForm.UniversalCover PerfectCentralCovering

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- Conditional source assembly. The cover premise is the specialization at
five of the existing PSU₃ universal-cover producer; the other two premises
are independent recognition and finite spectrum calculations. -/
theorem five_absolute_seven_restriction_of_principal_series_inputs
    (hcover : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
      ∃ (hS : IsQuasisimple J.specialSubgroup)
        (hP : IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)),
        letI := hS
        letI := hP
        Covering.IsUniversal.{0, 0, u}
          ({ toMonoidHom := J.specialToProjective,
             surjective := J.specialToProjective_surjective } :
            Covering J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hrecognition : SU3.FiveSmallModules.SevenRestriction.PrincipalSeriesRecognition.{0, v})
    (hspectra : SU3.FiveSmallModules.SevenRestriction.PrincipalSeriesSevenSpectra.{0, v}) :
    FiveAbsoluteSevenRestriction.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ h K _ _ _ U _ _ _ τ hf hi hd x hx _hxp
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h.quotient
  obtain ⟨hS, hP, huni⟩ := hcover F J hc hconj
  let := hS
  let := hP
  let q : Covering L (ProjectiveSpecialUnitaryMatrixGroup J) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  let f : Covering J.specialSubgroup L := huni.lift q
  exact SU3.FiveSmallModules.SevenRestriction.displacement_of_central_cover
    hrecognition hspectra J hc hconj f.toMonoidHom f.surjective f.ker_le_center
      τ hf hi hd x hx

private theorem five_exists_special_lift
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    (π : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hπ : Function.Surjective π)
    (hcore : pCore 2 L = ⊥) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      π.comp k = J.specialToProjective := by
  let := projective_isQuasisimple J (by decide : 2 < 5) hc hconj
  apply OddPartDescent.exists_lift_odd J (p := 5) (e := 1)
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [pow_one] using hc) (by simpa only [pow_one] using hconj)
    _ _ _ π hπ hcore
  · intro he
    omega
  · intro r hr hr2 hr3 hr5
    apply OddKernelBound.OddCrossCharacteristic.not_dvd_kernel_of_not_dvd_add_one
      J (p := 5) (e := 1) (by decide) (by decide) hr hr2 hr3 hr5
      (by simpa only [pow_one] using hc) (by simpa only [pow_one] using hconj)
      _ (universalCover _)
    intro hd
    have hd' : r ∣ 2 * 3 := hd
    rcases hr.dvd_mul.mp hd' with h2 | h3
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
    · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
  · intro _
    exact OddKernelBound.OddCrossCharacteristic.not_nine_dvd_kernel_of_not_nine_dvd_add_one
      J (by decide : 1 < 5) hc hconj (by decide) (by decide) (universalCover _)

/-- Every source absolute module of degree twenty or twenty-one has displacement
eighteen at the specified order-seven actor. The original binary action supplies
the two-core condition for the central-cover descent; recognition and spectra
are discharged over the original coefficient field. -/
theorem five_absolute_seven_restriction : FiveAbsoluteSevenRestriction.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ h K _ _ _ U _ _ _ τ hf hi hd x hx _hxp
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hcore : pCore 2 L = ⊥ := by
    have hk := normal_p_subgroup_le_ker (ρ.comp L.subtype) (pCore 2 L) pCore_isPGroup
    have hz : (ρ.comp L.subtype).ker = ⊥ :=
      (ρ.comp L.subtype).ker_eq_bot_iff.mpr (h.faithful.comp L.subtype_injective)
    exact bot_unique (hz ▸ hk)
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h.quotient
  let π : L →* ProjectiveSpecialUnitaryMatrixGroup J :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨k, hks, hk⟩ := five_exists_special_lift J hc hconj π hπ hcore
  have hkcenter : k.ker ≤ center J.specialSubgroup := by
    apply le_trans _ J.specialToProjective_ker_le_center
    intro y hy
    apply MonoidHom.mem_ker.mpr
    rw [← hk]
    change π (k y) = 1
    rw [MonoidHom.mem_ker.mp hy, map_one]
  exact SU3.FiveSmallModules.SevenRestriction.displacement_of_central_cover
    SU3.FiveSmallModules.SevenRestriction.principal_series_recognition
    SU3.FiveSmallModules.SevenRestriction.principal_series_seven_spectra
    J hc hconj k hks hkcenter τ hf hi hd x hx

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
