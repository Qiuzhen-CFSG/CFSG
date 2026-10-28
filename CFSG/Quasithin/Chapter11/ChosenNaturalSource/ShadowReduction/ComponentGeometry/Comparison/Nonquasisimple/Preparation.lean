module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.CartanEndpoints
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Fitting
public import Theory.GroupTheory.SylowCoreRestriction

/-!
# The actual omega-center in the nonquasisimple comparison

The common Sylow subgroup reverses two-core containment from KzT to L1T.
Condition (E) at the original point centralizer then makes KzT have
self-centralizing two-core. Thus the earlier line-centralization by R1
puts V1 in VK = Omega1 Z(O2(KzT)).

The relative A.4.11 theorem transfers radical centralization on R2(KzT)
to centralization of VK by the literal Fitting preimage. This excludes the
first source alternative Kz = O2,F(Kz)L1. The shared radical theorem and
the Frattini/component argument for the other alternative remain separate.
Source: Aschbacher--Smith, 11.4.2, printed pp.776--777.
-/

open Subgroup Theory.GroupTheory Stellmacher
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The source VK, embedded in the original ambient group. -/
@[expose] def pointOmega (E : Closure.Geometry D) : Subgroup G :=
  omegaOneCenterAmbient ((E.Kz ⊔ (T : Subgroup G)).pCoreIn 2)

/-- A.1.6 on the original common Sylow join. -/
theorem pointJoin_core_le_firstRadical :
    (E.Kz ⊔ (T : Subgroup G)).pCoreIn 2 ≤ E.R₁ :=
  pCoreIn_le_of_sylow_le T le_sup_right
    (sup_le_sup_right (le_conjugateSpanBy _ _) _)

/-- The actual KzT inherits characteristic two from the point two-local. -/
theorem pointJoin_mem_He (h : EarlierGeometry E) :
    E.Kz ⊔ (T : Subgroup G) ∈ Chapter1.He G := by
  have hJC : E.Kz ⊔ (T : Subgroup G) ≤ Gz E :=
    sup_le h.point_component.1 h.sylow_le_pointCentralizer
  have hc := Chapter1.twoLocal_mem_He_of_sylow_le T
    (E.input.source.simpleQTKE.evenCharacteristic T)
    (point_twoLocal E h.point_mem h.point_fixed h.point_ne_one) h.sylow_le_pointCentralizer
  have hcore := pCoreIn_le_of_sylow_le T le_sup_right hJC
  intro x hx
  exact hcore (hc ⟨hJC hx.1, (centralizer_le hcore) hx.2⟩)

/-- Earlier R1-centralization puts the original line in VK. -/
theorem line_le_pointOmega (h : EarlierGeometry E)
    (hR : E.R₁ ≤ centralizer (E.V₁ : Set G)) : E.V₁ ≤ pointOmega E := by
  let := D.elementary
  have hfix : E.V₁ ≤ centralizer ((E.Kz ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (le_centralizer_iff.mp hR).trans (centralizer_le pointJoin_core_le_firstRadical)
  intro v hv
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  exact ⟨pointJoin_mem_He h ⟨mem_sup_right (D.le_sylow (E.V₁_le hv)),hfix hv⟩,
    elemPow_eq_one_of_isElementaryAbelian v (E.V₁_le hv),hfix hv⟩

/-- Strict comparison forces movement of this same VK. -/
theorem pointOmega_moved (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hR : E.R₁ ≤ centralizer (E.V₁ : Set G)) :
    ¬ E.Kz ≤ centralizer (pointOmega E : Set G) := by
  intro hc
  exact hne ((h.eq_iff_point_centralizes_line hf).mpr
    (hc.trans (centralizer_le (line_le_pointOmega h hR))))


/-- A.4.11 applied through the literal Kz ≤ KzT inclusion. -/
theorem fittingPreimage_centralizes_pointOmega (h : EarlierGeometry E)
    (hrad : (solvableRadical E.Kz).map E.Kz.subtype ≤
      centralizer ((reducedTwoSubgroup (E.Kz ⊔ (T : Subgroup G) : Subgroup G)).map
        (E.Kz ⊔ (T : Subgroup G)).subtype : Set G)) :
    fittingPreimage E ≤ centralizer (pointOmega E : Set G) :=
  ChapterA.Section04.embedded_twoFittingCore_centralizes_omegaCenter_of_radical_reduced
    E.Kz (E.Kz ⊔ (T : Subgroup G)) le_sup_left h.point_mem_local_family.1.subnormal hrad

/-- Radical centralization supplies the Fitting-centralization premise
of the existing Cartan endpoint. -/
theorem fittingPreimage_centralizes_line (h : EarlierGeometry E)
    (hR : E.R₁ ≤ centralizer (E.V₁ : Set G))
    (hrad : (solvableRadical E.Kz).map E.Kz.subtype ≤
      centralizer ((reducedTwoSubgroup (E.Kz ⊔ (T : Subgroup G) : Subgroup G)).map
        (E.Kz ⊔ (T : Subgroup G)).subtype : Set G)) :
    fittingPreimage E ≤ centralizer (E.V₁ : Set G) :=
  (fittingPreimage_centralizes_pointOmega h hrad).trans
    (centralizer_le (line_le_pointOmega h hR))

/-- The first nonquasisimple alternative on p.777 is impossible. -/
theorem not_fitting_seed_split (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hR : E.R₁ ≤ centralizer (E.V₁ : Set G))
    (hrad : (solvableRadical E.Kz).map E.Kz.subtype ≤
      centralizer ((reducedTwoSubgroup (E.Kz ⊔ (T : Subgroup G) : Subgroup G)).map
        (E.Kz ⊔ (T : Subgroup G)).subtype : Set G)) :
    E.Kz ≠ fittingPreimage E ⊔ E.L₁ := by
  intro he
  apply hne
  apply (h.eq_iff_point_centralizes_line hf).mpr
  rw [he]
  exact sup_le (fittingPreimage_centralizes_line h hR hrad) h.seed_centralizes

/-- In the remaining Frattini alternative the literal residual moves V1.
Its factorization is still supplied by the separate source argument. -/
theorem normalizerResidual_moves_line_of_split (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hR : E.R₁ ≤ centralizer (E.V₁ : Set G))
    (hrad : (solvableRadical E.Kz).map E.Kz.subtype ≤
      centralizer ((reducedTwoSubgroup (E.Kz ⊔ (T : Subgroup G) : Subgroup G)).map
        (E.Kz ⊔ (T : Subgroup G)).subtype : Set G))
    (hsplit : E.Kz = fittingPreimage E ⊔ normalizerResidual E) :
    ¬ normalizerResidual E ≤ centralizer (E.V₁ : Set G) := by
  intro hc
  apply hne
  apply (h.eq_iff_point_centralizes_line hf).mpr
  rw [hsplit]
  exact sup_le (fittingPreimage_centralizes_line h hR hrad) hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
