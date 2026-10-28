module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Reduction
public import Theory.GroupTheory.Fitting.TwoCorePreimage

/-!
# The Cartan endpoints in the component comparison

A subgroup fixing z and normalized by X centralizes [<z>,X] = V1.
This closes the Thompson-normalizer branch, and the nonquasisimple branch
once the Frattini factorization and X-invariance of N_Kz(R1)^infinity
have been established. The latter specialization uses the literal preimage
of F(Kz/O2(Kz)), not a replacement odd core or an ambient normal subgroup.

These are conditional endpoints. The maximal-overcomponent exclusions,
the Frattini/model argument producing the factorization and invariance,
and the FF and alternating-seven arguments remain separate obligations.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The actual perfect normalizer residual used on printed p.777. -/
@[expose] def normalizerResidual (E : Closure.Geometry D) : Subgroup G :=
  Closure.residualIn (E.Kz ⊓ normalizer (E.R₁ : Set G))

/-- The normalizer residual remains a subgroup of the same point component. -/
theorem normalizerResidual_le : normalizerResidual E ≤ E.Kz :=
  (Closure.residualIn_le _).trans inf_le_left

/-- The commutator description of the line places it in the Cartan orbit span. -/
theorem line_le_cartan_span
    (hline : E.V₁ = ⁅zpowers E.z, E.X⁆) :
    E.V₁ ≤ conjugateSpanBy (zpowers E.z) E.X := by
  rw [hline]
  exact (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _))

/-- An X-invariant subgroup fixing z fixes the entire commutator line. -/
theorem centralizes_line_of_cartan_normalizes {A : Subgroup G}
    (hline : E.V₁ = ⁅zpowers E.z, E.X⁆)
    (hAz : A ≤ Gz E) (hXA : E.X ≤ normalizer (A : Set G)) :
    A ≤ centralizer (E.V₁ : Set G) := by
  have hz : zpowers E.z ≤ centralizer (A : Set G) := by
    apply zpowers_le.mpr
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hAz ha)
  have hspan : conjugateSpanBy (zpowers E.z) E.X ≤ centralizer (A : Set G) :=
    conjugateSpanBy_le hz (hXA.trans (normalizer_le_normalizer_centralizer A))
  exact le_centralizer_iff.mp ((line_le_cartan_span hline).trans hspan)

/-- The Cartan-normalization endpoint of the Thompson branch of 11.4.2. -/
theorem eq_of_cartan_normalizes_point_component (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hline : E.V₁ = ⁅zpowers E.z, E.X⁆)
    (hX : E.X ≤ normalizer (E.Kz : Set G)) : E.Kz = E.K :=
  (h.eq_iff_point_centralizes_line hf).mpr
    (centralizes_line_of_cartan_normalizes hline h.point_component.1 hX)

/-- The Cartan endpoint for a centralizing supplement and the actual N_Kz(R1) residual. -/
theorem eq_of_normalizer_residual_supplement (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hline : E.V₁ = ⁅zpowers E.z, E.X⁆)
    (A : Subgroup G) (hA : A ≤ centralizer (E.V₁ : Set G))
    (hsplit : E.Kz = A ⊔ normalizerResidual E)
    (hX : E.X ≤ normalizer (normalizerResidual E : Set G)) : E.Kz = E.K := by
  apply (h.eq_iff_point_centralizes_line hf).mpr
  rw [hsplit]
  exact sup_le hA (centralizes_line_of_cartan_normalizes hline
    ((normalizerResidual_le (E := E)).trans h.point_component.1) hX)

/-- O_{2,F}(Kz), embedded back into the original group. -/
@[expose] def fittingPreimage (E : Closure.Geometry D) : Subgroup G :=
  (Theory.GroupTheory.twoFittingCore E.Kz).map E.Kz.subtype

/-- The source nonquasisimple endpoint with the actual two-Fitting preimage.
The factorization and normalization premises still require their source proofs. -/
theorem eq_of_fitting_normalizer_split (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hline : E.V₁ = ⁅zpowers E.z, E.X⁆)
    (hF : fittingPreimage E ≤ centralizer (E.V₁ : Set G))
    (hsplit : E.Kz = fittingPreimage E ⊔ normalizerResidual E)
    (hX : E.X ≤ normalizer (normalizerResidual E : Set G)) : E.Kz = E.K :=
  eq_of_normalizer_residual_supplement h hf hline (fittingPreimage E) hF hsplit hX

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
