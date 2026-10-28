module
public import Theory.GroupTheory.LocalSolvableCoreNormalizer
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Sylow control of the residual of a solvable-core normalizer

If a full Sylow two-subgroup T normalizes J and R is characteristic in J,
then T preserves T ∩ R and hence N_J(T ∩ R) and its perfect residual K₀.
It also normalizes O₂(K₀); Sylow maximality puts that two-core inside T.
No C-component assertion about K₀ is needed.

Source: Aschbacher--Smith, Proposition 9.3.1, printed p.732, with
R = O_{2,2′,2}(J). All intersections and residual images are literal.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.LocalSolvableCoreNormalizer
variable {G : Type*} [Group G]

/-- The original Sylow subgroup preserves the literal normalizer residual. -/
theorem sylow_normalizes_localNormalizerResidual
    (T : Sylow 2 G) (J : Subgroup G)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (R : Subgroup J) [R.Characteristic] :
    (T : Subgroup G) ≤ normalizer
      (localNormalizerResidual J ((T : Subgroup G) ⊓ R.map J.subtype) : Set G) := by
  have hTR : (T : Subgroup G) ≤ normalizer (R.map J.subtype : Set G) :=
    hTJ.trans (normalizer_le_normalizer_characteristic_image J R)
  have hTQ := (le_inf (T : Subgroup G).le_normalizer hTR).trans
    inf_normalizer_le_normalizer_inf
  exact ((le_inf hTJ (hTQ.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

/-- Sylow maximality controls the core without requiring a component structure. -/
theorem localNormalizerResidual_core_le_sylow
    (T : Sylow 2 G) (J : Subgroup G)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (R : Subgroup J) [R.Characteristic] :
    (localNormalizerResidual J ((T : Subgroup G) ⊓ R.map J.subtype)).pCoreIn 2 ≤ T := by
  let K0 := localNormalizerResidual J ((T : Subgroup G) ⊓ R.map J.subtype)
  have hTQ : (T : Subgroup G) ≤ normalizer (K0.pCoreIn 2 : Set G) :=
    (sylow_normalizes_localNormalizerResidual T J hTJ R).trans
      (normalizer_le_normalizer_characteristic_image K0 (pCore 2 K0))
  have he := T.is_maximal'
    ((isPGroup_pCoreIn 2 K0).to_sup_of_normal_left' T.isPGroup' hTQ)
    (le_sup_right : (T : Subgroup G) ≤ K0.pCoreIn 2 ⊔ (T : Subgroup G))
  exact (le_sup_left : K0.pCoreIn 2 ≤ K0.pCoreIn 2 ⊔ (T : Subgroup G)).trans he.le

end Theory.GroupTheory.LocalSolvableCoreNormalizer

