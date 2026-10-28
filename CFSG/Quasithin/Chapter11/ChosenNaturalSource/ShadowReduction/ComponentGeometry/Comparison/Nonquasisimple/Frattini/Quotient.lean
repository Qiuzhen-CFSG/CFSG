module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Product
public import Theory.GroupTheory.PCoreSurjective

/-!
# The inclusion-induced residual quotient

The map is the inclusion of N_Kz(R₁)^∞ in Kz followed by the original
radical projection. The Frattini product makes it surjective. If its
kernel is a two-group, core transport identifies that kernel with the
literal two-core and gives a quotient equivalence commuting with the
original projections. Thus the PSL₂ model is attached to the required
quotient, with no choice of an unrelated abstract isomorphism.

The two-group kernel is still an explicit model-theoretic obligation.
This module does not claim to have proved that obligation or completed
11.4.2. Source: Aschbacher--Smith, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The actual inclusion followed by the original solvable-radical quotient. -/
@[expose] def residualProjection (E : Closure.Geometry D) :
    normalizerResidual E →* E.Kz ⧸ solvableRadical E.Kz :=
  (QuotientGroup.mk' (solvableRadical E.Kz)).comp (inclusion normalizerResidual_le)

/-- Representatives are unchanged by the residual projection. -/
theorem residualProjection_apply (x : normalizerResidual E) :
    residualProjection E x = QuotientGroup.mk' (solvableRadical E.Kz)
      ⟨x.val, normalizerResidual_le x.property⟩ := rfl

/-- The proved Frattini factorization makes the inclusion-induced map onto. -/
theorem residualProjection_surjective_of_split
    (hsplit : E.Kz = fittingPreimage E ⊔ normalizerResidual E) :
    Function.Surjective (residualProjection E) := by
  let F := fittingPreimage E
  let B := normalizerResidual E
  have hNF : B ≤ normalizer (F : Set G) := by
    apply normalizerResidual_le.trans
    intro k hk
    exact (twoFittingCore E.Kz).le_normalizer_map E.Kz.subtype
      ⟨⟨k, hk⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  have hFR : twoFittingCore E.Kz ≤ solvableRadical E.Kz :=
    le_solvableRadical _ inferInstance twoFittingCore_solvable
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (solvableRadical E.Kz) y
  have hk : k.val ∈ F ⊔ B := hsplit ▸ k.property
  obtain ⟨a, ha, b, hb, he⟩ := (coe_mul_of_right_le_normalizer_left F B hNF).subset hk
  obtain ⟨aK, haK, haeq⟩ := ha
  change aK.val = a at haeq
  refine ⟨⟨b, hb⟩, ?_⟩
  have hk' : aK * (⟨b, normalizerResidual_le hb⟩ : E.Kz) = k := by
    apply Subtype.ext
    change aK.val * b = k.val
    rw [haeq]
    exact he
  have ha1 : QuotientGroup.mk' (solvableRadical E.Kz) aK = 1 :=
    (QuotientGroup.eq_one_iff aK).mpr (hFR haK)
  change QuotientGroup.mk' (solvableRadical E.Kz) ⟨b, normalizerResidual_le hb⟩ = _
  rw [← hk', map_mul, ha1, one_mul]

/-- Once the remaining kernel calculation is supplied, it is exactly O₂. -/
theorem residualProjection_ker_eq_core
    (hsplit : E.Kz = fittingPreimage E ⊔ normalizerResidual E)
    (hk : IsPGroup 2 (residualProjection E).ker) :
    (residualProjection E).ker = pCore 2 (normalizerResidual E) := by
  have hq : pCore 2 (E.Kz ⧸ solvableRadical E.Kz) = ⊥ := by
    let : Group.IsNilpotent (pCore 2 (E.Kz ⧸ solvableRadical E.Kz)) := pCore_isPGroup.isNilpotent
    exact le_bot_iff.mp ((le_solvableRadical _ inferInstance inferInstance).trans_eq
      solvableRadical_quotient_solvableRadical)
  have hh := (residualProjection E).comap_pCore_of_ker_isPGroup
    (residualProjection_surjective_of_split hsplit) hk
  rw [hq] at hh
  exact hh

/-- The quotient equivalence is constructed from the literal inclusion map.
The kernel hypothesis is retained for the independent model calculation. -/
@[expose] def residualQuotientEquiv
    (hsplit : E.Kz = fittingPreimage E ⊔ normalizerResidual E)
    (hk : IsPGroup 2 (residualProjection E).ker) :
    (normalizerResidual E ⧸ pCore 2 (normalizerResidual E)) ≃*
      (E.Kz ⧸ solvableRadical E.Kz) :=
  QuotientGroup.liftEquiv (pCore 2 (normalizerResidual E))
    (residualProjection_surjective_of_split hsplit)
    (residualProjection_ker_eq_core hsplit hk).symm

/-- The quotient identification commutes with the original projections. -/
theorem residualQuotientEquiv_mk
    (hsplit : E.Kz = fittingPreimage E ⊔ normalizerResidual E)
    (hk : IsPGroup 2 (residualProjection E).ker) (x : normalizerResidual E) :
    residualQuotientEquiv hsplit hk (QuotientGroup.mk' (pCore 2 (normalizerResidual E)) x) =
      residualProjection E x :=
  QuotientGroup.liftEquiv_mk _ _ _ _

/-- Actual chosen-flag quotient application. Only the model and its kernel
calculation remain; radicality, the Sylow placement and factorization do not. -/
theorem ofFlag_residual_psl_of_fitting_model_and_kernel (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : Source.IsSL ((ofFlag S f X z H).Kz ⧸ twoFittingCore (ofFlag S f X z H).Kz) 2 p)
    (hk : IsPGroup 2 (residualProjection (ofFlag S f X z H)).ker) :
    ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
      pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p := by
  have hp3 : 3 < p := by
    have hpl := hp.1.two_le
    have h5 := hp.2.1
    omega
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := radical_model_of_fitting_sl2 hp3 hm
  have hsplit := ofFlag_fitting_factorization_of_model S f X z H h hA hseed hp hm
  exact ⟨F, inferInstance, inferInstance, hF, ⟨(residualQuotientEquiv hsplit hk).trans e⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
