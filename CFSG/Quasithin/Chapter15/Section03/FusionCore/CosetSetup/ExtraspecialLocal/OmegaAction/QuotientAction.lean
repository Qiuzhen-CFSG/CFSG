module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.QuotientAction.CenterKernel

/-!
# The actual extraspecial quotient action in 15.3.49

Starting from the genuine earlier conclusions of 15.3.7, this module
constructs the inclusion-induced isomorphism Y₀/O₂(Y₀) ≃ Z(Y/O₂(Y))
and the faithful action of the specified orthogonal Sylow image on
Y/O₂(Y). Compatibility is retained for every t in T and y in Y.
The image of C_T(Y₀/O₂(Y₀)) is exactly the center-fixing image for this
action. No faithfulness or comparison of kernels is an input.

The normalization of Y follows from Y = θ(M); normalization of Y₀
follows from the previously proved local residual calculation. Thus all
extra normalization inputs of the component constructions are discharged
here. The hypotheses are the earlier-source inputs used by the existing
local algebra API; the result applies in particular to V = localModule T M
and Y = residualY M Mc. The omega calculation is a separate consumer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7,
printed p.1122, and the calculation after 15.3.49(b), printed p.1143.
-/

public section

open Subgroup Stellmacher

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

variable {G : Type*} [Group G]

/-- The order-three generation clause makes Y invariant under M. -/
theorem ExtraspecialCase.normalizes {M Y V : Subgroup G} (h : ExtraspecialCase M Y V) :
    M ≤ normalizer (Y : Set G) := by
  rw [h.theta_eq]
  exact M.le_normalizer.trans (normalizer_le_normalizer_theta M)

/-- The actual quotient-center equivalence and faithful Sylow-image action,
with their representative formulas and the exact center-kernel comparison.
Every extra normalization premise of the component constructions is proved
from the listed earlier-source hypotheses. -/
theorem extraspecial_quotient_action [Finite G]
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V) (h : ExtraspecialCase M Y V)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    ∃ (e : (Y₀ ⧸ pCore 2 Y₀) ≃* center (Y ⧸ pCore 2 Y))
      (ρ : d.image (T : Subgroup G) →* MulAut (Y ⧸ pCore 2 Y)),
      (∀ y : Y₀, (e (QuotientGroup.mk' (pCore 2 Y₀) y) : Y ⧸ pCore 2 Y) =
        QuotientGroup.mk' (pCore 2 Y)
          ⟨y, (map_subtype_le _).trans inf_le_left y.property⟩) ∧
      Function.Injective ρ ∧
      (∀ (t : T) (y : Y),
        ρ (sylowProjection d T hTM t) (QuotientGroup.mk' (pCore 2 Y) y) =
          QuotientGroup.mk' (pCore 2 Y)
            ⟨(t : G) * (y : G) * (t : G)⁻¹,
              (h.normalizes (hTM t.property) (y : G)).mp y.property⟩) ∧
      d.image (commutatorPreimage (T : Subgroup G) Y₀ (Y₀.pCoreIn 2)) =
        centerFixingImage (d.image (T : Subgroup G)) ρ := by
  dsimp only
  let _ := h.extraspecial
  have hYM : Y ≤ M := by rw [h.theta_eq]; exact theta_le M
  have hn₀ := (extraspecial_local_normalization M Mc H Y V T hYM h
    d.normalizes hTM hTH hH hCH hfactor).1
  refine ⟨residualCenterEquiv Y V h.centralizer_eq,
    extraspecialQuotientAction d T hTM h.normalizes hYM hcore,
    residualCenterEquiv_apply_mk Y V h.centralizer_eq,
    extraspecialQuotientAction_injective d T hTM h.normalizes hYM hcore
      h.centralizer_eq himage, ?_,
    extraspecialQuotientAction_center_kernel d T hTM h.normalizes hYM hcore
      h.centralizer_eq hn₀⟩
  intro t y
  rw [extraspecialQuotientAction_projection, sylowQuotientConjugation_apply]
  rfl

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
