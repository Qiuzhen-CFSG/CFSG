module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane

/-!
# Strict span from local Fitting faithfulness

The commutator identity needed in (m) concerns the selected local H, rather
than only the involution centralizer M_c. Apply the proved local Fitting
theorem to Z_S at H, using empty L_f, characteristic two, and 15.3.48. Then
the actual orthogonal fixed-plane theorem derives the strict span. Neither
noncentrality of the two-core on Z_S nor nonsingularity of the plane is
assumed in this assembly.

The explicit inputs are the actual two orthogonal-action interfaces,
the standing local hypotheses, 15.3.46(2), the intrinsic versions of
15.3.48(2),(3), and elementary abelianness from 15.3.49(d).
Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(a),(2),(m), printed pp.1142 and 1144.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G] [Finite G]

/-- The source's strict span, with the local commutator premise discharged
at this H using Fitting faithfulness. Every quotient and residual is literal. -/
theorem strict_span_of_earlier
    (T : Sylow 2 G) (M H ZS : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H) (hout : ¬ H ≤ M)
    (d : Section03.NaturalOrthogonalAction M (localModule T M))
    [IsElementaryAbelian 2 (localModule T M)]
    (o : FusionCore.NaturalOrthogonalAction M (localModule T M))
    (i : OrthogonalPlaneIndex)
    (hseed : ZS = fixedPlane (localModule T M) (planeStabilizer T (d.plane i)))
    [IsElementaryAbelian 2 (localSpan (localModule T M) H)]
    (hZA : centralInvolutions T ≤ ZS)
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G))
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hUQ : localSpan (ZS.subgroupOf H) ⊤ ≤ pCore 2 H)
    (hPhi : (frattini (localSpan (ZS.subgroupOf H) ⊤)).map
      (localSpan (ZS.subgroupOf H) ⊤).subtype ≤ (centralInvolutions T).subgroupOf H)
    (hsmall : ∀ h : H,
      (∀ u ∈ localSpan (ZS.subgroupOf H) ⊤,
        ⁅u,h⁆ ∈ (centralInvolutions T).subgroupOf H) ↔ h ∈ pCore 2 H)
    (h48 : ⁅localSpan ZS H, localTwoCore H⁆ ≤ centralInvolutions T)
    (hnormalizer : ∀ W : Subgroup G, W ≤ localModule T M →
      ¬ IsTotallySingular o.form W → normalizer (W : Set G) ≤ M) :
    localSpan ZS H ⊔ localModule T M < localSpan (localModule T M) H := by
  have hAV : ZS ≤ localModule T M := by rw [hseed]; exact inf_le_left
  have hAH : ZS ≤ H := hAV.trans
    ((d.le_sylow T hTM (Section03.localModule_le T hTM)).trans hTH)
  have h49 := (CosetSetup.FittingFaithfulness.local_conclusions T M H ZS
    hTH hTM hout hAH hZA hZcard hHZ hc hempty hUQ hPhi hsmall).2.2.1
  rw [hseed] at h48 h49 ⊢
  exact Geometry.FixedPlane.localSpan_fixedPlane_sup_lt T M H hTM hTH hout
    d o i hZcard h48 h49 hnormalizer

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
