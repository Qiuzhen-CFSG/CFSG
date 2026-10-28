module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.Residual
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.PrimeSupport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.DualAction

/-!
# Local calculations for 15.3.49

In the extraspecial alternative of 15.3.7, put Y₀ = O²(C_Y(V)) and
Ω = Ω₁(O₂(H)). Order-three generation identifies Y₀ with θ(M ∩ H) and
θ(C_M(V)). Relative normalization puts [O₂(H),Y₀] in O₂(Y₀). Conjugation
on the actual quotient, compared with Z(Y/O₂(Y)) by the inclusion-induced
isomorphism, gives Ω₁(overline(C_T(Y₀/O₂(Y₀)))) = Z(T̄). Hence Ω ≤ S,
which puts U_H = ⟨Z_S^H⟩ in Z(Ω) and makes U_H elementary abelian.

The full ordinary conclusion, including the concrete E₉ quotient,
C_Y(Z) = C_Y(V) = O₂(Y), and the O^{3′} residual, is equivalent to the
three-prime conditions of 15.3.49(4). The compatible natural-action
normalizer calculation then proves (4) ⇒ (5).

These local results take genuine earlier conclusions explicitly: the
15.3.7 alternatives, factorization, core and image identities, the
15.3.46(5) normalizer containment, and the containment Z_S ≤ O₂(H)
from 15.3.48. The extraspecial case retains C_Y(V) ≤ H. No omega bound
or abelianness of a conjugate span is an input. The parent coset-setup
assembly supplies these earlier results and the independent faithful
action needed by `extraspecial_spans_of_omega_bound` to conclude that
V_H ≤ O₂(H) and V_H is elementary abelian. Excluding the extraspecial
alternative itself belongs to the later argument of 15.3.49.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7, printed p.1122, and 15.3.48–49, printed pp.1141–1143.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G] [Finite G]

/-- The residual and orthogonal-action calculations following 15.3.49(b),
with the actual source definitions and all quotient normalization included. -/
theorem extraspecial_local_calculation
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V)
    (hY : Y = residualY M Mc) (hV : V = localModule T M)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (h : ExtraspecialCase M Y V)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    let Q := H.pCoreIn 2
    let C := commutatorPreimage (T : Subgroup G) Y₀ (Y₀.pCoreIn 2)
    Y₀ ≠ ⊥ ∧ Y₀ = theta (M ⊓ H) ∧
      Y₀ = theta (M ⊓ centralizer (V : Set G)) ∧
      twoResidualAmbient Y₀ = Y₀ ∧
      ⁅Q, Y₀⁆ ≤ Q ⊓ Y₀ ∧ ⁅Q, Y₀⁆ ≤ Y₀.pCoreIn 2 ∧
      (T : Subgroup G) ≤ normalizer (Y₀ : Set G) ∧
      Y₀ ⊔ (T : Subgroup G) ≤ normalizer (Y₀.pCoreIn 2 : Set G) ∧
      (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      d.image (omegaOneAmbient Q) ≤ omegaOneAmbient (d.image C) ∧
      omegaOneAmbient (d.image C) =
        (center (d.image (T : Subgroup G))).map (d.image (T : Subgroup G)).subtype ∧
      ∀ i : OrthogonalPlaneIndex, omegaOneAmbient Q ≤ planeStabilizer T (d.plane i) := by
  have hYM : Y ≤ M := hY ▸ Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  obtain ⟨hne, htheta, hcentralTheta, hres, hcomm, hcommCore⟩ :=
    extraspecial_local_algebra M Mc H Y V T hYM h d.normalizes
      hTM hTH hH hCH hfactor
  obtain ⟨hn, hcoreN, hCN, hC, hOmega⟩ :=
    extraspecial_local_omega_calculation M Mc H Y V T d hY hV hMc h
      hTM hTH hH hCH hfactor hcore himage
  exact ⟨hne, htheta, hcentralTheta, hres, hcomm, hcommCore, hn, hcoreN, hCN,
    extraspecial_local_omega_image_le M Mc H Y V T d hYM h
      hTM hTH hH hCH hfactor, hC, hOmega⟩

/-- Source 15.3.49(c), and elementary abelianness of U_H, after the
containment Z_S ≤ O₂(H) supplied by 15.3.48. The omega bound is proved here. -/
theorem extraspecial_fixedPlane_span
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V) (h : ExtraspecialCase M Y V)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (i : OrthogonalPlaneIndex)
    (hAQ : fixedPlane V (planeStabilizer T (d.plane i)) ≤ H.pCoreIn 2) :
    let Ω := omegaOneAmbient (H.pCoreIn 2)
    let U := localSpan (fixedPlane V (planeStabilizer T (d.plane i))) H
    U ≤ (center Ω).map Ω.subtype ∧ IsElementaryAbelian 2 U := by
  let A := fixedPlane V (planeStabilizer T (d.plane i))
  let _ : IsElementaryAbelian 2 A := d.elementary_fixedPlane _
  have hOmega := extraspecial_local_omega_le_planeStabilizer M Mc H Y V T d h
    hTM hTH hH hCH hfactor hcore himage i
  have hcenter := span_le_center_omega A H (H.pCoreIn 2)
    (planeStabilizer T (d.plane i))
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
    hAQ inf_le_right hOmega
  let _ : IsMulCommutative (localSpan A H) := .of_setLike_mul_comm
    (fun a ha b hb => setLike_mul_comm (hcenter ha) (hcenter hb))
  exact ⟨hcenter, elementary_span_of_commutative A H⟩

/-- Source 15.3.49(3) ↔ (4) and (4) ⇒ (5), with the residual Y, local
module V, central involutions Z, and natural fixed plane Z_S specified.
The ordinary conclusion retains every source clause, not just its family. -/
theorem ordinary_prime_support_reductions
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V)
    (hY : Y = residualY M Mc) (hV : V = localModule T M)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hH : H ≤ Mc)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcases : OrdinaryCase M Y V ∨ ExtraspecialCase M Y V)
    (i : OrthogonalPlaneIndex)
    (hN : normalizer (fixedPlane V (planeStabilizer T (d.plane i)) : Set G) ≤ M) :
    let ZS := fixedPlane V (planeStabilizer T (d.plane i))
    let primeSupport :=
      Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)) ∧
      Nat.Coprime 3 (Nat.card (M ⊓ H : Subgroup G))
    (OrdinaryConclusion M Y V (centralInvolutions T) ↔ primeSupport) ∧
      d.image (M ⊓ normalizer (ZS : Set G)) = d.image (T : Subgroup G) ∧
      (primeSupport →
        normalizer (ZS : Set G) = M ⊓ normalizer (ZS : Set G) ∧
        Nat.Coprime 3 (Nat.card (normalizer (ZS : Set G)))) := by
  have hYM : Y ≤ M := hY ▸ Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hZV : centralInvolutions T ≤ V := by
    rw [hV]
    exact le_conjugateSpanBy _ _
  refine ⟨ordinary_iff_prime_support M Mc H Y V (centralInvolutions T) T
    hYM hZV hMc d.normalizes hTM hH hfactor hcases,
    NormalizerAction.image_normalizer_fixedPlane d T hTM i, ?_⟩
  rintro ⟨hc, _⟩
  subst V
  exact NormalizerAction.lemma_15_3_49_5_of_centralizer_three_prime T hTM d i hN hc

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
