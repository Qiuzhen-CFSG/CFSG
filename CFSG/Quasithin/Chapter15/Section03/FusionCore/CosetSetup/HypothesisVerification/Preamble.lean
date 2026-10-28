module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.Preamble.Characteristic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.Preamble.ReducedAction

/-!
# Local preamble for the application of F.9.1 in 15.3.48

For the actual residual Y of 15.3.7, even characteristic and relative
normality give F*(Y) = O₂(Y). Sylow containment in Mc gives both F*(H) =
O₂(H) and the ambient self-centralizing-core condition used by the normal-core
argument. The compatible natural orthogonal action supplies all four clauses
of V ∈ R₂(YT) via the actual centralizer quotient. Y is two-perfect and
T-invariant.

The residual-image calculation, the intrinsic orthogonal actor's trivial
two-core, and V ≤ T remain the expressly permitted earlier-local inputs.
The equality C_T(V) = O₂(YT) is retained as an identified 15.3.7 input in its
ambient convention: the intrinsic two-core is mapped into G by `pCoreIn`.
These calculations do not assert F.9.1 or F.9.2. The remaining clauses and
final assembly of all of 15.3.48 belong to HypothesisVerification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.1,
pp.317–318; B.2.11–14, pp.77–78; 15.3.2–7, pp.1121–1122;
15.3.48, pp.1141–1142.
-/

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Preamble

variable {G : Type*} [Group G] [Finite G]

/-- Assemble the local preamble from standing even characteristic and the
explicit earlier natural-action calculations. `hCT` is precisely the earlier
15.3.7 equality, not an extra generalized-Fitting or normal-core assumption. -/
public theorem local_preamble_of_earlier_local
    (M Mc H V : Subgroup G) (T : Sylow 2 G)
    (heven : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K →
      centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hM : IsMaximalTwoLocal M) (hMc : IsMaximalTwoLocal Mc)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H) (hHMc : H ≤ Mc)
    (d : NaturalOrthogonalAction M V)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : pCore 2 OrthogonalActor = ⊥) (hVT : V ≤ T)
    (hCT : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2) :
    let := vector_normal M Mc V T hTM d
    H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2 ∧
      generalizedFitting H = pCore 2 H ∧
      generalizedFitting (residualY M Mc) = pCore 2 (residualY M Mc) ∧
      pResidual 2 (residualY M Mc) = ⊤ ∧
      (T : Subgroup G) ≤ normalizer (residualY M Mc : Set G) ∧
      V ≤ residualY M Mc ⊔ (T : Subgroup G) ∧ IsElementaryAbelian 2 V ∧
      (V.subgroupOf (residualY M Mc ⊔ (T : Subgroup G))).Normal ∧
      pCore 2 ((residualY M Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
        centralizer (V.subgroupOf (residualY M Mc ⊔ (T : Subgroup G)) :
          Set (residualY M Mc ⊔ (T : Subgroup G) : Subgroup G))) = ⊥ ∧
      (T : Subgroup G) ⊓ centralizer (V : Set G) =
        (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := vector_normal M Mc V T hTM d
  obtain ⟨hVK, hV, hn, hq⟩ := reduced_module M Mc V T hTM d himage hcore hVT
  exact ⟨H_inf_centralizer_core_le T Mc H heven hMc hTH hHMc,
    H_generalizedFitting_eq_core T Mc H heven hMc hTH hHMc,
    residualY_generalizedFitting_eq_core T M Mc heven hM hTM,
    residualY_perfect M Mc, residualY_normalized M Mc T hTM,
    hVK, hV, hn, hq, hCT⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Preamble
