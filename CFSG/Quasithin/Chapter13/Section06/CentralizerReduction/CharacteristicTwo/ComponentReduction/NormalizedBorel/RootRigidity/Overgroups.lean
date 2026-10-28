module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.LinearThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.RankOne.UnitaryExtensions
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers.Overgroups

/-!
# Uniformity in the actual signed-three relative Borel

The source identity Lᵥ = [Lᵥ,Tᵥ] eliminates field action on Lᵥ*. The whole
join K*Lᵥ* consequently acts by inner-diagonal automorphisms. The linear
calculation applies throughout that join; the unitary calculation applies
to its normalizer of Tᵥ* ∩ K*, exactly the published `borelCandidate`.
Thus uniformity holds for every nonidentity root element in the actual
relative Borel, including the nonsplit source alternatives. The proof uses
central descent, so the component is never required to be centerless.

Source: Aschbacher–Smith, A.3.16–18 and proof of 13.6.6, printed p.927.
-/

public section
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- Commutator generation passes through the literal normalizer quotient. -/
theorem root_residualStar_commutator (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s)))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcomm : ⁅residual s, localT T (markedV s)⁆ = residual s) :
    ⁅residualStar s K, NormalizerAction.sylowImage K (localT T (markedV s))⁆ =
      residualStar s K := by
  have hDP : ⁅(residual s).subgroupOf (X K),
      (localT T (markedV s)).subgroupOf (X K)⁆ = (residual s).subgroupOf (X K) := by
    apply map_injective (X K).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hDN, map_subgroupOf_eq_of_le hTN, hcomm]
  change ⁅((residual s).subgroupOf (X K)).map (NormalizerAction.quotient K),
    ((localT T (markedV s)).subgroupOf (X K)).map (NormalizerAction.quotient K)⁆ = _
  rw [← map_commutator, hDP]
  rfl

/-- The component acts by inner automorphisms after actual central descent. -/
theorem root_component_modelAction_inner {M : Type*} [Group M] {v : G}
    (K : Subgroup (Gv v)) (e : K ⧸ center K ≃* M) :
    (NormalizerAction.componentImage K).map (rankOneModelAction K e) ≤
      MulAut.innerSubgroup M := by
  change (NormalizerAction.componentImage K).map
    ((MulAut.centralQuotientAction e).comp (NormalizerAction.action K)) ≤ _
  rw [← map_map, NormalizerAction.action_map_componentImage]
  exact map_le_iff_le_comap.mpr (MulAut.inner_le_comap_centralQuotientAction e)

/-- Every element of the source relative Borel has uniform centralizers
on the PSL₃ root center. Field action is removed on the entire join K*Lᵥ*. -/
theorem linearThree_borel_root_centralizers
    {F : Type*} [Field F] [Finite F]
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : K ⧸ center K ≃* PSL(3,F))
    (hU : (Matrix.PSL3.LinearThree.unipotent F).map (linearThreeEmbedding K e) =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcomm : ⁅residual s, localT T (markedV s)⁆ = residual s)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    borelCandidate s T K ⊓ centralizer ({r} : Set (XStar K)) =
      borelCandidate s T K ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply linearThree_root_centralizers T K e hU (borelCandidate s T K) _ r hr hne
  apply (map_mono (show borelCandidate s T K ≤
    NormalizerAction.componentImage K ⊔ residualStar s K from inf_le_left)).trans
  rw [Subgroup.map_sup]
  exact sup_le ((root_component_modelAction_inner K e).trans
      (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal F))
    (residualStar_linearThree_innerDiagonal s T K e
      (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hF)
      hDN hTN hcomm)

/-- Uniformity for the full relative unitary Borel, not just its residual.
The action is faithful for every quasisimple component cover. -/
theorem unitaryThree_borel_root_centralizers [Finite G]
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : K ⧸ center K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hU : (HermitianForm.BorelTorus.projectiveRoot J hJ).map (rankOneModelEmbedding K e) =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcomm : ⁅residual s, localT T (markedV s)⁆ = residual s)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    borelCandidate s T K ⊓ centralizer ({r} : Set (XStar K)) =
      borelCandidate s T K ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  apply HermitianForm.NormalizedRootCentralizers.commutator_generated_overgroup_uniform
    J hJ hn hcard hfixed (rankOneModelAction K e) (rankOneModelAction_injective K hK e)
    _ (NormalizerAction.componentImage K) (residualStar s K)
    (NormalizerAction.sylowImage K (localT T (markedV s))) (borelCandidate s T K) _
    (root_component_modelAction_inner K e)
    (root_residualStar_commutator s T K hDN hTN hcomm) inf_le_left inf_le_right r hr hne
  rw [← hU, map_map, rankOneModelAction_embedding]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
