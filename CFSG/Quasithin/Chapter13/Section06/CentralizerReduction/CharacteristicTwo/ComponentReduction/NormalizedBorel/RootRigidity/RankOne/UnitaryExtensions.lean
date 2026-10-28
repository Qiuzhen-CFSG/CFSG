module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers.Actions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ResidualAction
/-!
# Unitary extension branches in the actual component action

The model embedding comes from K/Z(K) ≃ K*, and its ambient action comes
from central descent of N(K)/C(K) acting on K. These maps intertwine with
the actual inner embedding. Perfectness and simplicity are inherited from
the component. The marked residual identity removes its field part through
the genuine abelian quotient by inner-diagonal automorphisms, leaving the
proved triangular unitary root calculation.

This proves the same exclusion for every unitary component extension,
including PGU₃(q) with q ≡ -1 mod 3 and the genuine nonsplit U₃°(2ⁿ)
with odd n divisible by three. No identification with a split extension
is needed. A separate application retains PGU's original matrix inclusion.
The parent's remaining inputs are its normalized Sylow alignment and
Borel placement, together with the existing marked local arrangement.

Source: Aschbacher–Smith, A.3.16–18 and proof of 13.6.6, printed p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
variable {G M : Type*} [Group G] [Group M] {v : G} (K : Subgroup (Gv v))

/-- The faithful ambient action after descent to the model component. -/
@[expose] def rankOneModelAction (e : K ⧸ center K ≃* M) : XStar K →* MulAut M :=
  (MulAut.centralQuotientAction e).comp (NormalizerAction.action K)

/-- The component embedding through the literal quotient K/Z(K) ≃ K*. -/
@[expose] noncomputable def rankOneModelEmbedding (e : K ⧸ center K ≃* M) : M →* XStar K :=
  (NormalizerAction.componentImage K).subtype.comp
    ((NormalizerAction.componentCentralQuotientEquiv K).toMonoidHom.comp e.symm.toMonoidHom)

theorem rankOneModelAction_embedding (e : K ⧸ center K ≃* M) :
    (rankOneModelAction K e).comp (rankOneModelEmbedding K e) = MulAut.conj := by
  apply MonoidHom.ext
  intro x
  obtain ⟨q, rfl⟩ := e.surjective x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) q
  change MulAut.centralQuotientAction e (NormalizerAction.action K
    ((NormalizerAction.componentCentralQuotientEquiv K
      (e.symm (e (QuotientGroup.mk' (center K) k)))) : XStar K)) = _
  rw [e.symm_apply_apply, NormalizerAction.componentCentralQuotientEquiv_mk]
  have he : NormalizerAction.action K (NormalizerAction.quotient K
      (inclusion K.le_normalizer k)) = MulAut.conj k := by
    ext y
    rfl
  rw [he, MulAut.centralQuotientAction_conj]

theorem rankOneModelAction_injective (hK : IsComponent (Gv v) K)
    (e : K ⧸ center K ≃* M) : Function.Injective (rankOneModelAction K e) := by
  let := hK.2
  exact (MulAut.centralQuotientAction_injective e).comp (NormalizerAction.action_injective K)

variable {L V : Subgroup G}
open BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus

/-- Full-center rigidity in the residual of any extension of the unitary component.
In particular this includes the actual PGU and nonsplit A.3.16 extensions.
Simplicity and faithfulness are inherited from K; the source commutator
identity removes the field part in the full ambient action. -/
theorem unitaryThree_extension_root_centralizers [Finite G]
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : K ⧸ center K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hU : (projectiveRoot J hJ).map (rankOneModelEmbedding K e) =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcomm : ⁅residual s, localT T (markedV s)⁆ = residual s)
    (hDB : residualStar s K ≤ borelCandidate s T K)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    residualStar s K ⊓ centralizer ({r} : Set (XStar K)) =
      residualStar s K ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let D := (residual s).subgroupOf (X K)
  let P := (localT T (markedV s)).subgroupOf (X K)
  have hDP : ⁅D,P⁆ = D := by
    apply map_injective (X K).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hDN, map_subgroupOf_eq_of_le hTN, hcomm]
  have hstar : ⁅residualStar s K, NormalizerAction.sylowImage K (localT T (markedV s))⁆ =
      residualStar s K := by
    change ⁅D.map (NormalizerAction.quotient K), P.map (NormalizerAction.quotient K)⁆ = _
    rw [← map_commutator, hDP]
    rfl
  apply HermitianForm.NormalizedRootCentralizers.commutator_generated_normalizer_uniform
    J hJ hn hcard hfixed (rankOneModelAction K e) (rankOneModelAction_injective K hK e)
    (NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (residualStar s K) (NormalizerAction.sylowImage K (localT T (markedV s))) _
    (fun x hx => (hDB hx).2) hstar r hr hne
  rw [← hU, map_map, rankOneModelAction_embedding]

/-- The unitary extension branches of the marked a*/z* exclusion, including
PGU₃(q) for q ≡ -1 mod 3 and U₃°(2ⁿ) for odd n divisible by three.
The proof applies in the whole faithful automorphism action, so it requires
no replacement of the genuine nonsplit extension by a semidirect product. -/
theorem exclude_unitaryThree_extensions [Finite G]
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hTN : localT T (markedV s) ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : K ⧸ center K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hU : (projectiveRoot J hJ).map (rankOneModelEmbedding K e) =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDB : residualStar s K ≤ borelCandidate s T K) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER
    (residualStar s K) le_rfl
    (unitaryThree_extension_root_centralizers s T K hK J hJ hn hcard hfixed e hU
      hDN hTN (residual_commutator s T hk hTL S hS) hDB)

open HermitianForm.ExtensionBorel

/-- The actual projective unitary matrix Borel transports through any
compatible model embedding, including the diagonal A.3.18 alternative. -/
theorem pgu_root_centralizers (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (f : projectiveUnitary J →* XStar K) (hf : Function.Injective f)
    (hU : (pguRoot J hJ).map f =
      NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hB : B ≤ (pguBorel J).map f)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) :=
  root_centralizers_of_model T K f hf (pguRoot J hJ) (pguBorel J) hU B hB
    (HermitianForm.NormalizedRootCentralizers.pgu_uniform J hJ hn hcard hfixed) r hr hne

/-- The PGU₃ Borel calculation applied to the literal marked configuration. -/
theorem exclude_pgu [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (f : projectiveUnitary J →* XStar K) (hf : Function.Injective f)
    (hU : (pguRoot J hJ).map f =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hB : B ≤ (pguBorel J).map f) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER B hDB
    (pgu_root_centralizers T K J hJ hn hcard hfixed f hf hU B hB)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
