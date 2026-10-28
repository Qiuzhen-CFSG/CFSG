module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ResidualAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.Solvable
public import Theory.GroupTheory.NormalizerAction.Sylow
public import Theory.GroupTheory.SolvableSylowControl

/-!
# Intrinsic placement in the actual relative Borel

The marked A₅ action supplies solvability of LᵥTᵥ. Its literal image in
N(K)/C(K) contains the marked Sylow of K*. Intrinsic solvable Sylow
overgroup control makes that Sylow the two-core of the intersection with
K*. It is therefore invariant under Lᵥ*, placing Lᵥ* in the published
candidate N_{K*Lᵥ*}(Tᵥ* ∩ K*). This argument also applies when Lᵥ* is
not contained in K*, as in the degree-three extension alternative.

Compatible model equivalences carry this very relative normalizer to a
concrete model Borel. `ModelPlacement.Catalogue` now proves the complete
intrinsic control and inner model markings; `ModelPlacement.SmallRankOuter`
discharges the outer calculation after the central-cover rank passage.
`ModelPlacement.Assembly` combines these with the concrete signed-three
extension calculations, from explicit compatible source alternatives, and
returns the Borel and marked action data. No Sp₄ identification or
root-centralizer calculation is claimed here.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, from “Hence
Tᵥ = T_X” through the placement of Lᵥ* in B*.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- The actual image of LᵥTᵥ is solvable, using the marking's two-group
kernel and T-normalization of L. -/
theorem residualStar_sup_sylowImage_isSolvable (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s)))
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (hT : IsPGroup 2 (localT T (markedV s)))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    Group.IsSolvable (residualStar s K ⊔ NormalizerAction.sylowImage K
      (localT T (markedV s)) : Subgroup (XStar K)) := by
  let A := residual s ⊔ localT T (markedV s)
  have hAN : A ≤ X K := sup_le hDN hTN
  let : Group.IsSolvable A := residual_sup_localT_isSolvable s T hk hTL hT
  let : Group.IsSolvable (A.subgroupOf (X K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hAN).toMonoidHom) (subgroupOfEquivOfLe hAN).injective
  have he : A.subgroupOf (X K) =
      (residual s).subgroupOf (X K) ⊔ (localT T (markedV s)).subgroupOf (X K) := by
    apply map_injective (X K).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAN,
      map_subgroupOf_eq_of_le hDN, map_subgroupOf_eq_of_le hTN]
  have hs := Group.isSolvable_of_surjective
    ((NormalizerAction.quotient K).subgroupMap_surjective (A.subgroupOf (X K)))
  rw [he, Subgroup.map_sup] at hs
  exact hs

/-- The marked Sylow intersection is the characteristic two-core of the
solvable intersection. This supplies actual normalization for placement. -/
theorem sylow_intersection_eq_twoCore (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s)))
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    ((residualStar s K ⊔ NormalizerAction.sylowImage K (localT T (markedV s))) ⊓
      NormalizerAction.componentImage K).pCoreIn 2 =
        NormalizerAction.sylowImage K (localT T (markedV s)) ⊓
          NormalizerAction.componentImage K := by
  let A := residualStar s K ⊔ NormalizerAction.sylowImage K (localT T (markedV s))
  let : Group.IsSolvable A := residualStar_sup_sylowImage_isSolvable s T K hk hTL
    (hS ▸ S.isPGroup') hDN hTN
  obtain ⟨P, hP⟩ := NormalizerAction.exists_component_sylow K S (hS ▸ hTN)
  rw [hS] at hP
  rw [← hP]
  exact hcontrol.core_intersection (NormalizerAction.componentImage K) A P
    (hP.le.trans (inf_le_left.trans le_sup_right))

/-- Intrinsic control in K* places the actual residual in the literal
relative Borel. This includes the non-inner extension case. -/
theorem residualStar_le_borelCandidate (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s)))
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    residualStar s K ≤ borelCandidate s T K := by
  let A := residualStar s K ⊔ NormalizerAction.sylowImage K (localT T (markedV s))
  let : Group.IsSolvable A := residualStar_sup_sylowImage_isSolvable s T K hk hTL
    (hS ▸ S.isPGroup') hDN hTN
  obtain ⟨P, hP⟩ := NormalizerAction.exists_component_sylow K S (hS ▸ hTN)
  rw [hS] at hP
  have hnorm := hcontrol.normalizes_sylow (NormalizerAction.componentImage K) A P
    le_normalizer_of_normal (hP.le.trans (inf_le_left.trans le_sup_right))
  rw [hP] at hnorm
  exact le_inf le_sup_right ((show residualStar s K ≤ A from le_sup_left).trans hnorm)

/-- A concrete component equivalence transports intrinsic model control
to the actual action image, including images of exceptional covers. -/
theorem residualStar_le_borelCandidate_of_model (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {M : Type*} [Group M]
    (e : NormalizerAction.componentImage K ≃* M)
    (hcontrol : SolvableSylowControl 2 M)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    residualStar s K ≤ borelCandidate s T K :=
  residualStar_le_borelCandidate s T K hk hTL S hS hDN hTN
    (hcontrol.of_equiv e)

omit [Finite G] in
/-- When the residual action is inner, the candidate is exactly the
Sylow normalizer inside K*, with the same marked Sylow intersection. -/
theorem borelCandidate_eq_of_residualStar_le (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hD : residualStar s K ≤ NormalizerAction.componentImage K) :
    borelCandidate s T K = NormalizerAction.componentImage K ⊓
      normalizer ((NormalizerAction.sylowImage K (localT T (markedV s)) ⊓
        NormalizerAction.componentImage K : Subgroup (XStar K)) : Set (XStar K)) := by
  unfold borelCandidate
  rw [sup_eq_left.mpr hD]

omit [Finite G] in
/-- An equivalence on the genuine overgroup and a compatible root marking
identify the published candidate with the concrete model Borel. The map
is on K*Lᵥ*, so it retains all extension embeddings. -/
theorem borelCandidate_model_map (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {M : Type*} [Group M]
    (e : (NormalizerAction.componentImage K ⊔ residualStar s K : Subgroup (XStar K)) ≃* M)
    (U B : Subgroup M)
    (hU : ((NormalizerAction.sylowImage K (localT T (markedV s)) ⊓
      NormalizerAction.componentImage K).subgroupOf
        (NormalizerAction.componentImage K ⊔ residualStar s K)).map e.toMonoidHom = U)
    (hB : normalizer (U : Set M) = B) :
    ((borelCandidate s T K).subgroupOf
      (NormalizerAction.componentImage K ⊔ residualStar s K)).map e.toMonoidHom = B :=
  SolvableSylowControl.relative_normalizer_map _ _
    (inf_le_right.trans le_sup_left) e U B hU hB

/-- The consumer receives both the actual placement and its concrete
model image, in the very same marking of K*Lᵥ*. -/
theorem residualStar_model_borel_data (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {M : Type*} [Group M]
    (e : (NormalizerAction.componentImage K ⊔ residualStar s K : Subgroup (XStar K)) ≃* M)
    (U B : Subgroup M)
    (hU : ((NormalizerAction.sylowImage K (localT T (markedV s)) ⊓
      NormalizerAction.componentImage K).subgroupOf
        (NormalizerAction.componentImage K ⊔ residualStar s K)).map e.toMonoidHom = U)
    (hB : normalizer (U : Set M) = B)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    residualStar s K ≤ borelCandidate s T K ∧
      ((borelCandidate s T K).subgroupOf
        (NormalizerAction.componentImage K ⊔ residualStar s K)).map e.toMonoidHom = B ∧
      ((residualStar s K).subgroupOf
        (NormalizerAction.componentImage K ⊔ residualStar s K)).map e.toMonoidHom ≤ B := by
  have hDB := residualStar_le_borelCandidate s T K hk hTL S hS hDN hTN hcontrol
  have he := borelCandidate_model_map s T K e U B hU hB
  exact ⟨hDB, he, he ▸ map_mono (subgroupOf_mono _ hDB)⟩

/-- Case (ii): the odd-rank bound first passes through the actual central
cover, then the intrinsic model outer calculation feeds perfect descent
and the already proved residual commutator identity. -/
theorem residualStar_le_of_small_three_rank (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (hr : primeRank 3 K ≤ 1)
    (houter : primeRank 3 (NormalizerAction.componentImage K) ≤ 1 →
      IsMulCommutative (MulAut.Outer (NormalizerAction.componentImage K)))
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    residualStar s K ≤ NormalizerAction.componentImage K := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let := houter (NormalizerAction.componentImage_rank_le_one K (by decide) hr)
  exact residualStar_le_of_abelian_outer_component s T K hK hk hTL S hS hDN hTN

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
