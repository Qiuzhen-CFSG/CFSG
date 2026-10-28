module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CorePreimage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreOrder

/-!
# The normalizer quotient and centralizer incidence in the HS double cover

The specified map to HS induces the actual conjugation action on its
characteristic elementary eight. Its kernel is Q, so M/Q is explicitly
SL₃(2), with a formula on representatives. The model core order gives
|Q| = 128. The central kernel lies in Q, and Q maps onto the model core.

We also name the embedded Z(O₂(O²(C_K(u)))) and prove that the source
incidence and normal-generation equalities imply that Q is abelian.
Constructing those incidences remains a separate obligation; this module
does not assert the nonsplit four-dimensional module conclusion.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Sporadic.LeechRelated.HS.BlockNormalizer

variable {K : Type*} [Group K]

/-- Conjugation on the concrete elementary eight, pulled back along localMap. -/
def normalizerAction (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    M e →* MulAut baseElementary :=
  baseElementary.normalizerMonoidHom.comp (localMap e)

theorem normalizerAction_surjective
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Function.Surjective (normalizerAction e) :=
  baseNormalizer_action_surjective.comp (localMap_surjective e)

theorem normalizerAction_ker [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    (normalizerAction e).ker = Q e := by
  rw [Q_eq_model_core_preimage e hZ, model_core_eq_action_ker]
  rfl

/-- The quotient equivalence comes from the specified action and quotient map. -/
noncomputable def normalizerQuotientEquiv [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    (M e ⧸ Q e) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerAction_ker e hZ).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (normalizerAction e)
      (normalizerAction_surjective e)).trans baseAutomorphismEquiv)

theorem normalizerQuotientEquiv_mk [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (m : M e) :
    normalizerQuotientEquiv e hZ (QuotientGroup.mk' (Q e) m) =
      baseAutomorphismEquiv (normalizerAction e m) := rfl

theorem Q_card_eq_128 [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) : Nat.card (Q e) = 128 := by
  rw [Q_card e hZ, model_core_card]

theorem center_le_Q [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    (center K).subgroupOf (M e) ≤ Q e := by
  rw [Q_eq_model_core_preimage e hZ, ← localMap_ker e]
  exact MonoidHom.ker_le_comap _ _

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Sporadic.LeechRelated.HS.BlockNormalizer
open Theory.GroupTheory
variable {K : Type*} [Group K]

/-- The center of the centralizer core, embedded in the original cover K. -/
def coreCenter (u : K) : Subgroup K :=
  (center (centralizerCore u)).map (centralizerCore u).subtype

/-- The actual core maps onto the normalizer's model core. -/
theorem Q_map_localMap [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    (Q e).map (localMap e) = pCore 2 baseNormalizer := by
  rw [Q_eq_model_core_preimage e hZ, map_comap_eq_self]
  rw [(localMap e).range_eq_top_of_surjective (localMap_surjective e)]
  exact le_top

/-- Images of Q centralize the concrete elementary eight pointwise. -/
theorem Q_modelMap_centralizes [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (q : Q e) (a : baseElementary) :
    modelMap e (q : K) * (a : Sporadic.LeechRelated.HS.Carrier) =
      (a : Sporadic.LeechRelated.HS.Carrier) * modelMap e (q : K) := by
  have hq : normalizerAction e (q : M e) = 1 := by
    change (q : M e) ∈ (normalizerAction e).ker
    rw [normalizerAction_ker e hZ]
    exact q.property
  have ha := congrArg (fun f : MulAut baseElementary => f a) hq
  have he : modelMap e (q : K) * (a : Sporadic.LeechRelated.HS.Carrier) *
      (modelMap e (q : K))⁻¹ = a := congrArg Subtype.val ha
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The source incidence and normal generation force Q to be abelian.
The hypotheses retain the literal residual and embedded center; their
normalizer-specific construction is a separate obligation. -/
theorem Q_isMulCommutative_of_incidence
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K)
    (hQX : (Q e).map (M e).subtype ≤ centralizerTwoResidual u)
    (hXV : centralizerTwoResidual u ≤ centralizer (coreCenter u : Set K))
    (hgen : normalClosure (((coreCenter u).subgroupOf (M e)) : Set (M e)) = Q e) :
    IsMulCommutative (Q e) := by
  have hc : Q e ≤ centralizer ((coreCenter u).subgroupOf (M e) : Set (M e)) := by
    intro q hq v hv
    apply Subtype.ext
    exact hXV (hQX (mem_map_of_mem _ hq)) v hv
  apply le_centralizer_iff_isMulCommutative.mp
  rw [← hgen] at hc ⊢
  exact normalClosure_le_normal (le_centralizer_iff.mp hc)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
