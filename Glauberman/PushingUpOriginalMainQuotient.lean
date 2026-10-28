module
public import Glauberman.PushingUpMainQuotient
public import Glauberman.PushingUpOmegaFixedIndex

/-!
# The original Niles central-chief reduction

The proved action-recognition theorem supplies the natural omega quotient
required by the source 7.2 construction. Thus the original finite group admits
a central-chief kernel whose quotient satisfies every Main Hypothesis input.
The kernel lies in the actual two-core, and the original PSL2(4) quotient and
Sylow image are retained literally. No independent coordinate, fixed-index or
orbit-formula assumption remains.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 7.2, pp.60–62.
-/

public section
open Subgroup NilesRankOneKernel Theory.GroupTheory
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- Source7.6 under the original hypotheses, with source2.9 discharged. -/
theorem original_psl2_four_kernel_orbit
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (α : MulAut S)
    (hVN : (omegaCenterIn (pCore 2 H)).subgroupOf (S : Subgroup H) ≤
      invariantNormalKernel (S : Subgroup H) α) :
    invariantNormalKernel (S : Subgroup H) α =
      ⨅ n : ℤ, ((pCore 2 H).subgroupOf (S : Subgroup H)).map ((α ^ n).toMonoidHom) := by
  obtain ⟨hlower,hsupp⟩ := original_psl2_four_omega_fixedIndex_data hF S hu K e hf hno
  apply pushingUp_kernel_orbit_of_natural_bounds hF S hu K e hno _ _ α hVN
  · intro A hA hAQ
    exact hlower A hA.1 hAQ
  · intro L hL
    obtain ⟨hi,hc⟩ := hsupp L hL
    rw [inf_relIndex_left] at hi
    exact ⟨hi.ge,hc⟩

/-- Source7.2 under only the original finite-group hypotheses. The actual
kernel lies in the original two-core and has only central ambient chief factors. -/
theorem original_psl2_four_exists_main_quotient
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) :
    ∃ α : MulAut S,
      let N := (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype
      let π := QuotientGroup.mk' N
      ∃ s : NoncentralChiefRefinement.SeriesOn N, (∀ i, s.Central i) ∧
        N ≤ pCore 2 H ∧ N ≤ K ∧
        Nonempty (((H ⧸ N) ⧸ K.map π) ≃* (H ⧸ K)) ∧
        generalizedFitting (H ⧸ N) = pCore 2 (H ⧸ N) ∧
        Order.HasUniqueMaximalOver ((S : Subgroup H).map π) ⊤ ∧
        ∃ β : MulAut ((S : Subgroup H).map π),
          NoInvariantNormal ((S : Subgroup H).map π) β := by
  obtain ⟨q,hq,hk,_,_,_,E,hE⟩ :=
    original_psl2_four_omegaAction_recognition hF S hu K e hf hno
  obtain ⟨α,s,hc,hNK,he,hf',hu',β,hβ⟩ :=
    exists_main_quotient_of_original_natural_action hF S hu K e hf hno q hq hk E hE
  refine ⟨α,s,hc,?_,hNK,he,hf',hu',β,hβ⟩
  have hNS := map_subtype_le (invariantNormalKernel (S : Subgroup H) α)
  exact le_sSup ⟨inferInstance,S.isPGroup'.of_injective
    (inclusion hNS) (inclusion_injective hNS)⟩

end Glauberman
