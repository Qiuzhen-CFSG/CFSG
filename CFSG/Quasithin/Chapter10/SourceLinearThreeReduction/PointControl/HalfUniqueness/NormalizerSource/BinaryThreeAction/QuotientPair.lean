module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.QuotientAction

/-!
# The irreducible pair on the literal enlargement quotient

A parabolic residual supplies its original odd complement through the Xi
local input. In a strict quasisimple normal closure, the component-detection
theorem gives the full commutator identity. The actual Sylow intersection
and complement therefore descend to an irreducible pair in K/O₂(K).
The two-residual of that pair is exactly the image of the original O²(H),
since adjoining the Sylow absorbs the complement's two-core.

This supplies the pair and irreducibility hypotheses for the remaining model
normalizer calculations in Aschbacher--Smith 10.2.5, printed pp.747--748.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding InvariantThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}

theorem Data.exists_localInput (h : Data D H) :
    ∃ P : Subgroup G, LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) := by
  let P : Sylow 3 (residual H) := Classical.arbitrary _
  have hTE : (T : Subgroup G) ≤ enlargement T L H := h.sylow_le.trans le_sup_right
  have hXT : residual H ⊔ (T : Subgroup G) ≤ enlargement T L H := by
    rw [h.residual_sup_sylow]
    exact le_sup_right
  exact ⟨_,localInput_of_mem_Xi h.xi.1
    (SourceLinearThreeReplacement.Overgroups.Closure.sylowIn_overgroup hTE)
    hXT (by decide : Odd 3) h.xi.2 P⟩

theorem Data.quotient_complement_join (h : Data D H) {P : Subgroup G}
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H)) :
    quotientImage (enlargedResidual T L H) P ⊔
      quotientImage (enlargedResidual T L H) (T : Subgroup G) =
    quotientImage (enlargedResidual T L H) (residual H) ⊔
      quotientImage (enlargedResidual T L H) (T : Subgroup G) := by
  let K := enlargedResidual T L H
  have hPX : P ≤ residual H := le_sup_right.trans hi.complement.le
  have hcT : (residual H).pCoreIn 2 ≤ (T : Subgroup G) :=
    le_sup_left.trans hi.normalizer_factor.symm.le
  have he : P ⊔ ((T : Subgroup G) ⊓ K) = residual H ⊔ ((T : Subgroup G) ⊓ K) := by
    apply le_antisymm (sup_le_sup_right hPX _)
    apply sup_le _ le_sup_right
    rw [← hi.complement]
    exact sup_le ((le_inf hcT ((pCoreIn_le 2 _).trans h.residual_le_enlargedResidual)).trans
      le_sup_right) le_sup_left
  have hs := congrArg (fun A : Subgroup G => A.subgroupOf K) he
  rw [subgroupOf_sup (hPX.trans h.residual_le_enlargedResidual) inf_le_right,
    subgroupOf_sup h.residual_le_enlargedResidual inf_le_right] at hs
  have hTi : ((T : Subgroup G) ⊓ K).subgroupOf K = (T : Subgroup G).subgroupOf K := by
    ext x
    exact and_iff_left x.property
  rw [hTi] at hs
  simpa only [quotientImage,Subgroup.map_sup] using
    congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) hs

/-- In a strict quasisimple enlargement the original complement and its full
Sylow image form the irreducible pair needed by the model calculation. -/
theorem Data.exists_quotient_pair (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hq : IsQuasisimple (XiQuotient (enlargedResidual T L H)))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) :
    ∃ (S : Sylow 2 (XiQuotient (enlargedResidual T L H)))
      (P : Subgroup (XiQuotient (enlargedResidual T L H))),
      (S : Subgroup (XiQuotient (enlargedResidual T L H))) = quotientImage (enlargedResidual T L H) (T : Subgroup G) ∧
      PairInput S P ∧ ¬ PairReducible (S : Subgroup (XiQuotient (enlargedResidual T L H))) P ∧
      (pResidual 2 (P ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H))) : Subgroup (XiQuotient (enlargedResidual T L H)))).map
        (P ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H)))).subtype =
          quotientImage (enlargedResidual T L H) (residual H) := by
  obtain ⟨P,hi⟩ := h.exists_localInput
  have hE := Chapter1.RadicalExclusions.sqtk_of_mem_H D.simpleQTKE (h.enlargement_mem_H hn)
  have hT := SourceLinearThreeReplacement.Overgroups.Closure.sylowIn_overgroup
    (h.sylow_le.trans (show H ≤ enlargement T L H from le_sup_right))
  obtain he | ⟨I,_,_,_,hc,_,he,_⟩ :=
    SourceLinearThreeReplacement.Overgroups.Closure.adequate_three_normalClosure hi hE hT
  · exact (h.residual_lt_enlargedResidual hN).ne' he |>.elim
  have hPK : P ≤ enlargedResidual T L H :=
    (le_sup_right.trans hi.complement.le).trans h.residual_le_enlargedResidual
  have hcomm : ⁅enlargedResidual T L H,P⁆ = enlargedResidual T L H := by
    change ⁅conjugateSpanBy (residual H) (enlargement T L H),P⁆ = _
    rw [he,hc]
    exact he.symm
  obtain ⟨S,hS,hpair⟩ := pairInput_of_sylow hi hE hT h.enlargedResidual_le_enlargement
    h.enlargedResidual_normal hq hPK hcomm
  refine ⟨S,quotientImage (enlargedResidual T L H) P,hS,hpair,?_,?_⟩
  · rw [hS]
    exact not_pairReducible hi hPK h.sylow_normalizes_enlargedResidual
  · rw [hS,h.quotient_complement_join hi]
    exact h.quotient_parabolic_residual

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
