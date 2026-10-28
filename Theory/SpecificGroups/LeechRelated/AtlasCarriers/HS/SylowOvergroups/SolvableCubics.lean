module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.PrimeActors
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Action
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import Theory.GroupTheory.SolvableSylowOvergroups.CubicSections
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Solvable Higman–Sims Sylow overgroups containing a cubic

The native full-Sylow cover puts a proper overgroup in the central-involution
or elementary-eight normalizer. Their actual surjective actions have targets
S₅ and GL₃(2), with two-group kernels. A solvable image containing the full
Sylow and a cubic has order 24; hence every odd subgroup has order dividing
three. The Chapter6 consumer applies this to the original Cartan and right
Hall images and excludes the HS containing row.
Source: Aschbacher--Smith A.3.12(18) and 5.1.13, printed pp.47--48,637.
Imported ATLAS HSG1-p100B0 certificates retain their attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open EvenLocalCandidates BlockNormalizer

/-- Every odd subgroup has order dividing three in this original full-Sylow configuration. -/
theorem odd_card_dvd_three_of_cubic
    (S : Sylow 2 Carrier) (J E : Subgroup Carrier)
    (hSJ : (S : Subgroup Carrier) ≤ J) (hJ : J ≠ ⊤)
    (hs : Group.IsSolvable J) (h3 : 3 ∣ Nat.card J)
    (hEJ : E ≤ J) (ho : Odd (Nat.card E)) : Nat.card E ∣ 3 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S baseSylow
  let c := MulAut.conj g
  have hS : (S : Subgroup Carrier).map c.toMonoidHom = subgroup :=
    congrArg Sylow.toSubgroup hg
  let U := J.map c.toMonoidHom
  let D := E.map c.toMonoidHom
  have hU : Nat.card U = Nat.card J := card_map_of_injective c.injective
  have hD : Nat.card D = Nat.card E := card_map_of_injective c.injective
  have hSU : subgroup ≤ U := hS ▸ map_mono hSJ
  have hUt : U ≠ ⊤ := by
    intro he
    apply hJ
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [map_top_of_surjective _ c.surjective]
    exact he
  let := hs
  let : Group.IsSolvable U := Group.isSolvable_of_surjective (c.toMonoidHom.subgroupMap_surjective J)
  have hDU : D ≤ U := map_mono hEJ
  have branch (i : Fin 3) (hUi : U ≤ localGroup i)
      {Q : Type} [Group Q] [Finite Q] (f : localGroup i →* Q)
      (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
      (hc : Nat.card Q = 120 ∨ Nat.card Q = 168) (hn : ¬ Group.IsSolvable Q) :
      Nat.card E ∣ 3 := by
    let P := baseSylow.subtype (hSU.trans hUi)
    let V := U.subgroupOf (localGroup i)
    let B := D.subgroupOf (localGroup i)
    have hV : Nat.card V = Nat.card J :=
      (Nat.card_congr (subgroupOfEquivOfLe hUi).toEquiv).trans hU
    have hB : Nat.card B = Nat.card E :=
      (Nat.card_congr (subgroupOfEquivOfLe (hDU.trans hUi)).toEquiv).trans hD
    let : Group.IsSolvable V := Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hUi).toMonoidHom) (subgroupOfEquivOfLe hUi).injective
    have hh := odd_card_dvd_three_of_small_nonsolvable_quotient f hf hk hc hn P V B
      (comap_mono hSU) inferInstance (hV ▸ h3) (comap_mono hDU) (hB ▸ ho)
    rwa [hB] at hh
  rcases proper_overgroup_le U hSU hUt with h0 | h2
  · apply branch 0 h0 CentralNormalizerThreePart.PairQuotient.fiveHom
      CentralNormalizerThreePart.PairQuotient.fiveHom_surjective
      (by rw [CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]; exact CentralInvolutionCore.core_isPGroup)
      (.inl (by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]))
    intro hs
    let := hs
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance
  · have hk : IsPGroup 2 baseElementary.normalizerMonoidHom.ker := by
      rw [baseNormalizer_ker_eq_pCore_of_surjective baseNormalizer_action_surjective]
      exact pCore_isPGroup
    apply branch 2 h2 baseElementary.normalizerMonoidHom baseNormalizer_action_surjective hk
      (.inr (by rw [Nat.card_congr baseAutomorphismEquiv.toEquiv,Matrix.PSL3Two.card_SL]))
    intro hs
    let := hs
    exact _root_.not_isSolvable_sl3_two (Group.isSolvable_of_surjective
      (f := baseAutomorphismEquiv.toMonoidHom) baseAutomorphismEquiv.surjective)

end Sporadic.LeechRelated.HS.SylowOvergroups
