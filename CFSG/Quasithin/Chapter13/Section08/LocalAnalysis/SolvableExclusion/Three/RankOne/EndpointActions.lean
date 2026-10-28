module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.Transport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Endpoint

/-!
# Excluding endpoint transvections in the solvable case

A common-axis transvection action on Uγ descends to the actual quotient
Uγ/A₁. The critical-pair conjugator identifies this action with the action
on U_H/V₁. Source 13.8.5(1) would supply a nonsolvable C-component for
any nonidentity transvection, so every descended action is trivial.
This contradicts the strict denominator D_H<U_H of 13.8.8(2).

The general quotient transport is reused from the five-primary development;
its argument has no five-primary hypothesis. The source implication remains
an earlier theorem input, not an assumed transvection exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.5(1),
13.8.10–11 and proof of 13.8.13, printed pp.947, 950–951.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
variable {G : Type*} [Group G]
open CriticalGeometry Five Five.Localization.EndpointGeometry

private theorem no_axis_of_quotient_action [Finite G]
    (P U Z D : Subgroup G) [IsElementaryAbelian 2 U]
    (hn : P ≤ normalizer (U : Set G))
    (rho : P →* MulAut (U ⧸ Z.subgroupOf U))
    (hrho : ∀ p : P, ∀ u : U,
      rho p (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(p : G) * (u : G) * (p : G)⁻¹,
            (mem_normalizer_iff.mp (hn p.property) u).mp u.property⟩)
    (hno : ∀ p : P, binaryLinear (rho p) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) → rho p = 1)
    (hproper : Source.DH P U Z < P) : ¬ HasTransvectionAxis P U D hn := by
  intro haxis
  apply hproper.not_ge
  apply le_commutatorPreimage le_rfl
  apply commutator_le.mpr
  intro p hp u hu
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let ql : Additive U →ₗ[ZMod 2] Additive (U ⧸ Z.subgroupOf U) :=
    { q.toAdditive with map_smul' := ZMod.map_smul q.toAdditive }
  have hq : Function.Surjective ql := by
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) x.toMul
    exact ⟨Additive.ofMul y, hy⟩
  have htrans := transvection_of_surjective_intertwiner ql hq
    (binaryLinear (conjugationAction P U hn ⟨p, hp⟩)) (binaryLinear (rho ⟨p, hp⟩))
    (fun x => (hrho ⟨p, hp⟩ x.toMul).symm) (haxis.2.2 ⟨p, hp⟩)
  have he := hrho ⟨p, hp⟩ ⟨u, hu⟩
  rw [hno ⟨p, hp⟩ htrans, MulAut.one_apply] at he
  have hh := QuotientGroup.eq_iff_div_mem.mp he.symm
  change (p * u * p⁻¹) / u ∈ Z at hh
  simpa only [coe_div, coe_mk, div_eq_mul_inv, commutatorElement_def] using hh

private theorem endpointAction_conjugation
    {L T H V V₃ V₁ : Subgroup G}
    (c : CriticalPair L T H V) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : StarAction H (Source.UH H V₃) V₁)
    [IsElementaryAbelian 2 (c.Ugamma V₃)]
    (j : vertexGroup L T H c.gamma) (u : c.Ugamma V₃) :
    endpointAction c V₃ V₁ a j
        (QuotientGroup.mk' ((c.Aone V₁).subgroupOf (c.Ugamma V₃)) u) =
      QuotientGroup.mk' ((c.Aone V₁).subgroupOf (c.Ugamma V₃))
        ⟨(j : G) * (u : G) * (j : G)⁻¹,
          (mem_normalizer_iff.mp (c.normalizes_Ugamma V₃ j.property) u).mp u.property⟩ := by
  obtain ⟨h, rfl⟩ := (endpointGroupEquiv c).surjective j
  obtain ⟨v, rfl⟩ := ((MulAut.conj (c.gb : G)).subgroupMap (Source.UH H V₃)).surjective u
  exact transportedAction_conjugation a (MulAut.conj (c.gb : G)) h v

/-- Source 13.8.5 excludes the common-axis action at the actual endpoint.
A transvection descends to Uγ/A₁; if every descended action were trivial,
then D_H would equal U_H, contradicting 13.8.8(2). -/
theorem no_endpoint_axis [Finite G] {L T H V V₃ V₁ : Subgroup G}
    (c : CriticalPair L T H V) [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (c.Ugamma V₃)]
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hUHJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃) :
    ¬ HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁)
      (hUHJ.trans (c.normalizes_Ugamma V₃)) := by
  let rho := (endpointAction c V₃ V₁ a).comp (inclusion hUHJ)
  apply no_axis_of_quotient_action _ _ _ _ _ rho
  · intro p u
    exact endpointAction_conjugation c a (inclusion hUHJ p) u
  · intro p ht
    exact endpointAction_eq_one_of_transvection c V₃ V₁ a hs h135 (inclusion hUHJ p) ht
  · exact hproper

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
end
