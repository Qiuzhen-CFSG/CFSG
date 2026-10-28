module
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.PGroupCore
public import Theory.GroupTheory.AutomorphismInvariantNormalKernel
public import Theory.GroupTheory.MinimalParabolicCentralizerKernel
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualCentralization

/-!
# The central-chief kernel in the original rank-one pushing-up group

For the actual maximal automorphism-invariant normal kernel N_alpha, the
Sylow-centralizer maximality test forces C_H(N_alpha) to supplement O2(H)
whenever Omega1 Z(O2(H)) is not contained in N_alpha. The two-residual then
centralizes N_alpha, so every actual ambient chief factor inside it is central.
This proves the original Lemma 7.3 with its literal kernel and core omega.

The final intersection argument constructs such a kernel once the cyclic-orbit
formula of Lemma 7.6 is supplied. Nontriviality of the core omega is proved
from F*(H)=O2(H) and the non-two quotient. The orbit formula remains an explicit
source input; the other Main Hypothesis inheritance properties and subsequent
Sylow structure are separate from this central-chief conclusion.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 7.3 and the final
paragraph of Theorem 7.2, printed pp.60–62.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

private theorem omega_center_ne_bot (P : Subgroup H)
    (hP : IsPGroup 2 P) (hPne : P ≠ ⊥) : omegaCenterIn P ≠ ⊥ := by
  let _ : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  let _ : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center P) := hP.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have htwo : 2 ∣ Nat.card (Subgroup.center P) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hi := omega₁_map_subtype_ne_bot (G := P) (Subgroup.center P) 2 htwo
  intro hb
  apply hi
  apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
  simpa only [omegaCenterIn, Subgroup.map_bot] using hb

theorem core_omega_ne_bot_of_generalizedFitting_eq
    (hf : generalizedFitting H = pCore 2 H) (hH : ¬ IsPGroup 2 H) :
    omegaCenterIn (pCore 2 H) ≠ ⊥ := by
  apply omega_center_ne_bot _ pCore_isPGroup
  intro hb
  have hc := centralizer_generalizedFitting_le H
  rw [hf, hb] at hc
  have hx (x : H) : x = 1 := mem_bot.mp (hc (by
    intro y hy
    have he : y = 1 := mem_bot.mp hy
    simp only [he, one_mul, mul_one]))
  let : Subsingleton H := subsingleton_of_forall_eq 1 hx
  exact hH (IsPGroup.of_subsingleton 2 H)

open NilesRankOneKernel

/-- Niles7.3 for the actual maximal automorphism-invariant normal kernel. -/
theorem invariantKernel_central_chief_of_omega_not_le
    (S : Sylow 2 H) (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K)) (α : MulAut S)
    (hV : ¬ omegaCenterIn (pCore 2 H) ≤
      (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype) :
    ∃ s : NoncentralChiefRefinement.SeriesOn
      ((invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype),
      ∀ i, s.Central i := by
  let N := (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype
  have hNS : N ≤ (S : Subgroup H) := map_subtype_le _
  have hp : IsPGroup 2 N := S.isPGroup'.of_injective (inclusion hNS) (inclusion_injective hNS)
  have hr : pResidual 2 H ≤ centralizer (N : Set H) :=
    MinimalParabolicKernel.residual_centralizes_normal_sylow_kernel S hu K hK N
      (omegaCenterIn (pCore 2 H)) hNS
      (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1)
      (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1) hV
      (sylow_inf_centralizer_le_kernel_of_le_twoCore S α)
  obtain ⟨s⟩ := NoncentralChiefRefinement.SeriesOn.exists_series N
  exact ⟨s, s.central_of_residual_centralizes hp hr⟩

/-- The final7.2 intersection argument yields the actual central-chief kernel.
Only the explicit cyclic-orbit identity of7.6 remains an earlier source input. -/
theorem exists_central_chief_invariantKernel_of_orbit_formula
    (S : Sylow 2 H) (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K))
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hformula : ∀ α : MulAut S,
      (omegaCenterIn (pCore 2 H)).subgroupOf (S : Subgroup H) ≤
        invariantNormalKernel (S : Subgroup H) α →
      invariantNormalKernel (S : Subgroup H) α =
        ⨅ n : ℤ, ((pCore 2 H).subgroupOf (S : Subgroup H)).map ((α ^ n).toMonoidHom)) :
    ∃ α : MulAut S, ∃ s : NoncentralChiefRefinement.SeriesOn
      ((invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype),
      ∀ i, s.Central i := by
  have hH : ¬ IsPGroup 2 H := fun hp => hK (hp.to_quotient K)
  have hVS : omegaCenterIn (pCore 2 H) ≤ (S : Subgroup H) :=
    fun _ hx => pCore_isPGroup.le_sylow_of_normal S
      (((mem_omegaCenterIn_iff (pCore 2 H) _).mp hx).1)
  have hne : (omegaCenterIn (pCore 2 H)).subgroupOf (S : Subgroup H) ≠ ⊥ := by
    intro hb
    have hh := congrArg (Subgroup.map (S : Subgroup H).subtype) hb
    rw [map_subgroupOf_eq_of_le hVS, Subgroup.map_bot] at hh
    exact core_omega_ne_bot_of_generalizedFitting_eq hf hH hh
  obtain ⟨α,hα⟩ := exists_not_le_invariantNormalKernel (S : Subgroup H) hno
    ((pCore 2 H).subgroupOf (S : Subgroup H))
    ((omegaCenterIn (pCore 2 H)).subgroupOf (S : Subgroup H)) hne hformula
  refine ⟨α, invariantKernel_central_chief_of_omega_not_le S hu K hK α ?_⟩
  intro hl
  apply hα
  intro v hv
  obtain ⟨w,hw,he⟩ := hl hv
  have he' : w = v := Subtype.ext he
  exact he' ▸ hw

end Theory.GroupTheory
