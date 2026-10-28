module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.ZStarDescent.Quotient
public import FeitThompson.BGsection3.Remaining
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupAction.Quotient

/-!
# Lifting a torus-invariant Sylow subgroup through the distinguished closure

Let A be the distinguished closure in M. A normal Sylow p-subgroup of M/A
has a normal preimage E, of order |A| times a power of p. The actual Suzuki
torus K is cyclic of odd order and lies in the pair stabilizer D. Thus,
when p is absent from |D|, the conjugation action of K on E is coprime.
The solvable-operator invariant-Sylow theorem selects a K-invariant Sylow
subgroup of E. Its index in M remains prime to p, so it is Sylow in M.

This is an actual lift under the map M → M/A, followed by the inclusion
M → G. No normality of the lifted Sylow subgroup is assumed or inferred
solely from quotient normality. The input that the quotient p-core is Sylow
is supplied by `Quotient.quotient_pCore_sylow_of_normalizer` after its local
normalizer premises have been discharged.

Source: GLS, Volume 4, Chapter 2, final paragraph of Proposition 14.1,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2620–2630.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII
open scoped IsMulCommutative

namespace ZStarDescent

private theorem invariant_sylow_lift
    {H : Type*} [Group H] [Finite H] (A K : Subgroup H) [A.Normal]
    [Group.IsSolvable K] (hA : IsPGroup 2 A) (hKodd : Odd (Nat.card K))
    (p : ℕ) [Fact p.Prime] (hpK : ¬ p ∣ Nat.card K)
    (Rbar : Sylow p (H ⧸ A)) [(Rbar : Subgroup (H ⧸ A)).Normal] :
    ∃ R : Sylow p H, K ≤ normalizer ((R : Subgroup H) : Set H) := by
  let pi := QuotientGroup.mk' A
  let E := (Rbar : Subgroup (H ⧸ A)).comap pi
  have hEindex : ¬ p ∣ E.index := by
    rw [show E = (Rbar : Subgroup (H ⧸ A)).comap pi from rfl,
      (Rbar : Subgroup (H ⧸ A)).index_comap_of_surjective (QuotientGroup.mk'_surjective A)]
    exact Rbar.not_dvd_index
  have hcop : Nat.Coprime (Nat.card K) (Nat.card E) := by
    obtain ⟨a, ha⟩ := hA.exists_card_eq
    obtain ⟨r, hr⟩ := Rbar.isPGroup'.exists_card_eq
    have hQ : Nat.card (E ⧸ pi.ker.subgroupOf E) = Nat.card Rbar :=
      card_quotient_subgroupOf_comap_eq pi (QuotientGroup.mk'_surjective A) Rbar
    have hker : Nat.card (pi.ker.subgroupOf E) = Nat.card A := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap pi Rbar)).toEquiv,
        QuotientGroup.ker_mk']
    have hcard := card_eq_card_quotient_mul_card_subgroup (pi.ker.subgroupOf E)
    rw [hQ, hker, ha, hr] at hcard
    rw [hcard]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpK).symm.pow_right r |>.mul_right
      (hKodd.coprime_two_right.pow_right a)
  let : MulDistribMulAction K E :=
    conjMulDistribMulActionOfLeNormalizer K E le_normalizer_of_normal
  obtain ⟨P, hPI⟩ := exists_invariant_sylow_of_solvable_operator_coprime hcop (p := p)
  have hIndex : ¬ p ∣ ((P : Subgroup E).map E.subtype).index := by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hEindex
  let R := (P.isPGroup'.map E.subtype).toSylow hIndex
  refine ⟨R, ?_⟩
  intro k hk
  apply mem_normalizer_iff.mpr
  intro x
  have hforward (a : K) {y : H} (hy : y ∈ (R : Subgroup H)) :
      (a : H) * y * (a : H)⁻¹ ∈ (R : Subgroup H) := by
    obtain ⟨yE, hyE, rfl⟩ := hy
    exact ⟨a • yE, (hPI.invariant a yE).mp hyE, rfl⟩
  constructor
  · exact hforward ⟨k, hk⟩
  · intro hx
    have hh := hforward (⟨k, hk⟩ : K)⁻¹ hx
    simpa only [Subgroup.coe_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using hh

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

private theorem torus_structure (d : Context Z M z t m) :
    IsCyclic (residualCommutator M t) ∧
      residualCommutator M t ≤ residualPairStabilizer M t ∧
      Odd (Nat.card (residualCommutator M t)) := by
  have hDN := residualPairStabilizer_le_normalizer_residualGenerated
    d.minimal d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.even_pair
  obtain ⟨hcyc, hc⟩ := residualGenerated_suzuki_pair_cyclic_card d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
    (by have := d.parameter_pos; omega) d.model
  have ho : Odd (Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G)) := by
    rw [hc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega : 2 * m + 1 ≠ 0)) odd_one
  rw [residualCommutator_eq_local_pair (d.minimal.disconnected.involutions t d.t_mem)
    hDN ho (fun _ hx => residualGenerated_suzuki_pair_inverted d.minimal.disconnected
      d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
      (by have := d.parameter_pos; omega) d.model hx)]
  exact ⟨hcyc, inf_le_left, ho⟩

/-- A normal Sylow subgroup in M/A admits a torus-invariant lift in M.
The lift uses coprime solvable-operator action on its full preimage; it
does not infer normality of a Sylow subgroup from quotient normality. -/
public theorem exists_torus_invariant_sylow_of_quotient_pCore_sylow
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (p : ℕ) [Fact p.Prime]
    (hpD : ¬ p ∣ Nat.card (residualPairStabilizer M t)) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    (∃ Rbar : Sylow p (M ⧸ A), (Rbar : Subgroup (M ⧸ A)) = pCore p (M ⧸ A)) →
      ∃ R : Sylow p M,
        residualCommutator M t ≤ normalizer ((R : Subgroup M).map M.subtype : Set G) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  change (∃ Rbar : Sylow p (M ⧸ A), (Rbar : Subgroup (M ⧸ A)) = pCore p (M ⧸ A)) → _
  rintro ⟨Rbar, hRbar⟩
  let : (Rbar : Subgroup (M ⧸ A)).Normal := hRbar ▸ inferInstance
  obtain ⟨hcyc, hKD, hKodd⟩ := torus_structure d
  let K := (residualCommutator M t).subgroupOf M
  have hKM : residualCommutator M t ≤ M := hKD.trans inf_le_left
  let : IsCyclic (residualCommutator M t) := hcyc
  let : IsCyclic K := (subgroupOfEquivOfLe hKM).isCyclic.mpr hcyc
  have hKcard : Nat.card K = Nat.card (residualCommutator M t) :=
    Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hKcard]
    exact fun hd => hpD (hd.trans (card_dvd_of_le hKD))
  have hA : IsPGroup 2 A := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro a
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have ha : (a.val.val : G) ∈ (closure (Z ∩ (M : Set G)) : Set G) := a.property
    rw [← g.P_involutions] at ha
    simpa only [pow_one, Subgroup.coe_pow, Subgroup.coe_one] using ha.2
  obtain ⟨R, hR⟩ := invariant_sylow_lift A K hA (hKcard.symm ▸ hKodd) p hpK Rbar
  refine ⟨R, ?_⟩
  intro k hk
  exact le_normalizer_map M.subtype (mem_map_of_mem M.subtype
    (hR (show (⟨k, hKM hk⟩ : M) ∈ K from hk)))

end ZStarDescent
end BenderSuzuki.ZD.SuzukiExclusion
