module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.PrimeObstruction
public import Theory.GroupAction.SubgroupConjugation
public import FeitThompson.PFsection6.PFsection6_5_a

/-!
# The split torus cannot normalize a Sylow subgroup at the primitive prime

For a nonidentity split-torus element, semiregularity on the actual cosets
forces its centralizer in M into the two-point stabilizer D. A p-subgroup
of M therefore has trivial fixed subgroup whenever p does not divide |D|.
If the torus normalizes that subgroup, orbit counting gives
q - 1 dividing its order minus one. The point-stabilizer order formula
puts its order in q² - q + 1, contradicting the primitive-prime obstruction.

This proves GLS4, Chapter 2, Lemma 14.4(a), conditional only on the shared
14.2–14.3 geometry and Proposition 12.13 semiregularity. The centralizer
embedding is not needed for this step. The final Suzuki contradiction and
the construction of those intermediate inputs remain separate obligations.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemma 14.4 and (14A), (14D), (14E).
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

/-- The split torus has the field order minus one, with the parameter fixed
by the actual Suzuki equivalence in the source context. -/
public theorem Context.torus_card :
    Nat.card (residualCommutator M t) = 2 ^ (2 * m + 1) - 1 := by
  have hDN := residualPairStabilizer_le_normalizer_residualGenerated
    d.minimal d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.even_pair
  obtain ⟨_, hc⟩ := residualGenerated_suzuki_pair_cyclic_card d.minimal.disconnected
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
  exact hc

/-- Centralizing a nonidentity split-torus element forces a point stabilizer
element to fix the second distinguished point as well. -/
public theorem Context.torus_centralizer_le_pair (hsemi : TorusSemiregular M t)
    {x : G} (hx : x ∈ residualCommutator M t) (hx1 : x ≠ 1) :
    M ⊓ centralizer ({x} : Set G) ≤ residualPairStabilizer M t := by
  let alpha : G ⧸ M := QuotientGroup.mk 1
  let beta : G ⧸ M := QuotientGroup.mk t
  have hbeta : beta ≠ alpha := by
    intro he
    apply d.t_not_mem_M
    have hh : t ∈ MulAction.stabilizer G alpha := by
      change t • alpha = alpha
      simpa [alpha, beta] using he
    rwa [baseCoset_stabilizer M] at hh
  have htI := d.minimal.disconnected.involutions t d.t_mem
  have hstab : MulAction.stabilizer G beta = rightConjugate M t := by
    have he : beta = t⁻¹ • alpha := by simp [beta, alpha, htI.inv_eq_self]
    rw [he, ← rightConjugate_stabilizer, baseCoset_stabilizer]
  intro y hy
  refine ⟨hy.1, ?_⟩
  have hya : y • alpha = alpha := by
    change y ∈ MulAction.stabilizer G alpha
    rw [baseCoset_stabilizer]
    exact hy.1
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp hy.2).symm
  have hfix : x • (y • beta) = y • beta := by
    rw [← mul_smul, hxy, mul_smul, (hsemi x hx hx1 beta).mpr (Or.inr rfl)]
  have hyb : y • beta = beta := by
    rcases (hsemi x hx hx1 (y • beta)).mp hfix with ha | hb
    · exact False.elim (hbeta ((MulAction.injective y) (ha.trans hya.symm)))
    · exact hb
  rw [← hstab]
  exact hyb

/-- The order of any p-subgroup lies in the cyclotomic factor when p is odd
and absent from the actual pair stabilizer. In particular this applies to Sylow subgroups. -/
public theorem Context.pSubgroup_card_dvd_cyclotomic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpD : ¬ p ∣ Nat.card (residualPairStabilizer M t))
    (R : Subgroup M) (hR : IsPGroup p R) :
    Nat.card R ∣ (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hR.exists_card_eq
  have hd := R.card_subgroup_dvd_card
  rw [d.card_pointStabilizer, ha] at hd
  have hcD : Nat.Coprime (p ^ a) (Nat.card (residualPairStabilizer M t)) :=
    (hp.coprime_pow_of_not_dvd hpD).symm
  have hc2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (fun h =>
    hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
  have hcq : Nat.Coprime (p ^ a) ((2 ^ (2 * m + 1)) ^ 3) :=
    ((hc2.pow_left a).pow_right (2 * m + 1)).pow_right 3
  rw [ha]
  exact hcq.dvd_of_dvd_mul_left (hcD.dvd_of_dvd_mul_right hd)

/-- The free conjugation action gives the source torus orbit congruence. -/
public theorem Context.torus_congruence_of_normalizes (hsemi : TorusSemiregular M t)
    {p : ℕ} (hp : p.Prime)
    (hpD : ¬ p ∣ Nat.card (residualPairStabilizer M t))
    (R : Subgroup M) (hR : IsPGroup p R)
    (hn : residualCommutator M t ≤ normalizer (R.map M.subtype : Set G)) :
    (2 ^ (2 * m + 1) - 1) ∣ Nat.card R - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := residualCommutator M t
  let H := R.map M.subtype
  let : MulDistribMulAction K H := conjMulDistribMulActionOfLeNormalizer K H hn
  have hH : IsPGroup p H := hR.map M.subtype
  have hfree (a : K) (ha : a ≠ 1) (v : H) (hv : a • v = v) : v = 1 := by
    by_contra hne
    have hc : Commute (a : G) (v : G) :=
      mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hv)
    have hvM : (v : G) ∈ M := map_subtype_le R v.property
    have hvD := d.torus_centralizer_le_pair hsemi a.property
      (fun he => ha (Subtype.ext he)) ⟨hvM, mem_centralizer_singleton_iff.mpr hc.symm.eq⟩
    have hdiv : p ∣ orderOf (v : G) := by simpa using hH.dvd_orderOf hne
    exact hpD (hdiv.trans ((residualPairStabilizer M t).orderOf_dvd_natCard hvD))
  have hd := Section6.natCard_actor_dvd_group_card_sub_one hfree
  rw [show Nat.card K = 2 ^ (2 * m + 1) - 1 from d.torus_card,
    show Nat.card H = Nat.card R from card_map_of_injective M.subtype_injective] at hd
  exact hd

/-- Lemma 14.4(a), retaining the primitive-prime data for the later Z-star
descent: no Sylow p-subgroup of M is normalized by the split torus. -/
public theorem Context.exists_prime_not_normalizing_sylow (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t) :
    ∃ p : ℕ, p.Prime ∧ 2 * m + 1 < p ∧ p ≠ 3 ∧
      orderOf (2 : ZMod p) = 6 * (2 * m + 1) ∧
      p ∣ (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1 ∧
      ¬ p ∣ Nat.card (residualPairStabilizer M t) ∧
      ∀ R : Sylow p M,
        ¬ residualCommutator M t ≤ normalizer ((R : Subgroup M).map M.subtype : Set G) := by
  obtain ⟨p, hp, hnp, hp3, hord, hpc, hpD, hobs⟩ := d.primitive_prime_obstruction g
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := d.parameter_pos; omega
  have hpM : p ∣ Nat.card M := by
    rw [d.card_pointStabilizer]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpc _) _
  refine ⟨p, hp, hnp, hp3, hord, hpc, hpD, ?_⟩
  intro R hn
  exact hobs R R.isPGroup' (R.ne_bot_of_dvd_card hpM)
    (d.pSubgroup_card_dvd_cyclotomic hp hp2 hpD R R.isPGroup')
    (d.torus_congruence_of_normalizes hsemi hp hpD R R.isPGroup' hn)

end BenderSuzuki.ZD.SuzukiExclusion
