module

public import Theory.GroupTheory.CentralPChiefFactors
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Central two-chief factors above an odd normal subgroup

If a finite group K has an odd normal subgroup N with quasisimple quotient,
every normal two-section B/(A ∩ B) is central in K/A. In particular all
actual two-chief factors of K are central.

Write P and M for the images of B and N in K/A. The relative quotient is
explicitly identified with P, so P is a two-group and P ∩ M = 1 by coprime
orders. The quotient (K/A)/M is a surjective image of K/N. Its normal
two-subgroup coming from P is central: a nontrivial quasisimple image has
only central proper normal subgroups and cannot itself be a two-group.
Consequently [K/A,P] lies in both P and M, and hence is trivial.

Source: the chief-factor step in Aschbacher–Smith, *The Classification of
Quasithin Groups*, proof of 1.2.10, printed p.507, using the common A.3.6
conclusions on pp.43–45 (combined manuscript of 1 March 2004).
-/

public section

open Subgroup
namespace Theory.GroupTheory

private theorem normal_two_subgroup_le_center_of_quasisimple_image
    {Q D : Type*} [Group Q] [Group D] [Finite D] [IsQuasisimple Q]
    (f : Q →* D) (hf : Function.Surjective f)
    (P : Subgroup D) [P.Normal] (hp : IsPGroup 2 P) : P ≤ center D := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases subsingleton_or_nontrivial D with hD | hD
  · let := hD
    intro x hx
    simp [Subsingleton.elim x 1]
  · let := hD
    let : IsQuasisimple D := IsQuasisimple.of_surjective f hf
    rcases IsQuasisimple.normal_le_center_or_eq_top P with hc | ht
    · exact hc
    · have htop : IsPGroup 2 (⊤ : Subgroup D) := ht ▸ hp
      have hpD : IsPGroup 2 D := htop.of_equiv Subgroup.topEquiv
      let : Group.IsNilpotent D := hpD.isNilpotent
      exact (Group.IsPerfect.not_isSolvable D inferInstance).elim

private theorem normal_two_section_central
    {K : Type*} [Group K] [Finite K]
    (N : Subgroup K) [N.Normal] (hN : Nat.Coprime 2 (Nat.card N))
    [IsQuasisimple (K ⧸ N)]
    (A B : Subgroup K) [A.Normal] [B.Normal]
    (hp : IsPGroup 2 (B ⧸ A.subgroupOf B)) :
    B.map (QuotientGroup.mk' A) ≤ center (K ⧸ A) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' A
  let P := B.map q
  let M := N.map q
  let r := QuotientGroup.mk' M
  have hk : (q.subgroupMap B).ker = A.subgroupOf B := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  let e : (B ⧸ A.subgroupOf B) ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap B)
        (q.subgroupMap_surjective B))
  have hpP : IsPGroup 2 P := hp.of_equiv e
  have hM : Nat.Coprime 2 (Nat.card M) :=
    hN.coprime_dvd_right (card_map_dvd N q)
  have hdis : Disjoint P M := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpP
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hM.pow_left n
  have hkill : N ≤ (r.comp q).ker := by
    intro x hx
    change r (q x) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem q hx)
  let f : (K ⧸ N) →* ((K ⧸ A) ⧸ M) := QuotientGroup.lift N (r.comp q) hkill
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk'_surjective M).comp
      (QuotientGroup.mk'_surjective A) y
    exact ⟨QuotientGroup.mk' N x, rfl⟩
  have hcentral : P.map r ≤ center ((K ⧸ A) ⧸ M) :=
    normal_two_subgroup_le_center_of_quasisimple_image f hf (P.map r) (hpP.map r)
  have hcM : ⁅(⊤ : Subgroup (K ⧸ A)), P⁆ ≤ M :=
    (map_mk_le_center_iff M P).mp hcentral
  have hcP : ⁅(⊤ : Subgroup (K ⧸ A)), P⁆ ≤ P := commutator_le_right _ _
  apply commutator_top_left_eq_bot_iff_le_center.mp
  exact le_bot_iff.mp ((le_inf hcP hcM).trans (disjoint_iff.mp hdis).le)

/-- An odd normal subgroup with quasisimple quotient forces every actual
normal two-chief interval to be central. -/
theorem hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
    {K : Type*} [Group K] [Finite K]
    (N : Subgroup K) [N.Normal] (hN : Nat.Coprime 2 (Nat.card N))
    (hQ : IsQuasisimple (K ⧸ N)) : HasCentralPChiefFactors 2 K := by
  let := hQ
  intro A B hA hB _ _ hp
  let := hA
  let := hB
  exact normal_two_section_central N hN A B hp

end Theory.GroupTheory
