module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.Lemma710
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.Conjugation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.Quotient
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.Structure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.ZJFactorization.Application

/-!
# The local conjugation step in the distinguished maximal-normalizer argument

Lemma 7.10 and the conjugated admissibility argument are proved in the
supporting modules. An odd normal factorization of `M₂` supplies the required
conjugating element by Sylow conjugacy. The canonical local structure and
ZJ arguments discharge this factorization and place its odd factor in the
triple stabilizer. No ambient strong embedding, oddness of `E`, or final
Sylow normalizer-chain conclusion is assumed.

Source: GLS, Volume 4, Chapter 2, Lemmas 7.10--7.11 and the final paragraph of
Proposition 7.1. The elementary Sylow conjugacy argument is adapted from
`BenderSuzuki.SE.Section7Final`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement
universe u

private theorem factorization_two_subgroupOf_eq_of_eq_sup_odd_normal
    {G : Type*} [Group G] [Finite G]
    {B T N : Subgroup G}
    (hTB : T ≤ B) (hNB : N ≤ B)
    (hBnormT : B ≤ Subgroup.normalizer (T : Set G))
    (hTodd : Odd (Nat.card T)) (hsup : B = T ⊔ N) :
    (Nat.card (N.subgroupOf B)).factorization 2 =
      (Nat.card B).factorization 2 := by
  classical
  let TB : Subgroup B := T.subgroupOf B
  let NB : Subgroup B := N.subgroupOf B
  have : TB.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTB).2
    exact hBnormT
  have hsupB : TB ⊔ NB = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hTB,
      Subgroup.map_subgroupOf_eq_of_le hNB,
      ← hsup]
    rw [← MonoidHom.range_eq_map]
    exact (Subgroup.range_subtype (H := B)).symm
  let qB : B →* B ⧸ TB := QuotientGroup.mk' TB
  let f : NB →* B ⧸ TB := qB.comp NB.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective TB y
    have hb : b ∈ TB ⊔ NB := by rw [hsupB]; trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hb with ⟨t, ht, n, hn, htn⟩
    let nn : NB := ⟨n, hn⟩
    refine ⟨nn, ?_⟩
    change qB n = qB b
    have hqt : qB t = 1 := (QuotientGroup.eq_one_iff t).2 ht
    rw [← htn, map_mul, hqt, one_mul]
  have hkerMapLe : f.ker.map NB.subtype ≤ TB := by
    intro b hb
    rcases Subgroup.mem_map.mp hb with ⟨n, hn, rfl⟩
    change qB n = 1 at hn
    exact (QuotientGroup.eq_one_iff (N := TB) (x := (n : B))).1 hn
  have hkerCardDvd : Nat.card f.ker ∣ Nat.card T := by
    have hmapCard : Nat.card (f.ker.map NB.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective NB.subtype_injective
    have hdiv : Nat.card (f.ker.map NB.subtype) ∣ Nat.card TB :=
      Subgroup.card_dvd_of_le hkerMapLe
    rw [show Nat.card TB = Nat.card T by
      simpa [TB] using natCard_subgroupOf_eq T B hTB, hmapCard] at hdiv
    exact hdiv
  have hkerOdd : Odd (Nat.card f.ker) := hTodd.of_dvd_nat hkerCardDvd
  have hquotCard : Nat.card (NB ⧸ f.ker) = Nat.card (B ⧸ TB) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hBcard := Subgroup.card_eq_card_quotient_mul_card_subgroup TB
  have hNBcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  calc
    (Nat.card NB).factorization 2 =
        (Nat.card (NB ⧸ f.ker) * Nat.card f.ker).factorization 2 := by
      rw [hNBcard]
    _ = (Nat.card (NB ⧸ f.ker)).factorization 2 := by
      rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
      simp only [Finsupp.add_apply]
      rw [Nat.factorization_eq_zero_of_not_dvd hkerOdd.not_two_dvd_nat]
      simp
    _ = (Nat.card (B ⧸ TB)).factorization 2 := by rw [hquotCard]
    _ = (Nat.card (B ⧸ TB) * Nat.card TB).factorization 2 := by
      rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
      simp only [Finsupp.add_apply]
      rw [show (Nat.card TB).factorization 2 = 0 by
        apply Nat.factorization_eq_zero_of_not_dvd
        have hTBodd : Odd (Nat.card TB) := by
          simpa [TB, natCard_subgroupOf_eq T B hTB] using hTodd
        exact hTBodd.not_two_dvd_nat]
      simp
    _ = (Nat.card B).factorization 2 := by rw [hBcard]

/-- If an involution lies in `B = T (B ∩ N_G(K))`, with `T` normal of odd
order, an element of `T` conjugates `K` to a subgroup normalized by that
involution. -/
private theorem theorem4b_exists_conjugate_normalized_of_eq_sup_odd_normal
    {G : Type*} [Group G] [Finite G]
    {B T K : Subgroup G} {z : G}
    (hTB : T ≤ B)
    (hBnormT : B ≤ Subgroup.normalizer (T : Set G))
    (hTodd : Odd (Nat.card T))
    (hsup : B = T ⊔ (B ⊓ Subgroup.normalizer (K : Set G)))
    (hzB : z ∈ B) (hz : IsInvolution z) :
    ∃ x : G, x ∈ T ∧
      z ∈ Subgroup.normalizer (K.conjBy x : Set G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := B ⊓ Subgroup.normalizer (K : Set G)
  have hNB : N ≤ B := inf_le_left
  let TB : Subgroup B := T.subgroupOf B
  let NB : Subgroup B := N.subgroupOf B
  have : TB.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTB).2
    exact hBnormT
  have hsupB : TB ⊔ NB = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hTB,
      Subgroup.map_subgroupOf_eq_of_le hNB,
      ← hsup]
    rw [← MonoidHom.range_eq_map]
    exact (Subgroup.range_subtype (H := B)).symm
  have hfac : (Nat.card NB).factorization 2 =
      (Nat.card B).factorization 2 := by
    exact factorization_two_subgroupOf_eq_of_eq_sup_odd_normal
      hTB hNB hBnormT hTodd (by simpa [N] using hsup)
  let SN : Sylow 2 NB := Classical.choice inferInstance
  let SB0 : Subgroup B := (SN : Subgroup NB).map NB.subtype
  have hSB0card : Nat.card SB0 =
      2 ^ (Nat.card B).factorization 2 := by
    rw [show Nat.card SB0 = Nat.card (SN : Subgroup NB) by
      exact Subgroup.card_map_of_injective NB.subtype_injective,
      SN.card_eq_multiplicity, hfac]
  let SB : Sylow 2 B := Sylow.ofCard SB0 hSB0card
  let zB : B := ⟨z, hzB⟩
  have hzBI : IsInvolution zB := IsInvolution.subtype hz hzB
  have hzP : IsPGroup 2 (Subgroup.zpowers zB) := by
    have horder : orderOf zB = 2 :=
      (orderOf_eq_prime_iff).2 ⟨hzBI.sq_eq_one, hzBI.ne_one⟩
    apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers zB) (n := 1)
    simp [Nat.card_zpowers, horder]
  obtain ⟨Pz, hzlePz⟩ := IsPGroup.exists_le_sylow hzP
  have hzPz : zB ∈ (Pz : Subgroup B) :=
    hzlePz (Subgroup.mem_zpowers zB)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B SB Pz
  have hPzConj : (Pz : Subgroup B) = (SB : Subgroup B).conjBy g := by
    rw [← hg]
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.conjBy]
    congr 1
  have hgSup : g ∈ TB ⊔ NB := by
    rw [hsupB]
    trivial
  rcases Subgroup.mem_sup_of_normal_left.mp hgSup with
    ⟨t, htT, n, hnN, htn⟩
  have hzConj : zB ∈ (SB : Subgroup B).conjBy g := by
    rw [← hPzConj]
    exact hzPz
  rw [Subgroup.conjBy, Subgroup.mem_map] at hzConj
  rcases hzConj with ⟨s0, hs0, hsEq⟩
  have hSBleNB : (SB : Subgroup B) ≤ NB := by
    change SB0 ≤ NB
    exact Subgroup.map_subtype_le _
  have hsN : (s0 : G) ∈ N := hSBleNB hs0
  have hnNG : (n : G) ∈ N := hnN
  have hyN : (n : G) * (s0 : G) * (n : G)⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem hnNG hsN) (N.inv_mem hnNG)
  have hzNconj : z ∈ N.conjBy (t : G) := by
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨(n : G) * (s0 : G) * (n : G)⁻¹, hyN, ?_⟩
    change (t : G) * ((n : G) * (s0 : G) * (n : G)⁻¹) * (t : G)⁻¹ = z
    calc
      _ = ((t * n : B) : G) * (s0 : G) * ((t * n : B) : G)⁻¹ := by
        change (t : G) * ((n : G) * (s0 : G) * (n : G)⁻¹) * (t : G)⁻¹ =
          ((t : G) * (n : G)) * (s0 : G) * (((t : G) * (n : G))⁻¹)
        group
      _ = (g : G) * (s0 : G) * (g : G)⁻¹ := by rw [htn]
      _ = z := congrArg Subtype.val hsEq
  refine ⟨(t : G), ?_, ?_⟩
  · exact htT
  · exact (section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (H := N) (K := K) inf_le_right (t : G)) hzNconj

/-- The post-Lemma-7.11 conjugation step. The local argument must produce
`B = M₂`, `T = theta(M₂)` and discharge every displayed premise. -/
public theorem action_exists_admissible_ZJ_conjugate_of_odd_factorization
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta)
    (B T : Subgroup G)
    (hTB : T ≤ B)
    (hBnormT : B ≤ Subgroup.normalizer (T : Set G))
    (hTodd : Odd (Nat.card T))
    (hTE : T ≤ theorem4bSection7E M d.z beta)
    (hzB : d.z ∈ B)
    (hfactor : B = T ⊔ (B ⊓ Subgroup.normalizer
      (corollary64Z ⟨d.p, d.hp⟩ q.R : Set G))) :
    ∃ x ∈ theorem4bSection7E M d.z beta,
      ∃ a : ActionAdmissibleQ d beta,
        a.Q = corollary64Z ⟨d.p, d.hp⟩ (q.R.conjBy x) := by
  obtain ⟨x, hxT, hzx⟩ :=
    theorem4b_exists_conjugate_normalized_of_eq_sup_odd_normal
      hTB hBnormT hTodd hfactor hzB d.hz
  obtain ⟨a, ha, _, _⟩ :=
    action_admissible_ZJ_conjugate_of_normalized h d q (hTE hxT) hzx
  exact ⟨x, hTE hxT, a, ha⟩

/-- Lemma 7.11 and Sylow conjugacy supply the admissible conjugate, with
all properties of the actual quotient-defined M₂ discharged. -/
public theorem action_exists_admissible_ZJ_conjugate
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    ∃ x ∈ theorem4bSection7E M d.z beta,
      ∃ a : ActionAdmissibleQ d beta,
        a.Q = corollary64Z ⟨d.p, d.hp⟩ (q.R.conjBy x) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let B := actionLocalM2InG Z M q.chosen.Q
  obtain ⟨_, _, hzB, hTE, hsolv, hSylow, hR, hcore, htheta⟩ :=
    actionLocal_structure h r d hne q
  apply action_exists_admissible_ZJ_conjugate_of_odd_factorization h.disconnected
    d q B (corollary64Theta d.p B)
  · exact (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  · exact theorem4b_section7_theta_le_normalizer B
  · exact lemma75_theta_odd_card d.p B
  · exact hTE
  · exact hzB
  · exact q.localM2_zj_factorization hsolv hSylow hR hcore htheta

end BenderSuzuki.ZD
