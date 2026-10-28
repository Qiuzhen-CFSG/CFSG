module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Setup
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.GeometryContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.OddNormalizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.Action
public import Theory.SpecificGroups.Suzuki.OddInversion
public import Theory.GroupAction.PrimeOrderConjugation

/-!
# Freeness on the moved Suzuki cosets

Assume the source split torus is semiregular away from the two marked
cosets. A nontrivial point stabilizer in `L` contains an element of prime
order. Distinguished involutions cannot fix a moved point. For an odd
prime dividing `q - 1`, the actual torus `K ≤ L` has index prime to that
prime, so a conjugator in `L` puts the element in `K`. Conjugating the
point preserves movement because the given involution centralizes `L`.

For the remaining primes, conjugation on the nonidentity elements of the
normal distinguished closure in the point stabilizer gives a distinguished
centralizing involution. The concrete Suzuki model supplies an inverting
involution in `L`, which is also distinguished. Lemma 12.12 excludes this
configuration. Cauchy's theorem then rules out any nontrivial stabilizer.

The final two applications give regularity and the actual injective
centralizer homomorphism with only torus semiregularity still explicit.
Its independent producer and the unconditional assembly remain with
`Regularity`; no regularity or model-inversion premise is assumed here.

Source: GLS, Volume 4, Chapter 2, Lemma 12.14(a–b),
`refs/KGroup/GLS4/Chapter2.tex`, lines 2325–2345.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

/-- The concrete Suzuki inverter lies in `L` and is therefore distinguished. -/
public theorem Context.odd_element_distinguished_inverter
    (x : residualGenerated M z t) (hx : Odd (orderOf x)) :
    ∃ s ∈ Z, s * (x : G) * s⁻¹ = (x : G)⁻¹ := by
  obtain ⟨s, hs, hinv⟩ := MatrixGroups.suzuki_odd_element_inverted_by_involution
    (by have := d.parameter_pos; omega) (d.model x)
    (by
      change Odd (orderOf (d.model.toMonoidHom x))
      rwa [orderOf_injective d.model.toMonoidHom d.model.injective])
  let y := d.model.symm s
  have hy : orderOf (y : G) = 2 := by
    rw [orderOf_coe]
    exact (orderOf_injective d.model.symm.toMonoidHom d.model.symm.injective s).trans hs
  have hyZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper y.property).mp
    ((orderOf_eq_prime_iff.mp hy).symm)
  refine ⟨y, hyZ, ?_⟩
  have he : y * x * y⁻¹ = x⁻¹ := d.model.injective (by simpa only
    [map_mul, map_inv, y, MulEquiv.apply_symm_apply] using hinv)
  exact congrArg Subtype.val he

/-- An odd-prime element whose order divides `q - 1` is conjugate into the actual `K` by an element of `L`. -/
public theorem Context.prime_dvd_torus_conjugate
    (x : residualGenerated M z t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : orderOf x = p) (hpd : p ∣ 2 ^ (2 * m + 1) - 1) :
    ∃ g : residualGenerated M z t,
      ((g⁻¹ * x * g : residualGenerated M z t) : G) ∈ residualCommutator M t := by
  let L := residualGenerated M z t
  let K := (residualCommutator M t).subgroupOf L
  let q := 2 ^ (2 * m + 1)
  have hKL : residualCommutator M t ≤ L := by
    rw [d.torus_structure.1]
    exact inf_le_right
  have hKcard : Nat.card K = q - 1 :=
    (Nat.card_congr (subgroupOfEquivOfLe hKL).toEquiv).trans d.torus_structure.2.2.1
  have hindex : K.index = (q ^ 2 + 1) * q ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < q - 1 from hKcard ▸ Nat.card_pos)
    have hc := K.card_mul_index
    rw [hKcard, d.card_residualGenerated] at hc
    exact hc.trans (by dsimp [q]; ring)
  have hpnq : ¬ p ∣ q := by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hpn : ¬ p ∣ q ^ 2 + 1 := by
    intro hd
    have hq : 1 ≤ q := Nat.one_le_two_pow
    have he : q ^ 2 + 1 = (q - 1) * (q + 1) + 2 := by
      have hh := Nat.sub_add_cancel hq
      nlinarith
    rw [he] at hd
    have hdprod : p ∣ (q - 1) * (q + 1) := dvd_mul_of_dvd_left hpd (q + 1)
    have hd2 : p ∣ 2 := (Nat.dvd_add_iff_right hdprod).mpr hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2)
  have hi : ¬ p ∣ K.index := by
    rw [hindex]
    exact hp.not_dvd_mul hpn (fun h => hpnq (hp.dvd_of_dvd_pow h))
  exact Theory.GroupAction.exists_conjugate_mem_of_prime_order K hp hx hi

/-- A prime-order element fixing a coset centralizes a distinguished element when its prime does not divide `q - 1`. -/
public theorem Context.prime_fixedPoint_distinguished_centralizer
    {x : G} {p : ℕ} (hp : p.Prime) (hx : orderOf x = p)
    (hpd : ¬ p ∣ 2 ^ (2 * m + 1) - 1)
    {beta : G ⧸ M} (hfix : x • beta = beta) :
    ∃ s ∈ Z, Commute x s := by
  induction beta using Quotient.inductionOn with
  | h b =>
    let A := closure (Z ∩ (M : Set G))
    let y := MulAut.conj b⁻¹ x
    have hyM : y ∈ M := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hfix
      simpa only [y, MulAut.conj_apply, inv_inv, mul_inv_rev, mul_assoc] using M.inv_mem hfix
    have hyorder : orderOf y = p :=
      (orderOf_injective (MulAut.conj b⁻¹).toMonoidHom (MulAut.conj b⁻¹).injective x).trans hx
    have hyN : y ∈ normalizer (A : Set G) := by
      rwa [distinguishedClosure_normalizer d.minimal.disconnected]
    obtain ⟨a, ha, hane, hcomm⟩ := Theory.GroupAction.exists_commuting_nonidentity_of_prime_order
      A hp hyorder hyN (by rwa [d.distinguishedClosure_elementary_card.2])
    have hAL := proper_residualGenerated_contains_distinguishedClosure d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
    let : IsElementaryAbelian 2 A := d.distinguishedClosure_elementary_card.1
    have haZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated d.minimal.disconnected
      d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper (hAL ha)).mp
      ⟨hane, elemPow_eq_one_of_isElementaryAbelian a ha⟩
    refine ⟨MulAut.conj b a, d.minimal.disconnected.invariant b a haZ, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, y, MulAut.conj_apply, inv_inv, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one] using
      hcomm.map (MulAut.conj b).toMonoidHom

/-- All three prime-order branches of Lemma 12.14(a), conditional only on torus semiregularity. -/
public theorem Context.prime_not_fix_movedPoint
    (htorus : TorusSemiregular M t) {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (x : residualGenerated M z t) {p : ℕ} (hp : p.Prime) (hx : orderOf x = p)
    {beta : G ⧸ M} (hbeta : u • beta ≠ beta) : (x : G) • beta ≠ beta := by
  intro hfix
  have hxord : orderOf (x : G) = p := (orderOf_coe x).trans hx
  by_cases hp2 : p = 2
  · exact d.involution_not_fix_movedPoint huD hu x.property
      ((orderOf_eq_prime_iff.mp (hxord.trans hp2)).symm) hbeta hfix
  have hxodd : Odd (orderOf (x : G)) := hxord ▸ hp.odd_of_ne_two hp2
  have hxne : (x : G) ≠ 1 := by
    intro he
    have ho := orderOf_eq_one_iff.mpr he
    rw [hxord] at ho
    exact hp.ne_one ho
  by_cases hpd : p ∣ 2 ^ (2 * m + 1) - 1
  · obtain ⟨g, hg⟩ := d.prime_dvd_torus_conjugate x hp hp2 hx hpd
    let y : residualGenerated M z t := g⁻¹ * x * g
    let gamma : G ⧸ M := ((g⁻¹ : residualGenerated M z t) : G) • beta
    have hyne : (y : G) ≠ 1 := by
      intro he
      apply hxne
      have he' := congrArg (fun a : G => (g : G) * a * (g : G)⁻¹) he
      simpa only [y, coe_mul, coe_inv, mul_assoc, mul_inv_cancel_left,
        inv_mul_cancel_left, mul_one, mul_inv_cancel] using he'
    have hyfix : (y : G) • gamma = gamma := by
      simp only [y, gamma, coe_mul, coe_inv, mul_smul, smul_inv_smul, hfix]
    have huJ := d.involution_mem_centralizer huD hu
    have hgammamove : u • gamma ≠ gamma := by
      intro he
      apply hbeta
      apply MulAction.injective ((g⁻¹ : residualGenerated M z t) : G)
      change ((g⁻¹ : residualGenerated M z t) : G) • (u • beta) =
        ((g⁻¹ : residualGenerated M z t) : G) • beta
      rw [← mul_smul, mem_centralizer_iff.mp huJ _ (g⁻¹).property, mul_smul]
      exact he
    have hbase : u • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
      change u ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
      rw [baseCoset_stabilizer]
      exact huD.1
    have htL : t ∈ residualGenerated M z t :=
      (show zpowers t ≤ residualGenerated M z t from
        le_sup_of_le_left le_sup_right) (mem_zpowers t)
    have htfix : u • (QuotientGroup.mk t : G ⧸ M) = QuotientGroup.mk t := by
      have he : (QuotientGroup.mk t : G ⧸ M) = t • (QuotientGroup.mk 1 : G ⧸ M) := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      rw [he, ← mul_smul, ← mem_centralizer_iff.mp huJ t htL, mul_smul, hbase]
    rcases (htorus (y : G) hg hyne gamma).mp hyfix with he | he
    · exact hgammamove (he ▸ hbase)
    · exact hgammamove (he ▸ htfix)
  · obtain ⟨s, hsZ, hscomm⟩ := d.prime_fixedPoint_distinguished_centralizer hp hxord hpd hfix
    obtain ⟨v, hvZ, hvinv⟩ := d.odd_element_distinguished_inverter x
      (by rwa [← orderOf_coe])
    have hbot := d.odd_inverted_centralizerClosure_eq_bot hxne hxodd hvZ hvinv
    have hsC : s ∈ centralizerClosure Z (x : G) := subset_closure
      ⟨hsZ, mem_centralizer_singleton_iff.mpr hscomm.symm⟩
    rw [hbot] at hsC
    exact (d.minimal.disconnected.involutions s hsZ).ne_one hsC

/-- Lemma 12.14(a): every stabilizer in `L` of a moved coset is trivial, assuming Proposition 12.13. -/
public theorem Context.movedPoint_free_of_torus_semiregular
    (htorus : TorusSemiregular M t) {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (x : residualGenerated M z t) (beta : G ⧸ M)
    (hbeta : u • beta ≠ beta) (hfix : (x : G) • beta = beta) : x = 1 := by
  by_contra hxne
  let H := MulAction.stabilizer (residualGenerated M z t) beta
  have hH : H ≠ ⊥ := by
    intro he
    have hxH : x ∈ H := hfix
    rw [he] at hxH
    exact hxne hxH
  have hc : Nat.card H ≠ 1 := fun he => hH (Subgroup.card_eq_one.mp he)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpd
  exact d.prime_not_fix_movedPoint htorus huD hu y.val hp
    ((orderOf_coe y).trans hy) hbeta y.property

/-- The source cardinalities turn the established freeness into regularity. -/
public theorem Context.regular_on_moved_of_torus_semiregular
    (htorus : TorusSemiregular M t) {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    {a b : G ⧸ M} (ha : u • a ≠ a) (hb : u • b ≠ b) :
    ∃! x : residualGenerated M z t, (x : G) • a = b :=
  d.regular_on_moved_of_free huD hu
    (d.movedPoint_free_of_torus_semiregular htorus huD hu) ha hb

/-- Lemma 12.14(b): the centralizer embeds into `L`, assuming only torus semiregularity. -/
public theorem Context.centralizer_embedding_of_torus_semiregular
    (htorus : TorusSemiregular M t) {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    ∃ f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t,
      Function.Injective f :=
  d.centralizer_embedding_of_regular huD hu
    (fun _ _ ha hb => d.regular_on_moved_of_torus_semiregular htorus huD hu ha hb)

end BenderSuzuki.ZD.SuzukiExclusion
