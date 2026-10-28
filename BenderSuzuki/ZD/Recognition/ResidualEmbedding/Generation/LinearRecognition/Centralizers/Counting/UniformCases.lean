module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.SourceData
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Arithmetic

/-!
# Uniform residual centralizer cases from the earlier source counts

The cross-multiplied noncentral degree formula is impossible for each of the
three local exponents, using the proper-orbit bound and the prime-divisor
congruence. Thus every pair-stabilizer involution centralizes the distinguished
subgroup. The actual PSL₂ field-action alternative then forces `2*k = k`,
contrary to `k ≥ 2`, so it centralizes the whole residual group.

The fixed distinguished subgroup now has the full field order. Strict
monotonicity of the degree polynomial makes its local exponent independent
of the involution, yielding the three uniform alternatives with the literal
fixed-coset counts. Distinguished generation gives the containment in the
centralizer closure asserted in Lemma 12.9.

These theorems leave the two earlier inputs explicit. The Lemma 12.8 producer
and the Corollary 7.12/orbit-bound producer must still be supplied by the
source assembly; none of these conditional results asserts their existence.
Section 13's unitary exclusion is separate and the third branch is retained.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.9–12.10.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem fixed_distinguished_eq {v : G}
    (hc : v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G)) :
    closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) = closure (Z ∩ (M : Set G)) := by
  apply inf_eq_left.mpr
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc x hx)

omit [Finite G] in
private theorem numerical_centralizes_distinguished {z t v : G}
    (hnum : ResidualCentralizerNumerics Z M z t)
    (hgeo : ResidualCentralizerArithmeticInput Z M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  obtain ⟨k, i, d⟩ := hnum v hvD hv
  by_contra hn
  obtain ⟨hcard, hdegree⟩ := d.moving_degree hn
  exact ResidualCentralizerArithmetic.noncentral_impossible d.exponent_ge d.kind d.suzuki_odd
    (by simpa only [hcard] using hgeo.degree_gt) hdegree
    (by simpa only [hcard] using hgeo.congruence)

/-- Lemma 12.9 centralization from the two earlier-source inputs. The field
action is excluded by the actual distinguished-subgroup cardinalities. -/
public theorem proper_residualGenerated_centralizes_of_numerics
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hnum : ResidualCentralizerNumerics Z M z t)
    (hgeo : ResidualCentralizerArithmeticInput Z M) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      v ∈ centralizer (residualGenerated M z t : Set G) := by
  have hAL := proper_residualGenerated_contains_distinguishedClosure
    h r ha hz hzM ht htM hL heven
  intro v hvD hv
  have hvA := numerical_centralizes_distinguished hnum hgeo hvD hv
  rcases hlocal.involution_action v hvD hv with hc | ⟨k, hk, hfixed, hm, _⟩
  · exact hc
  · have hfull := (psl2_distinguishedClosure_elementary_card h.disconnected r
      hz hzM ht htM hL hm (by omega : 2 ≤ 2 * k) hAL).2
    rw [fixed_distinguished_eq hvA] at hfixed
    have he := Nat.pow_right_injective (by decide : 2 ≤ 2) (hfull.symm.trans hfixed)
    omega


/-- Uniform Lemma 12.10 alternatives, retaining the unitary case and all
fixed-coset counts. The two earlier-source producers remain explicit. -/
public theorem proper_residualGenerated_uniform_cases_of_numerics
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hnum : ResidualCentralizerNumerics Z M z t)
    (hgeo : ResidualCentralizerArithmeticInput Z M) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n ∧
      ResidualCentralizerCases Z M z t n := by
  obtain ⟨n, hn, _, _, _, _, _, _, _, hAn, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  have hcentral := proper_residualGenerated_centralizes_of_numerics
    h r ha hz hzM ht htM hL heven hlocal hnum hgeo
  have hnumN : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      ∃ i : ℕ, ResidualCentralizerNumericalWitness Z M z t v n i := by
    intro v hvD hv
    obtain ⟨k, i, d⟩ := hnum v hvD hv
    have hAk := d.fixed_distinguished
    rw [fixed_distinguished_eq (numerical_centralizes_distinguished hnum hgeo hvD hv)] at hAk
    have hkn : k = n := Nat.pow_right_injective (by decide : 2 ≤ 2) (hAk.symm.trans hAn)
    subst k
    exact ⟨i, d⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvorder⟩ := exists_prime_orderOf_dvd_card'
    (G := residualPairStabilizer M t) 2 heven.two_dvd
  have hv : PFAppendixIII.IsInvolution (v : G) :=
    IsInvolution.map_of_injective (orderOf_eq_prime_iff.mp hvorder).symm
      (residualPairStabilizer M t).subtype Subtype.val_injective
  obtain ⟨i, di⟩ := hnumN v v.property hv
  have hdegree := di.central_degree (numerical_centralizes_distinguished hnum hgeo v.property hv)
  have hq : 2 ≤ 2 ^ n := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ n by omega)
    simpa only [pow_one] using hp
  have hsame : ∀ w ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution w →
      ResidualCentralizerNumericalWitness Z M z t w n i := by
    intro w hwD hw
    obtain ⟨j, dj⟩ := hnumN w hwD hw
    have hdj := dj.central_degree (numerical_centralizes_distinguished hnum hgeo hwD hw)
    have hji := ResidualCentralizerArithmetic.central_degree_injective hq (hdj.symm.trans hdegree)
    subst j
    exact dj
  refine ⟨n, hn, hAn, ?_⟩
  rcases di.central_model (hcentral v v.property hv) with
    ⟨hi, _, hlinear⟩ | ⟨hi, _, m, hm, hnm, hsuzuki⟩ | ⟨hi, _, _, hlinear⟩
  · subst i
    left
    refine ⟨hlinear, ?_, ?_⟩
    · simp only [pow_one] at hdegree
      have hs := Nat.sub_add_cancel (show 1 ≤ 2 ^ n by omega)
      nlinarith
    · intro w hwD hw
      have dw := hsame w hwD hw
      have hc := dw.central_model (hcentral w hwD hw)
      rcases hc with ⟨_, hcollapse, _⟩ | ⟨hbad, _⟩ | ⟨hbad, _⟩
      · exact ⟨hcollapse, by simpa only [pow_one] using dw.fixed_cosets⟩
      · omega
      · omega
  · subst i
    right; left
    refine ⟨m, hm, hnm, hsuzuki, hdegree, ?_⟩
    intro w hwD hw
    have dw := hsame w hwD hw
    have hc := dw.central_model (hcentral w hwD hw)
    rcases hc with ⟨hbad, _⟩ | ⟨_, hcollapse, _⟩ | ⟨hbad, _⟩
    · omega
    · exact ⟨hcollapse, dw.fixed_cosets⟩
    · omega
  · subst i
    right; right
    refine ⟨hlinear, ?_, hdegree, ?_⟩
    · intro w hwD hw
      have hc := (hsame w hwD hw).central_model (hcentral w hwD hw)
      rcases hc with ⟨hbad, _⟩ | ⟨hbad, _⟩ | ⟨_, hlt, hcover, _⟩
      · omega
      · omega
      · exact ⟨hlt, hcover⟩
    · intro w hwD hw
      exact (hsame w hwD hw).fixed_cosets

/-- Both clauses of the source Lemma 12.9, conditional only on the earlier
local recognition, numerical count, and action inputs. -/
public theorem proper_residualGenerated_lemma129_of_numerics
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hnum : ResidualCentralizerNumerics Z M z t)
    (hgeo : ResidualCentralizerArithmeticInput Z M) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) ∧
        residualGenerated M z t ≤ centralizerClosure Z v := by
  intro v hvD hv
  exact ⟨numerical_centralizes_distinguished hnum hgeo hvD hv,
    residualGenerated_le_centralizerClosure_of_centralizes h.disconnected hz ht
      (proper_residualGenerated_centralizes_of_numerics h r ha hz hzM ht htM hL heven
        hlocal hnum hgeo v hvD hv)⟩

end BenderSuzuki.ZD
