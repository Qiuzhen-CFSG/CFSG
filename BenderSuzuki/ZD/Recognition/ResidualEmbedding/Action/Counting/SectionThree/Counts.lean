module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Inputs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Swapping

/-!
# Sylow arithmetic for the distinguished Section 3 counts

The local invariant Sylow and centralizer-index inputs imply the inverted-set
bounds at a swapped pair and at a pair containing the base point. For the
converse saturation implication, extend inside the triple stabilizer and
compare the centralizer's prime part. Only the odd-prime subgroups have odd
order; the two-point and triple stabilizers may have even order.

These are conditional proofs of the numerical steps. The local and index
premises are separate geometric obligations which final assembly must prove.

Source: GLS, Volume 4, Chapter 2, Propositions 3.7(c,d) and 3.8(b,c), pp.30--31.
The arithmetic and triple-stabilizer argument adapt `SE.Theorem4`, replacing
its ambient strong-embedding assumption by the exact local inputs.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem sylow_data {p : ℕ} (hp : p.Prime) {P D : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P D) :
    P ≤ D ∧ IsPGroup p P ∧ Nat.card P = p ^ (Nat.card D).factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, rfl⟩ := hP
  refine ⟨?_, Q.isPGroup'.map D.subtype, ?_⟩
  · simpa using Subgroup.map_le_range D.subtype (Q : Subgroup D)
  · rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact Sylow.card_eq_multiplicity Q

private theorem pgroup_odd {p : ℕ} (hprime : p.Prime) (hp : Odd p) {P : Subgroup G}
    (hP : IsPGroup p P) : Odd (Nat.card P) := by
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact hp.pow

private theorem pgroup_card_le {p : ℕ} (hp : p.Prime) {P D : Subgroup G}
    (hP : IsPGroup p P) (hPD : P ≤ D) :
    Nat.card P ≤ p ^ (Nat.card D).factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have hfac := Nat.factorization_le_factorization_of_dvd_right
    (a := p) (Subgroup.card_dvd_of_le hPD) Nat.card_pos.ne' Nat.card_pos.ne'
  rw [ha, Nat.factorization_pow_self hp] at hfac
  rw [ha]
  exact Nat.pow_le_pow_right hp.pos hfac

private theorem primePart_mul {D : Subgroup G} {t z : G} {p : ℕ}
    (hindex : ((D ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf D).index = theorem4bM M z) :
    p ^ (Nat.card (D ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)).factorization p *
      theorem4bPrimeShare M z p = p ^ (Nat.card D).factorization p := by
  let C := D ⊓ Subgroup.centralizer ({t} : Set G)
  have hcardSub : Nat.card (C.subgroupOf D) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ≤ D from inf_le_left))
  have hcard : Nat.card C * theorem4bM M z = Nat.card D := by
    rw [← hcardSub, ← hindex]
    exact (C.subgroupOf D).card_mul_index
  have hmne : theorem4bM M z ≠ 0 := by
    rw [← hindex]
    exact Subgroup.index_ne_zero_of_finite
  have hfac : (Nat.card C).factorization p + (theorem4bM M z).factorization p =
      (Nat.card D).factorization p := by
    have hf := congrArg (fun n : ℕ => n.factorization p) hcard
    rw [Nat.factorization_mul Nat.card_pos.ne' hmne] at hf
    exact hf
  rw [theorem4bPrimeShare, ← pow_add, hfac]

private theorem inverted_sylow_lower {D P : Subgroup G} {t z : G} {p : ℕ}
    (ht : IsInvolution t) (hp : p.Prime) (hpOdd : Odd p)
    (hPNorm : t ∈ Subgroup.normalizer (P : Set G))
    (hPSylow : theorem4bIsSylowSubgroupOf p P D)
    (hindex : ((D ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf D).index = theorem4bM M z) :
    theorem4bPrimeShare M z p ≤ theorem4bInvertedCard t P := by
  obtain ⟨hPD, hPp, hPcard⟩ := sylow_data hp hPSylow
  have hfixed := theorem4b_card_eq_card_fixed_mul_inverted ht (pgroup_odd hp hpOdd hPp) hPNorm
  have hCPle := pgroup_card_le hp hPp.to_inf_left
    (inf_le_inf hPD (le_refl (Subgroup.centralizer ({t} : Set G))))
  have hpart := primePart_mul (p := p) hindex
  have hmul :
      p ^ (Nat.card (D ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)).factorization p *
          theorem4bPrimeShare M z p ≤
      p ^ (Nat.card (D ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)).factorization p *
          theorem4bInvertedCard t P := by
    calc
      _ = Nat.card P := hpart.trans hPcard.symm
      _ = _ := hfixed
      _ ≤ _ := Nat.mul_le_mul_right _ hCPle
  exact Nat.le_of_mul_le_mul_left hmul (pow_pos hp.pos _)

private theorem inverted_sylow_eq {D Q R : Subgroup G} {t z : G} {p : ℕ}
    (ht : IsInvolution t) (hp : p.Prime) (hpOdd : Odd p)
    (hQNorm : t ∈ Subgroup.normalizer (Q : Set G))
    (hQ : theorem4bIsSylowSubgroupOf p Q D)
    (hR : theorem4bIsSylowSubgroupOf p R (D ⊓ Subgroup.centralizer ({t} : Set G)))
    (hRQ : R ≤ Q)
    (hindex : ((D ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf D).index = theorem4bM M z) :
    theorem4bInvertedCard t Q = theorem4bPrimeShare M z p := by
  obtain ⟨hQD, hQp, hQcard⟩ := sylow_data hp hQ
  obtain ⟨hRC, _, hRcard⟩ := sylow_data hp hR
  have hCQcard : Nat.card (Q ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) =
      p ^ (Nat.card (D ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)).factorization p := by
    apply le_antisymm (pgroup_card_le hp hQp.to_inf_left (inf_le_inf hQD le_rfl))
    rw [← hRcard]
    exact Subgroup.card_le_of_le (le_inf hRQ (hRC.trans inf_le_right))
  have hfixed := theorem4b_card_eq_card_fixed_mul_inverted ht (pgroup_odd hp hpOdd hQp) hQNorm
  have he := primePart_mul (p := p) hindex
  rw [← hQcard, ← hCQcard] at he
  exact Nat.mul_left_cancel Nat.card_pos (hfixed.symm.trans he.symm)

/-- Proposition 3.7(c,d), from local invariant Sylows and the swapping index. -/
public theorem sectionThree_swapping_bound (h : IsProductDisconnected Z M)
    (hl : SectionThreeLocal Z M) (hi : SectionThreeIndices Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) {t : G} (ht : t ∈ Z)
    (beta : G ⧸ M) (hb : t • beta ≠ beta) {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    {P : Subgroup G} (hPp : IsPGroup p P)
    (hPD : P ≤ MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta))
    (hPNorm : t ∈ Subgroup.normalizer (P : Set G)) :
    theorem4bInvertedCard t P ≤ theorem4bPrimeShare M z p ∧
      (theorem4bIsSylowSubgroupOf p P
        (MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta)) →
        theorem4bInvertedCard t P = theorem4bPrimeShare M z p) := by
  let D := MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta)
  have hNormD : t ∈ Subgroup.normalizer (D : Set G) := by
    simpa [D] using theorem4b_mem_normalizer_tripleStabilizer
      (M := (⊤ : Subgroup G)) (beta := beta) (h.involutions t ht) (Subgroup.mem_top t)
  obtain ⟨Q, hQ, hPQ, hNormQ, R, hR, hRQ⟩ :=
    hl.swapping_sylow t ht beta hb p hp hpOdd D P le_rfl hNormD hPp hPD hPNorm
  have he := inverted_sylow_eq (h.involutions t ht) hp hpOdd hNormQ hQ hR hRQ
    (hi.swapping z hz hzM t ht beta hb)
  have hle := (theorem4bInvertedCard_mono (z := t) hPQ).trans_eq he
  refine ⟨hle, fun hP => le_antisymm hle ?_⟩
  exact inverted_sylow_lower (h.involutions t ht) hp hpOdd hPNorm hP
    (hi.swapping z hz hzM t ht beta hb)

/-- Proposition 3.8(b), from the swapped pair `beta, z • beta`. -/
public theorem sectionThree_base_bound (h : IsProductDisconnected Z M)
    (hl : SectionThreeLocal Z M) (hi : SectionThreeIndices Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    (beta : G ⧸ M) (hb : beta ≠ QuotientGroup.mk 1)
    {P : Subgroup G} (hPp : IsPGroup p P)
    (hPD : P ≤ M ⊓ MulAction.stabilizer G beta)
    (hPNorm : z ∈ Subgroup.normalizer (P : Set G)) :
    theorem4bInvertedCard z P ≤ theorem4bPrimeShare M z p ∧
      (theorem4bIsSylowSubgroupOf p P (M ⊓ MulAction.stabilizer G beta) →
        theorem4bInvertedCard z P = theorem4bPrimeShare M z p) := by
  have hmove : z • beta ≠ beta := fun he => hb (action_fixedPoint_eq_base h hz hzM he)
  have hPF : P ≤ MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (z • beta) :=
    le_inf (hPD.trans inf_le_right)
      (theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer hPNorm
        (hPD.trans inf_le_right))
  have hle := (sectionThree_swapping_bound h hl hi hz hzM hz beta hmove hp hpOdd hPp hPF hPNorm).1
  refine ⟨hle, fun hP => le_antisymm hle ?_⟩
  exact inverted_sylow_lower (h.involutions z hz) hp hpOdd hPNorm hP (hi.base z hz hzM beta hb)

/-- Proposition 3.8(c): saturation is equivalent to an invariant Sylow. -/
public theorem sectionThree_invariant_sylow (h : IsProductDisconnected Z M)
    (hl : SectionThreeLocal Z M) (hi : SectionThreeIndices Z M)
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M) {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    (beta : G ⧸ M) (hbeta : beta ≠ QuotientGroup.mk 1) :
    ((∃ Q : Subgroup G,
        theorem4bIsSylowSubgroupOf p Q (M ⊓ MulAction.stabilizer G beta) ∧
        z ∈ Subgroup.normalizer (Q : Set G)) ↔
      ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ M ⊓ MulAction.stabilizer G beta ∧
        z ∈ Subgroup.normalizer (P : Set G) ∧
        theorem4bInvertedCard z P = theorem4bPrimeShare M z p) := by
  have hz := h.involutions z hzZ
  let D : Subgroup G := M ⊓ MulAction.stabilizer G beta
  let E : Subgroup G := D ⊓ MulAction.stabilizer G (z • beta)
  let C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let CD : Subgroup G := D ⊓ C
  let CE : Subgroup G := E ⊓ C
  let : Fact p.Prime := ⟨hp⟩
  have hzNormE : z ∈ Subgroup.normalizer (E : Set G) := by
    simpa [E, D] using
      theorem4b_mem_normalizer_tripleStabilizer hz hzM
  have hCEeq : CE = CD := by
    simpa [CE, CD, E, D, C] using
      theorem4b_tripleStabilizer_inf_centralizer_eq M z beta
  constructor
  · rintro ⟨Q, hQSylow, hzNormQ⟩
    obtain ⟨Qd, hQeq⟩ := hQSylow
    have hQD : Q ≤ D := by
      rw [hQeq]
      simpa using
        (Subgroup.map_le_range D.subtype (Qd : Subgroup D))
    have hQp : IsPGroup p Q := by
      rw [hQeq]
      exact Qd.isPGroup'.map D.subtype
    refine ⟨Q, hQp, hQD, hzNormQ, ?_⟩
    have h38b := sectionThree_base_bound h hl hi hzZ hzM hp hpOdd beta hbeta hQp hQD hzNormQ
    exact h38b.2 ⟨Qd, hQeq⟩
  · rintro ⟨P, hPp, hPD, hzNormP, hPinv⟩
    have hPE : P ≤ E := by
      simpa [E, D] using
        theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer
          hzNormP hPD
    have hmove : z • beta ≠ beta := fun he => hbeta (action_fixedPoint_eq_base h hzZ hzM he)
    have hEF : E ≤ MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (z • beta) :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    obtain ⟨Q, hQSylowE, hPQ, hzNormQ, S, hSSylow, hSQ⟩ :=
      hl.swapping_sylow z hzZ beta hmove p hp hpOdd E P hEF hzNormE hPp hPE hzNormP
    obtain ⟨Qe, hQeq⟩ := hQSylowE
    have hQE : Q ≤ E := by
      rw [hQeq]
      simpa using
        (Subgroup.map_le_range E.subtype (Qe : Subgroup E))
    have hQD : Q ≤ D := hQE.trans inf_le_left
    have hQp : IsPGroup p Q := by
      rw [hQeq]
      exact Qe.isPGroup'.map E.subtype
    obtain ⟨Se, hSeq⟩ := hSSylow
    have hSCE : S ≤ CE := by
      rw [hSeq]
      simpa using
        (Subgroup.map_le_range CE.subtype (Se : Subgroup CE))
    have hScard : Nat.card S = p ^ (Nat.card CE).factorization p := by
      rw [hSeq, Subgroup.card_map_of_injective CE.subtype_injective]
      exact Sylow.card_eq_multiplicity Se
    let CQ : Subgroup G := Q ⊓ C
    have hSleCQ : S ≤ CQ := le_inf hSQ (hSCE.trans inf_le_right)
    have hcentralPartLe :
        p ^ (Nat.card CD).factorization p ≤ Nat.card CQ := by
      calc
        p ^ (Nat.card CD).factorization p =
            p ^ (Nat.card CE).factorization p := by rw [hCEeq]
        _ = Nat.card S := hScard.symm
        _ ≤ Nat.card CQ := Subgroup.card_le_of_le hSleCQ
    have hinvertedLe : theorem4bPrimeShare M z p ≤
        theorem4bInvertedCard z Q := by
      calc
        theorem4bPrimeShare M z p = theorem4bInvertedCard z P := hPinv.symm
        _ ≤ theorem4bInvertedCard z Q := theorem4bInvertedCard_mono hPQ
    have hQodd : Odd (Nat.card Q) := pgroup_odd hp hpOdd hQp
    have hQfactor :
        Nat.card Q = Nat.card CQ * theorem4bInvertedCard z Q := by
      simpa [CQ, C] using
        theorem4b_card_eq_card_fixed_mul_inverted hz hQodd hzNormQ
    have hprimePart :
        p ^ (Nat.card CD).factorization p * theorem4bPrimeShare M z p =
          p ^ (Nat.card D).factorization p := primePart_mul (hi.base z hzZ hzM beta hbeta)
    have htargetLe :
        p ^ (Nat.card D).factorization p ≤ Nat.card Q := by
      rw [← hprimePart, hQfactor]
      exact Nat.mul_le_mul hcentralPartLe hinvertedLe
    have hQdvd : Nat.card Q ∣ Nat.card D :=
      Subgroup.card_dvd_of_le hQD
    obtain ⟨a, hQcardPow⟩ := hQp.exists_card_eq
    have ha_le : a ≤ (Nat.card D).factorization p := by
      have hfac := Nat.factorization_le_factorization_of_dvd_right
        (a := p) hQdvd Nat.card_pos.ne' Nat.card_pos.ne'
      rw [hQcardPow, Nat.factorization_pow_self hp] at hfac
      exact hfac
    have hQle : Nat.card Q ≤ p ^ (Nat.card D).factorization p := by
      rw [hQcardPow]
      exact Nat.pow_le_pow_right hp.pos ha_le
    have hQcard : Nat.card Q = p ^ (Nat.card D).factorization p :=
      Nat.le_antisymm hQle htargetLe
    have hQdcard : Nat.card (Q.subgroupOf D) =
        p ^ (Nat.card D).factorization p := by
      rw [natCard_subgroupOf_eq Q D hQD, hQcard]
    refine ⟨Q, ?_, hzNormQ⟩
    refine ⟨Sylow.ofCard (Q.subgroupOf D) hQdcard, ?_⟩
    have hmap := Subgroup.subgroupOf_map_subtype Q D
    change Q = (Q.subgroupOf D).map D.subtype
    exact (inf_eq_left.mpr hQD).symm.trans hmap.symm


end BenderSuzuki.ZD
