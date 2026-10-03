module

public import Glauberman.PSL2SubfieldEmbedding
public import Glauberman.PSL2NineEmbedding
public import Glauberman.PSL2PrimeAlternatingFive
public import GorensteinWalter.LinearRingEquiv
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.GroupTheory.MinimalSimple
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import GorensteinWalter.A5

/-!
# Complete parameter restrictions on minimal-simple odd-field PSL2

A field embedding induces an actual PSL2 embedding. When the source field
has more than three elements, its PSL2 is nonsolvable by perfection. Minimal
simplicity therefore forces surjectivity, and strict growth of the projective
group orders forces equality of the field orders.

Consequently an odd field supporting a minimal-simple PSL2 is either a prime
field of order greater than three or a power of three with prime exponent.
The equivalences below are induced by actual finite-field isomorphisms.
The exceptional order-five model is identified with binary PSL2(4) through
A5. Actual A5 embeddings exclude degree two in characteristic three and
prime-field orders congruent to one or four modulo five: minimal simplicity
would force these embeddings to be surjective, contradicting group orders.
Thus the final theorem gives precisely binary PSL2(4), prime-field PSL2(p)
with p > 3 and p congruent to two or three modulo five, or PSL2(3^f) with
f an odd prime, all through actual group isomorphisms.

Source: Thompson's minimal-simple parameter argument, roadmap M4, and the
finite-field subfield theorem.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.MatrixGroups BenderSuzuki.External GorensteinWalter Glauberman.Dickson

/-- The exceptional order-five model belongs to the binary family, with
prime exponent two. -/
public theorem psl2_card_five_equiv_binary_four
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nonempty (PSL2MatrixGroup K ≃* PSL2MatrixGroup (GaloisField 2 2)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype K := Fintype.ofFinite K
  let eK : K ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (K := K) (K' := ZMod 5) (by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hK)
  obtain ⟨eFive⟩ := alternatingGroupFive_equiv_PSL2
  obtain ⟨eFour⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  exact ⟨((psl2RingEquiv eK).trans eFive.symm).trans eFour.symm⟩

/-- A subfield with more than three elements cannot be proper when the
ambient PSL2 is minimal simple. -/
public theorem minimalSimple_psl2_fieldEmbedding_card_eq
    {K F : Type*} [Field K] [Field F] [Finite K] [Finite F]
    (hG : IsMinimalSimple (PSL2MatrixGroup F)) (e : K →+* F)
    (hK : 3 < Nat.card K) : Nat.card K = Nat.card F := by
  have hle := Nat.card_le_card_of_injective e e.injective
  by_contra hne
  have hlt := psl2_card_lt_of_field_embedding e (lt_of_le_of_ne hle hne)
  obtain ⟨f, hf⟩ := exists_psl2_embedding e
  let : Group.IsPerfect (PSL2MatrixGroup K) := psl2_isPerfect_of_card_gt_three K hK
  have hsurj := hG.surjective_of_injective
    (Group.IsPerfect.not_isSolvable (PSL2MatrixGroup K)) f hf
  exact hlt.ne (Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩))

/-- A dividing field degree whose PSL2 is nonsolvable must be the full degree. -/
public theorem minimalSimple_psl2_degree_eq_of_dvd
    {p d n : ℕ} [Fact p.Prime] (hd : d ≠ 0) (hn : n ≠ 0)
    (hdiv : d ∣ n) (hlarge : 3 < p ^ d)
    (hG : IsMinimalSimple (PSL2MatrixGroup (GaloisField p n))) : d = n := by
  have hdegree : Module.finrank (ZMod p) (GaloisField p d) ∣
      Module.finrank (ZMod p) (GaloisField p n) := by
    rwa [GaloisField.finrank p hd, GaloisField.finrank p hn]
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdegree
  have hcard := minimalSimple_psl2_fieldEmbedding_card_eq hG e.toRingHom
    (by rwa [GaloisField.card p d hd])
  rw [GaloisField.card p d hd, GaloisField.card p n hn] at hcard
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard

/-- In odd characteristic, the subfield obstruction leaves degree one or
characteristic three with prime degree. -/
public theorem minimalSimple_odd_galoisField_parameters
    {p n : ℕ} [Fact p.Prime] (hpodd : Odd p) (hn : n ≠ 0)
    (hlarge : 3 < p ^ n)
    (hG : IsMinimalSimple (PSL2MatrixGroup (GaloisField p n))) :
    (3 < p ∧ n = 1) ∨ (p = 3 ∧ n.Prime) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hpne2 : p ≠ 2 := by
    rintro rfl
    exact (by decide : ¬ Odd (2 : ℕ)) hpodd
  by_cases hp3 : p = 3
  · right
    refine ⟨hp3, ?_⟩
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn1 : n = 1 := by omega
      simp [hp3, hn1] at hlarge
    by_contra hnot
    obtain ⟨d, hdiv, hd, hdn⟩ := Nat.exists_dvd_of_not_prime2 hn2 hnot
    have hpow : 3 < p ^ d := by
      calc
        3 < p ^ 2 := by norm_num [hp3]
        _ ≤ p ^ d := Nat.pow_le_pow_right (by omega) hd
    have heq := minimalSimple_psl2_degree_eq_of_dvd (by omega) hn hdiv hpow hG
    omega
  · left
    have hpgt : 3 < p := by omega
    refine ⟨hpgt, ?_⟩
    exact (minimalSimple_psl2_degree_eq_of_dvd (by decide) hn (one_dvd n)
      (by simpa using hpgt) hG).symm

/-- Actual model equivalences after the subfield reduction. The A5 witness
exclusions refine these alternatives further. -/
public theorem minimalSimple_odd_psl2_subfield_reduction
    {K : Type*} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (hlarge : 3 < Nat.card K) (hG : IsMinimalSimple (PSL2MatrixGroup K)) :
    (∃ (p : ℕ) (hp : Fact p.Prime),
      letI := hp
      3 < p ∧ Nonempty (PSL2MatrixGroup K ≃* PSL2MatrixGroup (ZMod p))) ∨
    (∃ f : ℕ, f.Prime ∧
      Nonempty (PSL2MatrixGroup K ≃* PSL2MatrixGroup (GaloisField 3 f))) := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' K
  let : Fact p.Prime := ⟨hp⟩
  have hn : (n : ℕ) ≠ 0 := ne_of_gt n.pos
  have hcard' : Nat.card K = p ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hpodd : Odd p := by
    rw [hcard'] at hodd
    exact (Nat.odd_pow_iff hn).mp hodd
  let : Fintype (GaloisField p n) := Fintype.ofFinite _
  let eK : K ≃+* GaloisField p n := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, GaloisField.card p n hn] using hcard')
  let e := psl2RingEquiv eK
  rcases minimalSimple_odd_galoisField_parameters hpodd hn
      (by rwa [← hcard']) (hG.of_mulEquiv e) with hprime | hthree
  · left
    obtain ⟨hpgt, hn1⟩ := hprime
    refine ⟨p, inferInstance, hpgt, ?_⟩
    let ePrime : K ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      simpa [hn1] using hcard)
    exact ⟨psl2RingEquiv ePrime⟩
  · right
    obtain ⟨rfl, hnprime⟩ := hthree
    exact ⟨n, hnprime, ⟨e⟩⟩

/-- The A5 witness cannot fill PSL2 over a field of order greater than five. -/
private theorem no_alternatingFive_embedding {K : Type*} [Field K] [Finite K]
    (hK : 5 < Nat.card K) (hG : IsMinimalSimple (PSL2MatrixGroup K))
    (f : alternatingGroup (Fin 5) →* PSL2MatrixGroup K)
    (hf : Function.Injective f) : False := by
  have hns : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
    intro hsolv
    let _ := hsolv
    have hproper := Group.IsSolvable.commutator_lt_top_of_nontrivial
      (G := alternatingGroup (Fin 5))
    rw [commutator_alternatingGroup_eq_top (by simp)] at hproper
    exact (lt_irrefl _ hproper)
  have hsurj := hG.surjective_of_injective hns f hf
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
  have h60 : Nat.card (PSL2MatrixGroup K) = 60 := by
    rw [← hcard, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have horder := huppert614_card_psl_mul_center (K := K)
  have hcenter : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) ≤ 2 := by
    by_cases hn : (-1 : K) = 1
    · rw [huppert614_card_center_of_neg_one_eq_one hn]
      omega
    · rw [huppert614_card_center_of_neg_one_ne_one hn]
  rw [h60] at horder
  have hbound : Nat.card K * (Nat.card K ^ 2 - 1) ≤ 120 := by omega
  have hsq : 35 ≤ Nat.card K ^ 2 - 1 := by
    have hpow : 6 ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have : 210 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by nlinarith
  omega

/-- The actual A5 subgroup of PSL2(9) obstructs minimal simplicity. -/
public theorem not_isMinimalSimple_psl2_nine :
    ¬ IsMinimalSimple (PSL2MatrixGroup (GaloisField 3 2)) := by
  intro hG
  obtain ⟨f, hf⟩ := exists_alternatingGroupFive_embedding_psl2_nine
  exact no_alternatingFive_embedding
    (by rw [GaloisField.card 3 2 (by decide)]; norm_num) hG f hf

/-- The prime-field A5 witnesses force the two allowed residues modulo five. -/
public theorem minimalSimple_psl2_prime_residue
    {p : ℕ} [Fact p.Prime] (hp : 5 < p)
    (hG : IsMinimalSimple (PSL2MatrixGroup (ZMod p))) :
    p % 5 = 2 ∨ p % 5 = 3 := by
  have hpmod : p % 5 ≠ 0 := by
    intro h
    have hdiv : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Fact.out : p.Prime).eq_one_or_self_of_dvd 5 hdiv
    omega
  have hnot : ¬ (p % 5 = 1 ∨ p % 5 = 4) := by
    intro hmod
    obtain ⟨f, hf⟩ := exists_alternatingGroupFive_embedding_psl2_prime p hp hmod
    exact no_alternatingFive_embedding (by simpa using hp) hG f hf
  have := Nat.mod_lt p (by decide : 0 < 5)
  omega

/-- Minimal simplicity forces the characteristic-three field degree to be an odd prime. -/
public theorem minimalSimple_psl2_three_exponent_odd_prime
    {f : ℕ} (hf : f ≠ 0) (hlarge : 3 < 3 ^ f)
    (hG : IsMinimalSimple (PSL2MatrixGroup (GaloisField 3 f))) :
    f.Prime ∧ Odd f := by
  have hprime : f.Prime := by
    rcases minimalSimple_odd_galoisField_parameters (by decide : Odd 3)
      hf hlarge hG with h | h
    · omega
    · exact h.2
  refine ⟨hprime, hprime.odd_of_ne_two ?_⟩
  rintro rfl
  exact not_isMinimalSimple_psl2_nine hG

/-- Complete odd-field parameter necessity, with actual equivalences to the
three permitted models and PSL2(5) normalized to binary PSL2(4). -/
public theorem minimalSimple_odd_psl2_parameters
    {K : Type*} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (hlarge : 3 < Nat.card K) (hG : IsMinimalSimple (PSL2MatrixGroup K)) :
    Nonempty (PSL2MatrixGroup K ≃* PSL2MatrixGroup (GaloisField 2 2)) ∨
    (∃ (p : ℕ) (hp : Fact p.Prime),
      letI := hp
      3 < p ∧ (p % 5 = 2 ∨ p % 5 = 3) ∧
        Nonempty (PSL2MatrixGroup K ≃* PSL2MatrixGroup (ZMod p))) ∨
    (∃ f : ℕ, f.Prime ∧ Odd f ∧
      Nonempty (PSL2MatrixGroup K ≃* PSL2MatrixGroup (GaloisField 3 f))) := by
  rcases minimalSimple_odd_psl2_subfield_reduction hodd hlarge hG with hprime | hthree
  · obtain ⟨p, hp, hpgt, ⟨e⟩⟩ := hprime
    let _ := hp
    by_cases hp5 : p = 5
    · subst p
      obtain ⟨eFive⟩ := psl2_card_five_equiv_binary_four (K := ZMod 5) (by simp)
      exact Or.inl ⟨e.trans eFive⟩
    · have hpgreater : 5 < p := by
        have := (Fact.out : p.Prime).eq_two_or_odd
        omega
      exact Or.inr (Or.inl ⟨p, hp, hpgt,
        minimalSimple_psl2_prime_residue hpgreater (hG.of_mulEquiv e), ⟨e⟩⟩)
  · obtain ⟨f, hf, ⟨e⟩⟩ := hthree
    have hfodd : Odd f := hf.odd_of_ne_two (by
      rintro rfl
      exact not_isMinimalSimple_psl2_nine (hG.of_mulEquiv e))
    exact Or.inr (Or.inr ⟨f, hf, hfodd, ⟨e⟩⟩)

end Stellmacher.Recognition
