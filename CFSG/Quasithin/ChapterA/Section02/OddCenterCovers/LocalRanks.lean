module

public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.BinaryLinear
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.OddRanks
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.Quasithin.LocalRank
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Degree-three ordinary and two-local ranks for the odd-center branch

This is the source adapter for the concrete rank clauses in A.2.12(I) and
A.2.18.  It works with the model records from `Statements.Models`, preserving
the coefficient field of order `(2^n)^2` and its displayed Frobenius
conjugation in the unitary case. The ordinary determinant bound, full split
Borel torus, odd-characteristic involution centralizers, and binary unitary
root normalizers yield the exact ordinary and local rank clauses. Elementary
subgroups in the literal original carrier feed the central-product argument.
-/

public section

set_option linter.style.haveILetI false

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.ChapterA.Section02.OddCenterCovers

variable {G : Type*} [Group G] [Finite G]

private theorem cyclic_supplement_rank {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (D : Subgroup G)
    (hD : D ≤ normalizer (S : Set G)) (hcyc : IsCyclic D)
    (hsup : (S : Subgroup G) ⊔ D = normalizer (S : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p (normalizer (S : Set G)) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let B := normalizer (S : Set G)
  let Q := (S : Subgroup G).subgroupOf B
  let E := D.subgroupOf B
  let : Q.Normal := normal_subgroupOf_of_le_normalizer (le_refl B)
  let : IsCyclic D := hcyc
  let : IsCyclic E := (subgroupOfEquivOfLe hD).isCyclic.mpr hcyc
  have hQE : Q ⊔ E = ⊤ := by
    change (S : Subgroup G).subgroupOf B ⊔ D.subgroupOf B = ⊤
    rw [← subgroupOf_sup (show (S : Subgroup G) ≤ B from
      (S : Subgroup G).le_normalizer) hD, hsup]
    exact subgroupOf_self B
  let q := QuotientGroup.mk' Q
  have hsurj : Function.Surjective (q.comp E.subtype) := by
    intro z
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Q z
    obtain ⟨s, hs, d, hd, rfl⟩ := mem_sup_of_normal_left.mp (hQE ▸ mem_top b)
    refine ⟨⟨d, hd⟩, ?_⟩
    change q d = q (s * d)
    have hs1 : q s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
    rw [map_mul, hs1, one_mul]
  let : IsCyclic (B ⧸ Q) := isCyclic_of_surjective (q.comp E.subtype) hsurj
  let P : Sylow p B := Classical.choice inferInstance
  apply P.primeRank_le_one_of_isCyclic
  apply isCyclic_of_injective (q.comp (P : Subgroup B).subtype)
  apply injective_comp_subtype_of_coprime_ker q _ _ P.isPGroup'
  rw [QuotientGroup.ker_mk']
  have hQp : IsPGroup 2 Q := S.isPGroup'.comap_subtype
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  change Nat.Coprime p (Nat.card Q)
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n

private theorem regular_free {G Ω : Type*} [Group G] [MulAction G Ω]
    (S : Subgroup G) {α β : Ω}
    (heval : Set.BijOn (fun s : S => (s : G) • β) Set.univ {a | a ≠ α})
    (s : S) {a : Ω} (ha : a ≠ α) (hsa : (s : G) • a = a) : s = 1 := by
  obtain ⟨r, _, hr⟩ := heval.surjOn ha
  have hsr : s * r = r := heval.injOn (Set.mem_univ _) (Set.mem_univ _) (by
    simpa only [coe_mul, mul_smul, hr] using hsa)
  exact mul_right_cancel (hsr.trans (one_mul r).symm)

private theorem regular_normalizer_le {G Ω : Type*} [Group G] [MulAction G Ω]
    (S : Subgroup G) {α β : Ω}
    (hN : normalizer (S : Set G) = MulAction.stabilizer G α)
    (heval : Set.BijOn (fun s : S => (s : G) • β) Set.univ {a | a ≠ α})
    (R : Subgroup G) (hR : R ≠ ⊥) (hRS : R ≤ S) :
    normalizer (R : Set G) ≤ normalizer (S : Set G) := by
  intro g hg
  rw [hN, MulAction.mem_stabilizer_iff]
  by_contra hmove
  obtain ⟨r, hr⟩ := ne_bot_iff_exists_ne_one.mp hR
  have hconj : g⁻¹ * (r : G) * g ∈ R := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (R : Set G)).inv_mem hg) (r : G)).mp r.property
  have hfix : (g⁻¹ * (r : G) * g) • α = α :=
    MulAction.mem_stabilizer_iff.mp (hN ▸ S.le_normalizer (hRS hconj))
  have hfix' : (r : G) • (g • α) = g • α := by
    have := congrArg (fun a => g • a) hfix
    simpa only [mul_smul, smul_inv_smul] using this
  have h1 := regular_free S heval ⟨r, hRS r.property⟩ hmove hfix'
  have hrG : (r : G) = 1 := congrArg (fun s : S => (s : G)) h1
  exact hr (Subtype.ext hrG)

private theorem twoLocalPrimeRank_le_one_of_regular_borel
    {Ω : Type*} [MulAction G Ω]
    (S : Sylow 2 G) {α β : Ω}
    (hN : normalizer (S : Set G) = MulAction.stabilizer G α)
    (heval : Set.BijOn (fun s : S => (s : G) • β) Set.univ {a | a ≠ α})
    (D : Subgroup G) (hD : D ≤ normalizer (S : Set G)) (hcyc : IsCyclic D)
    (hsup : (S : Subgroup G) ⊔ D = normalizer (S : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    twoLocalPrimeRank p G ≤ 1 := by
  apply (twoLocalPrimeRank_le_iff p 1).mpr
  rintro M ⟨R, hR, hRp, rfl⟩
  obtain ⟨T, hRT⟩ := hRp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let e := MulAut.conj g
  have hmap : (T : Subgroup G).map e.toMonoidHom = (S : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have hle : (normalizer (R.map e.toMonoidHom : Set G)) ≤ normalizer (S : Set G) :=
    regular_normalizer_le (S : Subgroup G) hN heval _
      (fun h => hR ((map_eq_bot_iff_of_injective R e.injective).mp h))
      ((map_mono hRT).trans_eq hmap)
  have hle' : (normalizer (R : Set G)).map e.toMonoidHom ≤
      normalizer (S : Set G) := by
    rwa [map_equiv_normalizer_eq]
  rw [primeRank_equiv p
    (equivMapOfInjective (normalizer (R : Set G)) e.toMonoidHom e.injective)]
  exact (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hle')
    (inclusion_injective hle')).trans (cyclic_supplement_rank S D hD hcyc hsup p hp ho)

private theorem three_ne_zero_of_binary_card
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hcard : Nat.card F = 2 ^ n) :
    (3 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  change (↑(3 : ℕ) : F) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff F 2]
  norm_num

private theorem standard_psu_local_threeRank_le_one
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    twoLocalPrimeRank p (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1 := by
  obtain ⟨rho, α, S, ⟨D, hD, _, hcyc, _, hsup⟩, hproper, hsolv, hinj,
    hnatural, hScard, hN, hregular, htwo⟩ :=
    CFSG.Quasithin.ChapterF.Source.Unitary.standard_psu_borel_data
      J n hn hcard hconj hstandard
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let Ω := unitaryIsotropicPoints J
  let U := ProjectiveSpecialUnitaryMatrixGroup J
  let : MulAction U Ω := MulAction.compHom Ω rho
  let : FaithfulSMul U Ω := ⟨fun {_ _} h => hinj (Equiv.ext h)⟩
  have hN' : normalizer ((S : Subgroup U) : Set U) = MulAction.stabilizer U α := hN
  obtain ⟨g, hg⟩ : ∃ g : U,
      g ∉ normalizer ((S : Subgroup U) : Set U) := by
    by_contra! h
    exact hproper.ne (eq_top_iff.mpr fun g _ => h g)
  let β : Ω := g • α
  have hβ : β ≠ α := by
    intro h
    apply hg
    rw [hN']
    exact h
  have heval : Set.BijOn (fun s : S => (s : U) • β)
      Set.univ {a | a ≠ α} := by
    have hmap : ∀ s : S, (s : U) • β ≠ α := by
      intro s
      have hsα : (s : U) • α = α := MulAction.mem_stabilizer_iff.mp
        (hN' ▸ (S : Subgroup U).le_normalizer s.property)
      rw [← hsα]
      exact (MulAction.injective (s : U)).ne hβ
    refine ⟨fun s _ => hmap s, ?_, ?_⟩
    · intro s _ r _ h
      exact ExistsUnique.unique (hregular β ((r : U) • β) hβ (hmap r)) h rfl
    · intro a ha
      obtain ⟨s, hs, _⟩ := hregular β a hβ ha
      exact ⟨s, Set.mem_univ _, hs⟩
  exact twoLocalPrimeRank_le_one_of_regular_borel S hN' heval D hD hcyc hsup hp ho

private theorem standard_psu_normalizer_control
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    : ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      ∀ R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), R ≠ ⊥ → R ≤ S →
        normalizer (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
          normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨rho, α, S, ⟨D, hD, _, hcyc, _, hsup⟩, hproper, hsolv, hinj,
    hnatural, hScard, hN, hregular, htwo⟩ :=
    CFSG.Quasithin.ChapterF.Source.Unitary.standard_psu_borel_data
      J n hn hcard hconj hstandard
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let Ω := unitaryIsotropicPoints J
  let U := ProjectiveSpecialUnitaryMatrixGroup J
  let : MulAction U Ω := MulAction.compHom Ω rho
  let : FaithfulSMul U Ω := ⟨fun {_ _} h => hinj (Equiv.ext h)⟩
  have hN' : normalizer ((S : Subgroup U) : Set U) = MulAction.stabilizer U α := hN
  obtain ⟨g, hg⟩ : ∃ g : U,
      g ∉ normalizer ((S : Subgroup U) : Set U) := by
    by_contra! h
    exact hproper.ne (eq_top_iff.mpr fun g _ => h g)
  let β : Ω := g • α
  have hβ : β ≠ α := by
    intro h
    apply hg
    rw [hN']
    exact h
  have heval : Set.BijOn (fun s : S => (s : U) • β)
      Set.univ {a | a ≠ α} := by
    have hmap : ∀ s : S, (s : U) • β ≠ α := by
      intro s
      have hsα : (s : U) • α = α := MulAction.mem_stabilizer_iff.mp
        (hN' ▸ (S : Subgroup U).le_normalizer s.property)
      rw [← hsα]
      exact (MulAction.injective (s : U)).ne hβ
    refine ⟨fun s _ => hmap s, ?_, ?_⟩
    · intro s _ r _ h
      exact ExistsUnique.unique (hregular β ((r : U) • β) hβ (hmap r)) h rfl
    · intro a ha
      obtain ⟨s, hs, _⟩ := hregular β a hβ ha
      exact ⟨s, Set.mem_univ _, hs⟩
  exact ⟨S, regular_normalizer_le (S : Subgroup U) hN' heval⟩

/- The special-unitary root Borel is retained as an actual normalizer.  This
   is the rank-one witness used when the scalar kernel is present. -/
theorem unitary_binary_root_normalizer_primeRank_le_one
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (normalizer (suRoot J hstandard : Set J.specialSubgroup)) ≤ 1 := by
  obtain ⟨_, _, S, hSR, _, _, _, hNB, _, _, _, _, hcyc, _, _⟩ :=
    CFSG.Quasithin.ChapterF.Source.Unitary.standard_su_borel_data
      J n hn hcard hconj hstandard
  let D := suTorus J hstandard
  have hN : normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup) =
      normalizer (suRoot J hstandard : Set J.specialSubgroup) := by
    exact congrArg (fun H : Subgroup J.specialSubgroup =>
      Subgroup.normalizer (H : Set J.specialSubgroup)) hSR
  have hD : D ≤ normalizer (suRoot J hstandard : Set J.specialSubgroup) := by
    rw [hNB]
    exact le_sup_right
  have hsup : (S : Subgroup J.specialSubgroup) ⊔ D =
      normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup) := by
    rw [hN, hNB, hSR]
  rw [← hN]
  have hD' : D ≤ normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup) := by
    rw [hN]
    exact hD
  exact cyclic_supplement_rank S D hD' hcyc hsup p hp ho

/-- The cyclic torus in the actual root normalizer supplies one odd-prime
direction whenever the prime divides `2ⁿ+1`.  Together with the preceding
upper bound this identifies the rank of this concrete normalizer exactly. -/
theorem unitary_binary_root_normalizer_primeRank_eq_one
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {s : ℕ} (hs : s.Prime) (hodd : Odd s) (hdiv : s ∣ 2 ^ n + 1) :
    primeRank s (normalizer (suRoot J hstandard : Set J.specialSubgroup)) = 1 := by
  have hle := unitary_binary_root_normalizer_primeRank_le_one J n hn hcard hconj
    hstandard hs hodd
  let : Fact s.Prime := ⟨hs⟩
  obtain ⟨_, _, S, hSR, _, _, hRcard, hNB, _, _, _, _, hcyc, hDcard, _⟩ :=
    CFSG.Quasithin.ChapterF.Source.Unitary.standard_su_borel_data
      J n hn hcard hconj hstandard
  let D := suTorus J hstandard
  have hD : D ≤ normalizer (suRoot J hstandard : Set J.specialSubgroup) := by
    rw [hNB]
    exact le_sup_right
  let q : ℕ := 2 ^ n
  have hq : 1 ≤ q := by
    dsimp [q]
    exact Nat.one_le_pow n 2 (by decide)
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hqq : q ≤ q * q := by
      have h := Nat.mul_le_mul_left q hq
      simpa using h
    rw [pow_two]
    calc
      q * q - 1 = (q * q - q) + (q - 1) := by omega
      _ = (q - 1) * q + (q - 1) := by rw [Nat.sub_mul]; simp only [one_mul]
      _ = (q - 1) * (q + 1) := by ring
  have hdiv : s ∣ Nat.card D := by
    rw [hDcard]
    rw [show (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) by
      simpa only [q] using hfactor]
    exact dvd_mul_of_dvd_right hdiv _
  have hrD : 1 ≤ primeRank s D := by
    have hne : primeRank s D ≠ 0 := by
      intro hz
      apply PrimeRank.eq_zero_iff_not_dvd_card.mp hz
      exact hdiv
    exact Nat.one_le_iff_ne_zero.mpr hne
  have hrN : 1 ≤ primeRank s
      (normalizer (suRoot J hstandard : Set J.specialSubgroup)) :=
    hrD.trans (Theory.GroupTheory.primeRank_le_of_injective s
      (inclusion hD) (inclusion_injective _))
  exact le_antisymm hle hrN

/-- Every odd-prime ordinary rank of a binary PSL₃ model is at most two. -/
theorem linear_odd_primeRank_le_two {n p : ℕ} (hp : p.Prime) (ho : Odd p)
    (h : ClassicalGroup.IsPSL G 3 (2 ^ n)) : primeRank p G ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  by_cases h3 : p = 3
  · subst p
    rw [primeRank_equiv 3 e]
    exact Matrix.ProjectiveDimensionThree.psl_primeRank_three_le_two
      (three_ne_zero_of_binary_card hcard)
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow
      (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  rw [primeRank_equiv p e]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.projective_linear_odd_prime_rank_le_two h3
      (Theory.SpecificGroups.Classical.cast_ne_zero_of_odd_prime_char_two ho)

/-- Every odd-prime ordinary rank of a binary PSU₃ model is at most two. -/
theorem unitary_odd_primeRank_le_two {n p : ℕ} (hp : p.Prime) (ho : Odd p)
    (h : ClassicalGroup.IsPSU G 3 (2 ^ n)) : primeRank p G ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup J => e.symm x)
      e.symm.injective
  by_cases h3 : p = 3
  · subst p
    rw [primeRank_equiv 3 e]
    exact Matrix.ProjectiveDimensionThree.psu_primeRank_three_le_two
      (three_ne_zero_of_binary_card (n := n * 2) (by
        simpa only [pow_mul, Nat.mul_comm] using hcard)) J
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow
      (by simpa only [← Nat.card_eq_fintype_card] using
        (show Nat.card F = 2 ^ (n * 2) by
          simpa only [pow_mul, Nat.mul_comm] using hcard))
  rw [primeRank_equiv p e]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.projective_unitary_odd_prime_rank_le_two J h3
      (Theory.SpecificGroups.Classical.cast_ne_zero_of_odd_prime_char_two ho)

/-- The cubic-centre linear cover has exact three-rank at the even binary
parameter. -/
theorem linear_special_threeRank_eq_two {n : ℕ} (hn : Even n)
    (h : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ n ∧ Nonempty (G ≃* SL(3,F))) : primeRank 3 G = 2 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  rw [primeRank_equiv 3 e]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.binary_linear_special_threeRank_eq_two hcard hn

/-- The cubic-centre unitary cover has exact three-rank at odd binary
parameter, with the coefficient field and Frobenius map retained. -/
theorem unitary_special_threeRank_eq_two {n : ℕ} (hnpos : 0 < n) (hn : Odd n)
    (h : IsSpecialUnitaryModel G 3 (2 ^ n)) : primeRank 3 G = 2 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  rw [primeRank_equiv 3 e]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.binary_unitary_special_threeRank_eq_two J hnpos hcard hconj hn

/-- In the binary unitary family every odd-prime two-local has rank at most
one.  The proof uses the actual cyclic torus complement in the normalizer of
a nontrivial Sylow two-subgroup. -/
theorem unitary_binary_twoLocalPrimeRank_le_one {n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (ho : Odd p)
    (h : ClassicalGroup.IsPSU G 3 (2 ^ n)) : twoLocalPrimeRank p G ≤ 1 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  obtain ⟨C, hC⟩ := CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport.exists_standard_basis
    J n hn hcard hconj
  let J₀ := CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport.standardForm J
  let ep := e.trans (CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport.projectiveEquiv
    J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective ep ep.surjective
  rw [twoLocalPrimeRank_mulEquiv p ep]
  exact standard_psu_local_threeRank_le_one J₀ n hn hcard hconj rfl hp ho

/-- An odd prime `s > 3` dividing `2ⁿ+1` gives the two independent
torus directions in the actual binary SU₃ cover. -/
theorem unitary_binary_special_primeRank_ge_two {n s : ℕ} (hn : 0 < n)
    (hs : s.Prime) (hdiv : s ∣ 2 ^ n + 1)
    (h : IsSpecialUnitaryModel G 3 (2 ^ n)) :
    2 ≤ primeRank s G := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  rw [primeRank_equiv s e]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.binary_unitary_special_primeRank_ge_two
    J hn hs hdiv hcard hconj

private theorem all_sylow_normalizer_control
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hS : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ S →
      normalizer (R : Set G) ≤ normalizer (S : Set G))
    (T : Sylow 2 G) (R : Subgroup G) (hR : R ≠ ⊥) (hRT : R ≤ T) :
    normalizer (R : Set G) ≤ normalizer (T : Set G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let e := MulAut.conj g
  have hmap : (T : Subgroup G).map e.toMonoidHom = (S : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have h := hS (R.map e.toMonoidHom)
    (fun he => hR ((map_eq_bot_iff_of_injective R e.injective).mp he))
    ((map_mono hRT).trans_eq hmap)
  change normalizer ((R.map e.toMonoidHom : Subgroup G) : Set G) ≤
    normalizer ((S : Subgroup G) : Set G) at h
  rw [← map_equiv_normalizer_eq, ← hmap, ← map_equiv_normalizer_eq] at h
  exact (map_le_map_iff_of_injective e.injective).mp h

private theorem sylow_normalizer_rank_le_of_one
    {G : Type*} [Group G] [Finite G] (p b : ℕ) (S T : Sylow 2 G)
    (hS : primeRank p (normalizer (S : Set G)) ≤ b) :
    primeRank p (normalizer (T : Set G)) ≤ b := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  let e := MulAut.conj g
  have hmap : (S : Subgroup G).map e.toMonoidHom = (T : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have hN := map_equiv_normalizer_eq (S : Subgroup G) e
  rw [hmap] at hN
  change primeRank p (normalizer ((T : Subgroup G) : Set G)) ≤ b
  rw [← hN, ← Theory.GroupTheory.primeRank_equiv p
    (equivMapOfInjective (normalizer ((S : Subgroup G) : Set G)) e.toMonoidHom e.injective)]
  exact hS

private theorem local_rank_of_central_odd_projection
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (hodd : Odd (Nat.card f.ker))
    (hc : ∀ (S : Sylow 2 H) (R : Subgroup H), R ≠ ⊥ → R ≤ S →
      normalizer (R : Set H) ≤ normalizer (S : Set H))
    (p b : ℕ) (hr : ∀ S : Sylow 2 G, primeRank p (normalizer (S : Set G)) ≤ b) :
    twoLocalPrimeRank p G ≤ b := by
  apply (twoLocalPrimeRank_le_iff p b).mpr
  rintro M ⟨R, hR, hRp, rfl⟩
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  have hi := injective_comp_subtype_of_coprime_ker f hodd.coprime_two_left R hRp
  have hRmap : R.map f ≠ ⊥ := by
    intro he
    have hle := (map_eq_bot_iff R).mp he
    apply hR
    apply eq_bot_iff.mpr
    intro x hx
    have hh : f (⟨x, hx⟩ : R) = f (1 : R) := (hle hx).trans (map_one f).symm
    have hx1 : (⟨x, hx⟩ : R) = 1 := hi hh
    exact congrArg Subtype.val hx1
  have hN := hc (S.mapSurjective hf) (R.map f) hRmap (map_mono hRS)
  have hNle : normalizer (R : Set G) ≤ normalizer (S : Set G) := by
    rw [← S.normalizer_comap_of_central_kernel f hf hk]
    exact map_le_iff_le_comap.mp ((le_normalizer_map f).trans hN)
  exact (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hNle)
    (inclusion_injective _)).trans (hr S)


private theorem standard_su_local_primeRank_le_one
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    twoLocalPrimeRank p J.specialSubgroup ≤ 1 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨P, hP⟩ := standard_psu_normalizer_control J n hn hcard hconj hstandard
  obtain ⟨_, _, S, hSR, _⟩ := standard_su_borel_data J n hn hcard hconj hstandard
  apply local_rank_of_central_odd_projection (suProjection J) (suProjection_surjective J)
    (suProjection_ker_central J) (suProjection_ker_odd J hstandard n hn hcard)
    (all_sylow_normalizer_control P hP) p 1
  intro T
  apply sylow_normalizer_rank_le_of_one p 1 S T
  change primeRank p (normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup)) ≤ 1
  rw [hSR]
  exact unitary_binary_root_normalizer_primeRank_le_one J n hn hcard hconj hstandard hp ho

/-- Every odd-prime local rank in binary SU₃ is at most one; the scalar
kernel is retained by lifting normalizer control through the central projection. -/
theorem unitary_binary_special_twoLocalPrimeRank_le_one {n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (ho : Odd p)
    (h : IsSpecialUnitaryModel G 3 (2 ^ n)) : twoLocalPrimeRank p G ≤ 1 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let J₀ := FormTransport.standardForm J
  let es := e.trans (FormTransport.specialEquiv J C hC)
  rw [twoLocalPrimeRank_mulEquiv p es]
  exact standard_su_local_primeRank_le_one J₀ n hn hcard hconj rfl hp ho

private theorem normalizer_rank_witness_of_equiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (R : Subgroup H) (hR : R ≠ ⊥) (hRp : IsPGroup 2 R)
    (s r : ℕ) (hr : primeRank s (normalizer (R : Set H)) = r) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      primeRank s (normalizer (Q : Set G)) = r := by
  have hlocal : IsTwoLocal (normalizer (R : Set H)) := ⟨R, hR, hRp, rfl⟩
  obtain ⟨Q, hQ, hQp, hQN⟩ := Theory.GroupTheory.isTwoLocal_map e.symm hlocal
  refine ⟨Q, hQ, hQp, ?_⟩
  rw [← hQN, ← Theory.GroupTheory.primeRank_equiv s
    (equivMapOfInjective (normalizer (R : Set H)) e.symm.toMonoidHom e.symm.injective)]
  exact hr

/-- The binary SU₃ rank-one witness is an actual normalizer of a nontrivial
root two-subgroup, transported to the original model carrier. -/
theorem unitary_binary_special_local_witness {n s : ℕ} (hn : 0 < n)
    (hs : s.Prime) (ho : Odd s) (hdiv : s ∣ 2 ^ n + 1)
    (h : IsSpecialUnitaryModel G 3 (2 ^ n)) :
    ∃ R : Subgroup G, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      primeRank s (normalizer (R : Set G)) = 1 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let J₀ := FormTransport.standardForm J
  let es := e.trans (FormTransport.specialEquiv J C hC)
  obtain ⟨_, _, S, hSR, _, _, hRcard, _⟩ :=
    standard_su_borel_data J₀ n hn hcard hconj rfl
  have hR : suRoot J₀ rfl ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hRcard
    have hp : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
    have hp3 : 1 < (2 ^ n) ^ 3 := Nat.one_lt_pow (by decide) hp
    omega
  have hRp : IsPGroup 2 (suRoot J₀ rfl) := hSR ▸ S.isPGroup'
  exact normalizer_rank_witness_of_equiv es (suRoot J₀ rfl) hR hRp s 1
    (unitary_binary_root_normalizer_primeRank_eq_one J₀ n hn hcard hconj rfl hs ho hdiv)

/-- The norm-one torus and its root normalizer give exact ordinary and local
ranks two and one whenever an odd prime divides q+1. -/
theorem unitary_binary_special_rank_pair {n s : ℕ} (hn : 0 < n)
    (hs : s.Prime) (ho : Odd s) (hdiv : s ∣ 2 ^ n + 1)
    (h : IsSpecialUnitaryModel G 3 (2 ^ n)) :
    primeRank s G = 2 ∧ twoLocalPrimeRank s G = 1 := by
  refine ⟨le_antisymm ?_ (unitary_binary_special_primeRank_ge_two hn hs hdiv h), ?_⟩
  · obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
    let : Fact s.Prime := ⟨hs⟩
    let : CharP F 2 := by
      let := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := n * 2)
        (by simpa only [← Nat.card_eq_fintype_card, pow_mul] using hcard)
    rw [Theory.GroupTheory.primeRank_equiv s e]
    exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.unitary_odd_prime_rank_le_two J
      (Theory.SpecificGroups.Classical.cast_ne_zero_of_odd_prime_char_two ho)
  · apply le_antisymm (unitary_binary_special_twoLocalPrimeRank_le_one hn hs ho h)
    obtain ⟨R, hR, hRp, hr⟩ := unitary_binary_special_local_witness hn hs ho hdiv h
    exact hr.ge.trans ((show IsTwoLocal (normalizer (R : Set G)) from ⟨R, hR, hRp, rfl⟩).primeRank_le s)

/-- The exact local three-rank of the cubic-center binary SU₃ cover. -/
theorem unitary_binary_special_twoLocalThreeRank_eq_one {n : ℕ}
    (hn : 3 ≤ n) (ho : Odd n) (h : IsSpecialUnitaryModel G 3 (2 ^ n)) :
    twoLocalPrimeRank 3 G = 1 := by
  apply (unitary_binary_special_rank_pair (by omega) Nat.prime_three (by decide) ?_ h).2
  have hm := Nat.BinaryTorusParity.two_pow_mod_three n
  rw [Nat.odd_iff.mp ho] at hm
  norm_num at hm
  omega

/-- The actual binary SL₃ cover supplies the local-rank-two source clause. -/
theorem linear_binary_special_twoLocalPrimeRank_eq_two {n : ℕ}
    (hnpos : 0 < n) (hn : Even n)
    (h : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ n ∧ Nonempty (G ≃* SL(3,F))) :
    twoLocalPrimeRank 3 G = 2 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  rw [twoLocalPrimeRank_mulEquiv 3 e]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.binary_linear_twoLocalPrimeRank_eq_two
    hnpos hcard hn

/-- The source product calculation receives an actual ordinary elementary
s²-subgroup and an elementary s-subgroup inside an actual two-local. -/
theorem unitary_binary_special_elementary_witnesses {n s : ℕ} (hn : 0 < n)
    (hs : s.Prime) (hs3 : 3 < s) (hdiv : s ∣ 2 ^ n + 1)
    (h : IsSpecialUnitaryModel G 3 (2 ^ n)) :
    ∃ E R D : Subgroup G,
      IsElementaryAbelian s E ∧ Nat.card E = s ^ 2 ∧
      R ≠ ⊥ ∧ IsPGroup 2 R ∧ IsElementaryAbelian s D ∧ Nat.card D = s ∧
      D ≤ normalizer (R : Set G) := by
  let : Fact s.Prime := ⟨hs⟩
  have ho : Odd s := hs.odd_of_ne_two (by omega)
  have hr := (unitary_binary_special_rank_pair hn hs ho hdiv h).1
  obtain ⟨E, hEe, hEcard⟩ := exists_elementaryAbelian_card_primeRank (G := G) (p := s)
  rw [hr] at hEcard
  obtain ⟨R, hR, hRp, hNr⟩ := unitary_binary_special_local_witness hn hs ho hdiv h
  let N := normalizer (R : Set G)
  obtain ⟨D, hDe, hDcard⟩ := exists_elementaryAbelian_card_primeRank (G := N) (p := s)
  let : IsElementaryAbelian s D := hDe
  refine ⟨E, R, D.map N.subtype, hEe, hEcard, hR, hRp,
    IsElementaryAbelian.map _, ?_, map_subtype_le _⟩
  rw [card_map_of_injective N.subtype_injective, hDcard, hNr, pow_one]

/-- Both cubic ranks of the odd-prime linear cover in source A.2.12(I.i). -/
theorem linear_odd_prime_rank_pair {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmod : p % 3 = 1)
    (h : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = p ∧ Nonempty (G ≃* SL(3,F))) :
    primeRank 3 G = 2 ∧ twoLocalPrimeRank 3 G = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  rw [Theory.GroupTheory.primeRank_equiv 3 e, twoLocalPrimeRank_mulEquiv 3 e]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.odd_prime_linear_rank_pair ho hcard hmod

/-- Both cubic ranks of the odd-prime unitary cover in source A.2.12(I.i). -/
theorem unitary_odd_prime_rank_pair {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmod : p % 3 = 2) (h : IsSpecialUnitaryModel G 3 p) :
    primeRank 3 G = 2 ∧ twoLocalPrimeRank 3 G = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  rw [Theory.GroupTheory.primeRank_equiv 3 e, twoLocalPrimeRank_mulEquiv 3 e]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.odd_prime_unitary_rank_pair
    J ho hcard hconj hmod

/-- The original binary unitary carrier satisfies the exact ordinary and local
cubic-rank clause (I.ii) of A.2.12. -/
theorem unitary_binary_cubic_source {n : ℕ} (hn : 3 ≤ n) (ho : Odd n)
    (h : IsSpecialUnitaryModel G 3 (2 ^ n)) :
    primeRank 3 G = 2 ∧ twoLocalPrimeRank 3 G = 1 :=
  ⟨unitary_special_threeRank_eq_two (by omega) ho h,
    unitary_binary_special_twoLocalThreeRank_eq_one hn ho h⟩

end CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
