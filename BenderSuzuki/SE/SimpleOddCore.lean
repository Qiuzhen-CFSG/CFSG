module

public import BenderSuzuki.SE.Final
public import BenderSuzuki.SE.Borel

/-!
# Odd cores of strongly embedded subgroups in simple groups

A strongly embedded subgroup of a finite simple group has trivial odd core.
Bender–Suzuki identifies it as a Borel subgroup in a simple Bender model,
whose normal Sylow two-subgroup acts regularly on the non-base cosets.
The odd core commutes with that Sylow subgroup. Coprime orders and regularity
force each odd-core element to fix all cosets; simplicity and properness
make the coset kernel trivial.

Consequently the normalizer of an odd-order subgroup cannot be strongly
embedded: the subgroup is normal in its normalizer, hence trivial, making
the normalizer the whole group.

Source: Bender–Suzuki Theorem SE, as proved in `SE.Final`, and the checked
Borel model actions in `SE.Borel`.
-/

namespace BenderSuzuki

open PFchapter1section1

private theorem fixes_of_regular_coprime
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {P : Subgroup G} (hP : IsPGroup 2 P) {S : Set Ω}
    (hreg : IsRegularOn P S)
    {x : G} (hcomm : ∀ y : P, Commute x (y : G))
    {n : ℕ} (hcop : Nat.Coprime 2 n) (hpow : x ^ n = 1)
    {a : Ω} (ha : a ∈ S) (hxa : x • a ∈ S) : x • a = a := by
  obtain ⟨y, hy, _⟩ := hreg ha hxa
  have hpows : ∀ k : ℕ, (y : G) ^ k • a = x ^ k • a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        (y : G) ^ (k + 1) • a = (y : G) ^ k • ((y : G) • a) := by
          rw [pow_succ, mul_smul]
        _ = (y : G) ^ k • (x • a) := by rw [hy]
        _ = x • ((y : G) ^ k • a) := by
          rw [← mul_smul, ← (hcomm y).pow_right k, mul_smul]
        _ = x ^ (k + 1) • a := by rw [ih, ← mul_smul, pow_succ']
  have hypow : (y : G) ^ n • a = a := by rw [hpows n, hpow, one_smul]
  obtain ⟨z, _, hz⟩ := hreg ha ha
  have hyn : y ^ n = 1 := (hz (y ^ n) hypow).trans (hz 1 (by simp)).symm
  have hyone : y = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (hP.orderOf_coprime hcop y) dvd_rfl
      (orderOf_dvd_of_pow_eq_one hyn)
  simpa [hyone] using hy.symm

private theorem core_eq_bot_of_regular
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (B : Subgroup G) (hB : B ≠ ⊤)
    (P : Sylow 2 B) (hPn : (P : Subgroup B).Normal)
    (hreg : IsRegularOn ((P : Subgroup B).map B.subtype)
      {a : G ⧸ B | a ≠ QuotientGroup.mk 1}) :
    pPrimeCore 2 B = ⊥ := by
  let O := pPrimeCore 2 B
  let _ := hPn
  have hcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hdis : Disjoint (P : Subgroup B) O :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hk]; exact hcop.pow_left k)
  have hcentral : (P : Subgroup B) ≤ Subgroup.centralizer (O : Set B) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_eq_bot_of_disjoint hdis)
  have hkernel : B.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B.normalCore inferInstance with h | h
    · exact h
    · exact (hB (top_unique (h ▸ B.normalCore_le))).elim
  apply eq_bot_iff.mpr
  intro x hx
  have hfix : ∀ a : G ⧸ B, (x : G) • a = a := by
    intro a
    have hbase : (x : G) • (QuotientGroup.mk 1 : G ⧸ B) = QuotientGroup.mk 1 := by
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simp
    by_cases ha : a = QuotientGroup.mk 1
    · simpa [ha] using hbase
    · refine fixes_of_regular_coprime
        (P.isPGroup'.map B.subtype) hreg (n := Nat.card O) ?_ hcop ?_ ha ?_
      · intro y
        obtain ⟨z, hz, hzy⟩ := y.property
        have hc := hcentral hz x hx
        change (x : G) * (y : G) = (y : G) * (x : G)
        rw [← hzy]
        exact congrArg Subtype.val hc
      · exact congrArg (fun z : O => ((z : B) : G))
          (pow_card_eq_one' (x := (⟨x, hx⟩ : O)))
      · intro heq
        apply ha
        apply (MulAction.injective (x : G))
        exact heq.trans hbase.symm
  have hxkernel : (x : G) ∈ B.normalCore := by
    rw [B.normalCore_eq_ker]
    exact Equiv.Perm.ext hfix
  have hxone : (x : G) = 1 := Subgroup.mem_bot.mp (hkernel ▸ hxkernel)
  exact Subgroup.mem_bot.mpr (Subtype.ext hxone)

/-- A strongly embedded subgroup of a finite simple group has trivial odd core. -/
public theorem IsStronglyEmbedded.pPrimeCore_eq_bot_of_isSimple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {M : Subgroup G} (hM : IsStronglyEmbedded M) :
    pPrimeCore 2 M = ⊥ := by
  have hL : involutionCore G = ⊤ :=
    hM.involutionCore_eq_top_of_isSimple inferInstance
  let eL : involutionCore G ≃* G :=
    (MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv
  have hrank : TwoRankAtLeastTwo (involutionCore G) :=
    twoRankAtLeastTwo_of_mulEquiv eL.symm
      (simpleStronglyEmbeddedRankTwo M inferInstance hM)
  have hSE : TheoremSEBenderConclusion M :=
    (theorem_SE M hM).resolve_left (fun h => h hrank)
  obtain ⟨hmodel, hBorel⟩ :=
    recognition_borel_of_simple_theoremSEBenderConclusion M hM inferInstance hSE
  obtain ⟨P, hPn, hregular⟩ := simpleBender_borel_normalSylow_regular hBorel hmodel
  exact core_eq_bot_of_regular M hM.ne_top P hPn hregular

/-- An odd-order subgroup of a finite simple group cannot have a strongly
embedded normalizer. -/
public theorem not_isStronglyEmbedded_normalizer_of_odd
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (R : Subgroup G) (hR : Odd (Nat.card R)) :
    ¬ IsStronglyEmbedded (Subgroup.normalizer (R : Set G)) := by
  intro hM
  let M := Subgroup.normalizer (R : Set G)
  have hcore : pPrimeCore 2 M = ⊥ := hM.pPrimeCore_eq_bot_of_isSimple
  have hRsub : R.subgroupOf M = ⊥ := by
    apply (pPrimeCore_eq_bot_iff.mp hcore) _ inferInstance
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe R.le_normalizer).toEquiv]
    exact Nat.coprime_two_left.mpr hR
  have hRbot : R = ⊥ := by
    calc
      R = (R.subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le R.le_normalizer).symm
      _ = ⊥ := by rw [hRsub, Subgroup.map_bot]
  apply hM.ne_top
  rw [hRbot]
  exact (⊥ : Subgroup G).normalizer_eq_top

end BenderSuzuki
