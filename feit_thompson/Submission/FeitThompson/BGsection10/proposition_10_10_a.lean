/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.BGsection10.corollary_10_9_b
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem section10_isElementaryAbelian_zpowers_of_pow_eq_one
    {p : ℕ} [Fact p.Prime] {x : G} (hxpow : x ^ p = 1) :
    IsElementaryAbelian p (Subgroup.zpowers x) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro y
  apply Subtype.ext
  have hy_dvd : orderOf ((y : Subgroup.zpowers x) : G) ∣ p := by
    exact (orderOf_dvd_of_mem_zpowers y.2).trans (orderOf_dvd_of_pow_eq_one hxpow)
  simpa using (orderOf_dvd_iff_pow_eq_one.mp hy_dvd)

omit [Finite G] [IsMinCE G] in
public theorem section10_isElementaryAbelian_sup_of_le_centralizer
    {p : ℕ} [Fact p.Prime] {E D : Subgroup G}
    [IsElementaryAbelian p E] [IsElementaryAbelian p D]
    (hDE : D ≤ Subgroup.centralizer (E : Set G)) :
    IsElementaryAbelian p ↥(E ⊔ D) := by
  classical
  let s : Set G := (E : Set G) ∪ (D : Set G)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxC
    · rcases hy with hyE | hyC
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hDE hyC)) x hxE
    · rcases hy with hyE | hyC
      · exact ((Subgroup.mem_centralizer_iff.mp (hDE hxC)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := D)).comm ⟨x, hxC⟩ ⟨y, hyC⟩)
  have hsup : E ⊔ D = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E D)
  refine
    { toIsMulCommutative := by
        letI : CommGroup (Subgroup.closure s) := Subgroup.closureCommGroupOfComm hcomm_s
        rw [hsup]
        exact { is_comm := ⟨fun x y => mul_comm x y⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z hz => z ^ p = 1) (x := (x : G)) (by
        intro y hy
        rcases hy with hyE | hyC
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyC⟩ : D) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p D) ⟨y, hyC⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          letI : CommGroup (Subgroup.closure s) := Subgroup.closureCommGroupOfComm hcomm_s
          show y * z = z * y
          simpa using congrArg Subtype.val
            (mul_comm (⟨y, hy⟩ : Subgroup.closure s) (⟨z, hz⟩ : Subgroup.closure s))
        calc
          (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

omit [IsMinCE G] in
public theorem section10_groupRank_at_least_two_of_generatorRank_subgroup
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 2 ≤ generatorRank A) :
    2 ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    letI : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : 2 ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section10_generatorRank_le_natCard_pre B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hAgen⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section10_primeRank_le_natCard_pre (q := r) K)
  · exact ⟨q, hq, hqrankK⟩

public theorem section10_rankTwoMaximal_subgroupPrimeSet_eq_singleton
    {p : Nat.Primes} {A : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G) :
    subgroupPrimeSet A = ({p} : Set Nat.Primes) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hAp : IsPGroup p.val A := by
    letI : IsElementaryAbelian p.val A := hA.1.2
    exact IsElementaryAbelian.isPGroup p.val A
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hcard_one : Nat.card A = 1 := (Subgroup.card_eq_one (H := A)).2 hbot
    have hp2_ne_one : p.val ^ 2 ≠ 1 := by
      intro hp2
      have hp_dvd_one : p.val ∣ 1 := by
        rw [← hp2]
        simp [pow_two]
      exact p.property.not_dvd_one hp_dvd_one
    exact hp2_ne_one (hA.1.1.symm.trans hcard_one)
  simpa using
    section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
      (G := G) (p := p.val) hAp hAne

public theorem section10_rankTwoMaximal_hypothesis7_1
    {p : Nat.Primes} {A : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G) :
    Hypothesis7_1 A := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  letI : IsElementaryAbelian p.val A := hA.1.2
  letI : IsMulCommutative A := hA.1.2.toIsMulCommutative
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  have hpG : p.val ∣ Nat.card G := by
    have hpA : p.val ∣ Nat.card A := by
      rw [hA.1.1]
      simp [pow_two]
    exact hpA.trans (Subgroup.card_subgroup_dvd_card A)
  have hAeq :
      (A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p.val = 1} := by
    ext x
    constructor
    · intro hxA
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hyA
        exact Subgroup.mul_comm_of_mem_isMulCommutative (H := A) hyA hxA
      · let xA : A := ⟨x, hxA⟩
        have hxpow : xA ^ p.val = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p.val A) xA
        simpa [xA] using congrArg Subtype.val hxpow
    · rintro ⟨hxCent, hxpow⟩
      let C : Subgroup G := Subgroup.zpowers x
      have hCelem : IsElementaryAbelian p.val C :=
        section10_isElementaryAbelian_zpowers_of_pow_eq_one (G := G) (p := p.val) hxpow
      letI : IsElementaryAbelian p.val C := hCelem
      have hCA : C ≤ Subgroup.centralizer (A : Set G) := by
        intro y hy
        rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hcomm : Commute a x :=
          Subgroup.mem_centralizer_iff.mp hxCent a ha
        exact (hcomm.zpow_right n).eq
      have hsupElem : IsElementaryAbelian p.val ↥(A ⊔ C) :=
        section10_isElementaryAbelian_sup_of_le_centralizer (G := G) (p := p.val)
          (E := A) (D := C) hCA
      have hAeqSup : A = A ⊔ C := hA.2.2 (A ⊔ C) le_sup_left hsupElem
      have hxC : x ∈ C := Subgroup.mem_zpowers x
      have hxSup : x ∈ A ⊔ C := Subgroup.mem_sup_right hxC
      rw [hAeqSup]
      exact hxSup
  exact proposition_7_5 (G := G) (p := p.val) hpG hAp
    (Or.inl ⟨hAeq, fun X hX => theorem_10_6 (G := G) (H := X) (p := p) hX⟩)

omit [Finite G] [IsMinCE G] in
private theorem section10_mem_section7HFamily_top_conjBy
    {A Q : Subgroup G} {π : Set Nat.Primes} {g : G}
    (hQ : Q ∈ section7HFamily (⊤ : Subgroup G) A π) :
    Q.conjBy g ∈ section7HFamily (⊤ : Subgroup G) (A.conjBy g) π := by
  rcases hQ with ⟨_, hQπ, hAnormQ⟩
  refine ⟨le_top, ?_, ?_⟩
  · intro r hr
    have hcard : Nat.card (Q.conjBy g) = Nat.card Q := by
      simpa [Subgroup.conjBy] using
        Subgroup.card_map_of_injective
          (K := Q) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    exact hQπ r (by simpa [hcard] using hr)
  · refine subgroup_le_normalizer_of_conj_mem (Q.conjBy g) (A.conjBy g) ?_
    intro a x hx
    rcases a.2 with ⟨a0, ha0A, ha_eq⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQ, rfl⟩
    have hy' : a0 * y * a0⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hAnormQ ha0A) y).1 hyQ
    exact Subgroup.mem_map.mpr ⟨a0 * y * a0⁻¹, hy', by
      rw [← ha_eq]
      simp [map_mul, mul_assoc]⟩

omit [Finite G] [IsMinCE G] in
public theorem section10_mem_section7HStarFamily_top_conjBy
    {A Q : Subgroup G} {π : Set Nat.Primes} {g : G}
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) A π) :
    Q.conjBy g ∈ section7HStarFamily (⊤ : Subgroup G) (A.conjBy g) π := by
  refine ⟨section10_mem_section7HFamily_top_conjBy (G := G) (g := g) hQ.1, ?_⟩
  intro R hQR hR
  have hR_back :
      R.conjBy g⁻¹ ∈ section7HFamily (⊤ : Subgroup G) A π := by
    have htmp :=
      section10_mem_section7HFamily_top_conjBy (G := G) (g := g⁻¹) hR
    simpa [section10_conjBy_inv] using htmp
  have hQ_le_back : Q ≤ R.conjBy g⁻¹ := by
    intro x hx
    have hxR : g * x * g⁻¹ ∈ R := by
      exact hQR (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hxR, by simp [mul_assoc]⟩
  have hEq_back : R.conjBy g⁻¹ = Q := hQ.2 _ hQ_le_back hR_back
  calc
    R = (R.conjBy g⁻¹).conjBy g := by
      exact (section10_conjBy_inv' R g).symm
    _ = Q.conjBy g := by simp [hEq_back]

omit [Finite G] [IsMinCE G] in
public theorem section10_sylow_smul_coe_eq_conjBy
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (g : G) :
    ((g • P : Sylow p G) : Subgroup G) = (P : Subgroup G).conjBy g := by
  ext x
  constructor
  · intro hx
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hx
    simpa [Subgroup.conjBy] using hx
  · intro hx
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    simpa [Subgroup.conjBy] using hx

public theorem section10_section7K_le_centralizer (A : Subgroup G) :
    section7K A ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  exact piCoreIn_le _ _ (by simpa [section7K] using hx)

/-- Proposition 10.10(a). -/
public theorem proposition_10_10_a
    {p q : Nat.Primes} (hpq : p ≠ q) {A Q : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) A {q})
    (hqC : q ∈ subgroupPrimeSet (Subgroup.centralizer (A : Set G))) :
    ∃ P : Sylow p.val G, A ≤ (P : Subgroup G) ∧
      Subgroup.normalizer ((P : Subgroup G) : Set G) =
        section10PPrimeCore p (Subgroup.centralizer ((P : Subgroup G) : Set G)) ⊔
          (Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓ Subgroup.normalizer (Q : Set G)) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  letI : IsElementaryAbelian p.val A := hA.1.2
  letI : IsMulCommutative A := hA.1.2.toIsMulCommutative
  letI : CommGroup A := CommGroup.ofIsMulCommutative
  have hHyp : Hypothesis7_1 A := section10_rankTwoMaximal_hypothesis7_1 (G := G) hA
  have hAπ : subgroupPrimeSet A = ({p} : Set Nat.Primes) :=
    section10_rankTwoMaximal_subgroupPrimeSet_eq_singleton (G := G) hA
  have hqA : q ∉ subgroupPrimeSet A := by
    intro hq_mem
    have hqp : q = p := by simpa [hAπ] using hq_mem
    exact hpq hqp.symm
  have hcenterRank : 2 ≤ groupRank (Subgroup.center A) := by
    have htop_le_center : (⊤ : Subgroup A) ≤ Subgroup.center A := by
      intro a _ha
      rw [Subgroup.mem_center_iff]
      intro b
      exact mul_comm b a
    have htop_p : IsPGroup p.val (⊤ : Subgroup A) := by
      letI : IsElementaryAbelian p.val A := hA.1.2
      have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
      simpa using hAp.to_subgroup (⊤ : Subgroup A)
    have htop_comm : IsMulCommutative (⊤ : Subgroup A) := by
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      exact mul_comm (x : A) (y : A)
    have hgen_top : 2 ≤ generatorRank (⊤ : Subgroup A) := by
      letI : IsElementaryAbelian p.val A := hA.1.2
      have hgenA : 2 ≤ generatorRank A :=
        section10_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq_pre
          (p := p.val) (A := A) hA.1.1
      have hgen_eq : generatorRank (⊤ : Subgroup A) = generatorRank A := by
        rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
        exact Group.rank_congr Subgroup.topEquiv
      simpa [hgen_eq] using hgenA
    exact section10_groupRank_at_least_two_of_generatorRank_subgroup
      (G := A) (q := p.val) p.property htop_le_center htop_p htop_comm hgen_top
  have htrans :
      ConjugationActionTransitiveOn (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) :=
    theorem_7_3 (G := G) hHyp hqA hcenterRank hqC
  have hAp : IsPGroup p.val A := by
    letI : IsElementaryAbelian p.val A := hA.1.2
    exact IsElementaryAbelian.isPGroup p.val A
  obtain ⟨P₀, hAP₀⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
  have hP₀proper : (P₀ : Subgroup G) ≠ ⊤ :=
    section10_global_pSubgroup_proper_of_min_ce (G := G) (p := p.val) P₀.isPGroup'
  haveI : Group.IsNilpotent (P₀ : Subgroup G) :=
    IsPGroup.isNilpotent (p := p.val) (G := (P₀ : Subgroup G)) P₀.isPGroup'
  have hAsubnormalP₀ : IsSubnormalIn A (P₀ : Subgroup G) :=
    section8_isSubnormalIn_of_nilpotent (G := G) hAP₀
  have hP₀π : IsPiSubgroup (subgroupPrimeSet A) (P₀ : Subgroup G) := by
    have hsingle : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) (P₀ : Subgroup G) :=
      section8_isPiSubgroup_singleton_of_isPGroup P₀.isPGroup'
    simpa [hAπ] using hsingle
  have hres₀ :=
    theorem_7_4 (G := G) (A := A) (P := (P₀ : Subgroup G))
      hHyp hqA hP₀proper hAsubnormalP₀ hP₀π htrans
  have hbotFam :
      (⊥ : Subgroup G) ∈ section7HFamily (⊤ : Subgroup G) (P₀ : Subgroup G)
        ({q} : Set Nat.Primes) := by
    exact section8_bot_mem_section7HFamily_top (G := G) (P₀ : Subgroup G) ({q} : Set Nat.Primes)
  obtain ⟨Q₀, hQ₀star, _hbot_le_Q₀⟩ :=
    section8_exists_mem_section7HStarFamily_of_mem_family (G := G) hbotFam
  have hQ₀A : Q₀ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    hres₀.2.2.1 hQ₀star
  obtain ⟨k, hkQ⟩ := htrans Q₀ hQ₀A Q hQ
  let P : Sylow p.val G := ((k : G) • P₀ : Sylow p.val G)
  have hPconj : (P : Subgroup G) = (P₀ : Subgroup G).conjBy (k : G) := by
    simpa [P] using section10_sylow_smul_coe_eq_conjBy (G := G) P₀ (k : G)
  have hkCent : (k : G) ∈ Subgroup.centralizer (A : Set G) :=
    section10_section7K_le_centralizer (G := G) A k.property
  have hAP : A ≤ (P : Subgroup G) := by
    intro a ha
    rw [hPconj]
    refine Subgroup.mem_map.mpr ⟨a, hAP₀ ha, ?_⟩
    have hcomm : (k : G) * a = a * (k : G) :=
      (Subgroup.mem_centralizer_iff.mp hkCent a ha).symm
    calc
      (MulAut.conj (k : G)).toMonoidHom a = (k : G) * a * (k : G)⁻¹ := rfl
      _ = a := by
        rw [hcomm]
        simp [mul_assoc]
  have hQPk :
      Q ∈ section7HStarFamily (⊤ : Subgroup G) (P : Subgroup G) ({q} : Set Nat.Primes) := by
    have hQ₀conj :
        Q₀.conjBy (k : G) ∈
          section7HStarFamily (⊤ : Subgroup G) ((P₀ : Subgroup G).conjBy (k : G))
            ({q} : Set Nat.Primes) :=
      section10_mem_section7HStarFamily_top_conjBy (G := G) (g := (k : G)) hQ₀star
    simpa [hkQ, hPconj] using hQ₀conj
  have hPproper : (P : Subgroup G) ≠ ⊤ :=
    section10_global_pSubgroup_proper_of_min_ce (G := G) (p := p.val) P.isPGroup'
  haveI : Group.IsNilpotent (P : Subgroup G) :=
    IsPGroup.isNilpotent (p := p.val) (G := (P : Subgroup G)) P.isPGroup'
  have hAsubnormalP : IsSubnormalIn A (P : Subgroup G) :=
    section8_isSubnormalIn_of_nilpotent (G := G) hAP
  have hPπ : IsPiSubgroup (subgroupPrimeSet A) (P : Subgroup G) := by
    have hsingle : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) (P : Subgroup G) :=
      section8_isPiSubgroup_singleton_of_isPGroup P.isPGroup'
    simpa [hAπ] using hsingle
  have hres :=
    theorem_7_4 (G := G) (A := A) (P := (P : Subgroup G))
      hHyp hqA hPproper hAsubnormalP hPπ htrans
  let Np : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G)
  let Ccore : Subgroup G :=
    section10PPrimeCore p (Subgroup.centralizer ((P : Subgroup G) : Set G))
  let L : Subgroup G := Np ⊓ Subgroup.normalizer (Q : Set G)
  have hfactorSet :
      ((Np : Subgroup G) : Set G) = (Ccore : Set G) * (L : Set G) := by
    have hraw := (hres.2.2.2 Q hQPk).2
    simpa [Np, Ccore, L, section10PPrimeCore, section10PPrimeSet, hAπ] using hraw
  refine ⟨P, hAP, ?_⟩
  apply le_antisymm
  · intro x hx
    have hxset : x ∈ ((Np : Subgroup G) : Set G) := by simpa [Np] using hx
    rw [hfactorSet] at hxset
    rcases Set.mem_mul.mp hxset with ⟨c, hc, l, hl, rfl⟩
    exact (Ccore ⊔ L).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hl)
  · refine sup_le ?_ ?_
    · intro x hx
      have hxC : x ∈ Subgroup.centralizer (((P : Subgroup G) : Set G)) := by
        exact piCoreIn_le _ _ hx
      exact centralizer_le_normalizer (P : Subgroup G) hxC
    · exact inf_le_left
