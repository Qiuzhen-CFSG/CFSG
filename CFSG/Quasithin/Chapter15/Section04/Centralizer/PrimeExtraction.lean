module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SourceCubic.NineLift
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Hall.Existence
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import CFSG.KnownSimple.CarrierCatalogue
public import Mathlib.Algebra.Group.PUnit

/-!
# Prime extraction for 15.4.4--5

In a solvable Hall {2,p}-overgroup of the actual Sylow subgroup, the
two-core quotient has nontrivial p-core. A minimal nonzero Sylow-invariant
subgroup of its central first omega subgroup has order p or p², by lifting
elementary subgroups through the coprime two-core kernel. Its literal
two-residual preimage belongs to lowercase ξ or uppercase Ξ, respectively.

The printed candidate on p.1157 is Ω₁(Z(H/O₂(H))). That expression can be
trivial even for H=S₄. Here the candidate is Ω₁(Z(O_p(H/O₂(H)))), as in the
existing SourceCubic.Omega construction. No invariant elementary complement
in H is assumed. The original source statements are preserved.

The final applications retain precisely earlier 15.4.2(2),(3) and the
maximal-prime conclusions of 15.4.3. Their discharge belongs to
qt-15-04-prime-reduction. Source: Aschbacher--Smith, printed pp.1156--1157.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.PrimeExtraction
open FamilySource LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G] [Finite G]

private theorem elementary_of_le {p : ℕ} {Q : Type*} [Group Q]
    {A P : Subgroup Q} [IsElementaryAbelian p P] (hAP : A ≤ P) :
    IsElementaryAbelian p A where
  toIsMulCommutative := ⟨⟨by
    intro x y
    apply Subtype.ext
    exact congrArg (fun z : P => (z : Q))
      (mul_comm (⟨(x : Q), hAP x.property⟩ : P) (⟨(y : Q), hAP y.property⟩ : P))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    change (x : Q) ^ p = 1
    exact elemPow_eq_one_of_isElementaryAbelian (A := P) (x : Q) (hAP x.property)

private theorem odd_pGroup_perfect {p : ℕ} [Fact p.Prime]
    {Q : Type*} [Group Q] [Finite Q] (P : Subgroup Q)
    (hP : IsPGroup p P) (ho : Odd p) : IsPPerfect 2 P := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  apply (pResidual_eq_top_iff 2 P).mp
  apply top_unique
  intro x _
  apply mem_pResidual_of_orderOf_coprime
  exact (ho.coprime_two_left.pow_right n).of_dvd_right
    (hn ▸ orderOf_dvd_natCard x)

private theorem residual_odd_quotient {p : ℕ} [Fact p.Prime]
    {Q : Type*} [Group Q] [Finite Q]
    (q : G →* Q) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Subgroup Q) (hP : IsPGroup p P) (ho : Odd p) :
    ∃ e : residualPreimage q P ⧸ pCore 2 (residualPreimage q P) ≃* P,
      ∀ x : residualPreimage q P,
        (e (QuotientGroup.mk' (pCore 2 (residualPreimage q P)) x) : Q) = q x := by
  let L := residualPreimage q P
  have him : L.map q = P := residualPreimage_image q hq P (odd_pGroup_perfect P hP ho)
  let f := q.subgroupMap L
  have hf := q.subgroupMap_surjective L
  have hfk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have hpP : IsPGroup p (L.map q) := by rw [him]; exact hP
  have hcore : pCore 2 (L.map q) = ⊥ := by
    have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup (p := 2))
      (hpP.to_subgroup ⊤) ho.coprime_two_left
    simpa using hd
  have hker : f.ker = pCore 2 L := by
    simpa only [hcore, MonoidHom.comap_bot] using f.comap_pCore_of_ker_isPGroup hf hfk
  let e : L ⧸ pCore 2 L ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans (MulEquiv.subgroupCongr him))
  exact ⟨e, fun x => rfl⟩

/-- An odd p-subgroup lifts through the literal two-core quotient, with
the original projection retained on every element. -/
theorem odd_lift_quotient {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H : Subgroup G) (P : Subgroup (CoreQuotient H)) (hP : IsPGroup p P) :
    ∃ e : Chapter1.XiQuotient (lift H P) ≃* P,
      ∀ x : lift H P,
        (e (QuotientGroup.mk' (pCore 2 (lift H P)) x) : CoreQuotient H) =
          quotientMap H ⟨(x : G), lift_le H P x.property⟩ := by
  have hk : IsPGroup 2 (quotientMap H).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']; exact pCore_isPGroup
  obtain ⟨e, he⟩ := residual_odd_quotient (quotientMap H)
    (QuotientGroup.mk'_surjective _) hk P hP ho
  let f := ((residualPreimage (quotientMap H) P).equivMapOfInjective H.subtype H.subtype_injective).symm
  let e' := (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  refine ⟨e', ?_⟩
  intro x
  change (e (QuotientGroup.mk' _ (f x)) : CoreQuotient H) = _
  rw [he]
  congr 1
  apply Subtype.ext
  have hh := congrArg (fun y : lift H P => (y : G)) (f.symm_apply_apply x)
  exact hh

private theorem elementary_lift_frattini {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H : Subgroup G) (P : Subgroup (CoreQuotient H)) [IsElementaryAbelian p P] :
    ∃ e : Chapter1.XiFrattiniQuotient (lift H P) ≃* P,
      ∀ x : lift H P,
        (e (QuotientGroup.mk' (frattini (Chapter1.XiQuotient (lift H P)))
          (QuotientGroup.mk' (pCore 2 (lift H P)) x)) : CoreQuotient H) =
          quotientMap H ⟨(x : G), lift_le H P x.property⟩ := by
  obtain ⟨e, he⟩ := odd_lift_quotient ho H P (IsElementaryAbelian.isPGroup p P)
  let : IsElementaryAbelian p (Chapter1.XiQuotient (lift H P)) :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  let : Fact (IsPGroup p (Chapter1.XiQuotient (lift H P))) :=
    ⟨IsElementaryAbelian.isPGroup p _⟩
  exact ⟨(frattiniQuotientEquivOfIsElementaryAbelian (p := p)).trans e, fun x => he x⟩

private theorem quotient_oddCore_ne_bot {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (H : Subgroup G) (hs : Group.IsSolvable H)
    (hsupport : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = p)
    (hdiv : p ∣ Nat.card H) : pCore p (CoreQuotient H) ≠ ⊥ := by
  let Q := CoreQuotient H
  let : Group.IsSolvable H := hs
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
  have hnot : ¬ p ∣ Nat.card (pCore 2 H) := by
    intro hd
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn] at hd
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two hd)
  have hqd : p ∣ Nat.card Q := by
    change p ∣ (pCore 2 H).index
    have hm : p ∣ Nat.card (pCore 2 H) * (pCore 2 H).index := by
      rw [card_mul_index]; exact hdiv
    exact (hp.dvd_mul.mp hm).resolve_left hnot
  have hqp : ∀ q : ℕ, q.Prime → q ∣ Nat.card Q → q = 2 ∨ q = p := by
    intro q hq hd
    exact hsupport q hq (hd.trans (index_dvd_card (pCore 2 H)))
  intro hpc
  have hf : fittingSubgroup Q = ⊥ := by
    rw [fitting_eq_sup_pCore]
    apply le_bot_iff.mp
    refine iSup_le fun q => ?_
    rcases hqp q.val.val (Nat.prime_of_mem_primeFactors q.val.property)
      (Nat.dvd_of_mem_primeFactors q.val.property) with hq | hq
    · rw [hq, pCore_quotient_pCore_eq_bot]
    · rw [hq, hpc]
  have hc := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
    (inferInstance : Group.IsSolvable Q)
  rw [hf] at hc
  have he : (⊤ : Subgroup Q) = ⊥ := by
    apply le_bot_iff.mp
    intro x _
    apply hc
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]
  have hcard : Nat.card Q = 1 := by
    simpa using congrArg (fun A : Subgroup Q => Nat.card A) he
  exact hp.ne_one (Nat.eq_one_of_dvd_one (hcard ▸ hqd))

private def omegaSection (p : ℕ) (H : Subgroup G) : Subgroup (CoreQuotient H) :=
  ((omega₁ (center (pCore p (CoreQuotient H))) (p := p)).map
    (center (pCore p (CoreQuotient H))).subtype).map (pCore p (CoreQuotient H)).subtype

omit [Finite G] in
private theorem omegaSection_normal (p : ℕ) (H : Subgroup G) : (omegaSection p H).Normal := by
  let : (omega₁ (center (pCore p (CoreQuotient H))) (p := p)).Characteristic :=
    omega₁_characteristic _
  unfold omegaSection
  exact inferInstance

omit [Finite G] in
private theorem omegaSection_elementary (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    IsElementaryAbelian p (omegaSection p H) := by
  let : IsElementaryAbelian p (omega₁ (center (pCore p (CoreQuotient H))) (p := p)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian p ((omega₁ (center (pCore p (CoreQuotient H))) (p := p)).map
      (center (pCore p (CoreQuotient H))).subtype) := IsElementaryAbelian.map_subtype
  exact IsElementaryAbelian.map_subtype

/-- Extraction in the actual solvable {2,p}-overgroup. The elementary
subgroup is chosen in H/O₂(H), not as an invariant complement in H. -/
theorem exists_member_of_two_prime_overgroup (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : H ∈ Chapter1.H G)
    (hs : Group.IsSolvable H) (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hsupport : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = p)
    (hdiv : p ∣ Nat.card H) (hr : primeRank p H ≤ 2) :
    ∃ X : Subgroup G, X ≤ H ∧
      ((X ∈ Xi (T : Subgroup G) ∧ (pCore 2 X).index = p) ∨
       (X ∈ Chapter1.Xi G (T : Subgroup G) ∧ Nat.card (Chapter1.XiQuotient X) = p ^ 2)) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let P := omegaSection p H
  let : P.Normal := omegaSection_normal p H
  let : IsElementaryAbelian p P := omegaSection_elementary p H
  have hPne : P ≠ ⊥ := by
    let C := pCore p (CoreQuotient H)
    let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr
      (quotient_oddCore_ne_bot ho H hs hsupport hdiv)
    intro he
    exact omega_center_ne_bot (G := C) pCore_isPGroup
      ((map_eq_bot_iff_of_injective _ C.subtype_injective).mp he)
  let F : Subgroup (CoreQuotient H) → Prop :=
    fun A => A ≠ ⊥ ∧ image H (T : Subgroup G) ≤ normalizer (A : Set _)
  obtain ⟨A, ⟨hAne, hAN⟩, hAP, hmin⟩ := exists_minimal_subgroup_of_mem_le F P
    ⟨hPne, by rw [normalizer_eq_top]; exact le_top⟩
  let : IsElementaryAbelian p A := elementary_of_le hAP
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
  have hk : Nat.Coprime p (Nat.card (quotientMap H).ker) := by
    rw [quotientMap, QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hm]
    exact ho.coprime_two_left.symm.pow_right m
  have hnle : n ≤ 2 := (IsElementaryAbelian.primeRank_ge_of_coprime_quotient
    (quotientMap H) (QuotientGroup.mk'_surjective _) hk A hn).trans hr
  have hnpos : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    exact hAne (Subgroup.card_eq_one.mp (by simpa only [he, pow_zero] using hn))
  let X := lift H A
  have hXH : X ≤ H := lift_le H A
  have hXN : (T : Subgroup G) ≤ normalizer (X : Set G) := lift_normalized H T hTH A hAN
  have hHX : X ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right⟩
    intro hb
    exact hH (le_bot_iff.mp (hb ▸ pCoreIn_le_pCoreIn_of_sylow T
      (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right) (sup_le hXH hTH)))
  obtain ⟨e₀, _⟩ := odd_lift_quotient ho H A (IsElementaryAbelian.isPGroup p A)
  have hi : (pCore 2 X).index = p ^ n := (Nat.card_congr e₀.toEquiv).trans hn
  refine ⟨X, hXH, ?_⟩
  have hncase : n = 1 ∨ n = 2 := by omega
  rcases hncase with rfl | rfl
  · have hi' : (pCore 2 X).index = p := by simpa using hi
    exact Or.inl ⟨⟨hXN, lift_perfect H A, hHX, hi' ▸ hp, hi' ▸ ho⟩, hi'⟩
  · right
    refine ⟨?_, hi⟩
    let : IsElementaryAbelian p (Chapter1.XiQuotient X) :=
      IsElementaryAbelian.of_surjective e₀.symm.toMonoidHom e₀.symm.surjective
    obtain ⟨e, he⟩ := elementary_lift_frattini ho H A
    refine ⟨lift_perfect H A, hXN, hHX.1, ⟨p, hp, ho, Or.inl ⟨inferInstance, hi⟩⟩, ?_⟩
    intro D hD
    by_cases hDb : D = ⊥
    · exact Or.inl hDb
    right
    let B := (D.map e.toMonoidHom).map A.subtype
    have hBne : B ≠ ⊥ := by
      intro hb
      exact hDb ((map_eq_bot_iff_of_injective _ e.injective).mp
        ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp hb))
    have hBN : image H (T : Subgroup G) ≤ normalizer (B : Set (CoreQuotient H)) := by
      change ((T : Subgroup G).subgroupOf H).map (quotientMap H) ≤ normalizer (B : Set _)
      apply le_normalizer_iff.mpr
      rintro q ⟨t, ht, rfl⟩ b ⟨v, ⟨a, ha, rfl⟩, rfl⟩
      have hm := mem_map_of_mem A.subtype
        (mem_map_of_mem e.toMonoidHom (hD ⟨(t : G), ht⟩ a ha))
      change (e (Chapter1.xiFrattiniAction (T : Subgroup G) X hXN ⟨(t : G), ht⟩ a) :
        CoreQuotient H) ∈ B at hm
      rw [CentralizerWitness.SourceCubic.nine_lift_action_compatible
        (T : Subgroup G) H hTH A hXN e he ⟨(t : G), ht⟩ a] at hm
      exact hm
    have hBA : B = A := hmin B ⟨hBne, hBN⟩ (map_subtype_le _)
    apply D.eq_top_of_card_eq
    calc
      Nat.card D = Nat.card B := ((Subgroup.card_map_of_injective A.subtype_injective).trans
        (Subgroup.card_map_of_injective e.injective)).symm
      _ = Nat.card A := hBA ▸ rfl
      _ = Nat.card (Chapter1.XiFrattiniQuotient X) := (Nat.card_congr e.toEquiv).symm

private theorem two_prime_hall (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hM : M ∈ Chapter1.H G)
    (hs : Group.IsSolvable M) (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card M) :
    ∃ H : Subgroup G, H ≤ M ∧ (T : Subgroup G) ≤ H ∧ H ∈ Chapter1.H G ∧
      Group.IsSolvable H ∧ p ∣ Nat.card H ∧
      (∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = p) := by
  let : Group.IsSolvable M := hs
  let : MulDistribMulAction Unit M := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let π : Set Nat.Primes := {q | q.val = 2 ∨ q.val = p}
  let S := T.subtype hTM
  have hSπ : IsPiSubgroup π (S : Subgroup M) := by
    intro q hq
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    exact Or.inl (Nat.prime_eq_prime_of_dvd_pow q.property Nat.prime_two (hn ▸ hq))
  obtain ⟨B, hB, _, hSB⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hs (by simp) π (S : Subgroup M) hSπ ⟨fun _ _ => Iff.rfl⟩
  let H := B.map M.subtype
  have hHM : H ≤ M := map_subtype_le _
  have hTH : (T : Subgroup G) ≤ H := by
    have hm := map_mono (f := M.subtype) hSB
    simpa only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using hm
  have hH : H ∈ Chapter1.H G := by
    intro hb
    exact hM (le_bot_iff.mp (hb ▸ pCoreIn_le_pCoreIn_of_sylow T hTH hHM))
  have hc : Nat.card H = Nat.card B := card_map_of_injective M.subtype_injective
  have hdp : p ∣ Nat.card B := by
    have hn : ¬ p ∣ B.index := fun hd => hB.p_in_pi_of_p_dvd_index
      ⟨p, hp⟩ hd (Or.inr rfl)
    have hm : p ∣ Nat.card B * B.index := by rw [card_mul_index]; exact hdiv
    exact (hp.dvd_mul.mp hm).resolve_right hn
  refine ⟨H, hHM, hTH, hH, ?_, ?_, ?_⟩
  · exact Group.isSolvable_of_surjective (M.subtype.subgroupMap_surjective B)
  · rw [hc]; exact hdp
  · intro q hq hd
    exact hB.p_in_pi_of_p_dvd_card ⟨q, hq⟩ (hc ▸ hd)

/-- A solvable source overgroup supplies the Hall subgroup internally.
Both source-family alternatives retain the same odd prime divisor. -/
theorem exists_member_of_solvable_overgroup (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hM : M ∈ Chapter1.H G)
    (hs : Group.IsSolvable M) (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hdiv : p ∣ Nat.card M) (hr : primeRank p M ≤ 2) :
    ∃ X : Subgroup G, X ≤ M ∧
      ((X ∈ Xi (T : Subgroup G) ∧ (pCore 2 X).index = p) ∨
       (X ∈ Chapter1.Xi G (T : Subgroup G) ∧ Nat.card (Chapter1.XiQuotient X) = p ^ 2)) := by
  obtain ⟨H, hHM, hTH, hH, hsolv, hd, hsupport⟩ := two_prime_hall T M hTM hM hs p hp hdiv
  have hhr : primeRank p H ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hHM) (inclusion_injective hHM)).trans hr
  obtain ⟨X, hXH, hX⟩ := exists_member_of_two_prime_overgroup T H hTH hH hsolv p hp ho hsupport hd hhr
  exact ⟨X, hXH.trans hHM, hX⟩

/-- The maximality hypothesis is exactly maximality among lowercase ξ,
as in 15.4.3, and finiteness supplies a maximizing member. -/
theorem xi_index_le_five (T : Subgroup G)
    (h43 : ∀ X ∈ Xi T,
      (∀ Y ∈ Xi T, (pCore 2 Y).index ≤ (pCore 2 X).index) →
      3 < (pCore 2 X).index → (pCore 2 X).index = 5)
    {X : Subgroup G} (hX : X ∈ Xi T) : (pCore 2 X).index ≤ 5 := by
  obtain ⟨Y, hY, hmax⟩ := (Xi T).exists_max_image
    (fun A => (pCore 2 A).index) (Xi T).toFinite ⟨X, hX⟩
  have hXY := hmax X hX
  by_cases hlarge : 3 < (pCore 2 Y).index
  · exact (h43 Y hY hmax hlarge) ▸ hXY
  · omega

private theorem quotient_prime_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup q A) (hc : Nat.card A = p ^ 2) : p = q := by
  let : Fact q.Prime := ⟨hq⟩
  have hd : p ∣ Nat.card A := by rw [hc, pow_two]; exact dvd_mul_right p p
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [hn] at hd
  exact Nat.prime_eq_prime_of_dvd_pow hp hq hd

/-- The prime restriction from 15.4.2(3) and the exact maximal-prime
conclusion 15.4.3(4), applied to a genuine solvable H(T) member. -/
theorem prime_divisors_of_solvable_overgroup (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hM : M ∈ Chapter1.H G) (hs : Group.IsSolvable M)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p M ≤ 2)
    (h42 : ∀ X ∈ Chapter1.Xi G (T : Subgroup G),
      IsPGroup 3 (Chapter1.XiQuotient X) ∨ IsPGroup 5 (Chapter1.XiQuotient X))
    (h43 : ∀ X ∈ Xi (T : Subgroup G),
      (∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) →
      3 < (pCore 2 X).index → (pCore 2 X).index = 5) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3 ∨ p = 5 := by
  intro p hp hd
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  have ho := hp.odd_of_ne_two hp2
  obtain ⟨X, _, hX | hX⟩ := exists_member_of_solvable_overgroup T M hTM hM hs p hp ho hd (hr p hp ho)
  · have hle := xi_index_le_five (T : Subgroup G) h43 hX.1
    rw [hX.2] at hle
    have hlo := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  · rcases h42 X hX.1 with h3 | h5
    · exact Or.inr (Or.inl (quotient_prime_eq hp Nat.prime_three h3 hX.2))
    · exact Or.inr (Or.inr (quotient_prime_eq hp (by decide) h5 hX.2))

omit [Finite G] in
private theorem mem_H_of_twoLocal {M : Subgroup G} (hM : IsTwoLocal M) : M ∈ Chapter1.H G := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  have hc := le_pCoreIn_of_normalizes hp Q.le_normalizer le_rfl
  intro hb
  exact hQ (le_bot_iff.mp (hb ▸ hc))

/-- Literal 15.4.4 consumer, retaining the genuine earlier solvability,
uppercase-Ξ restriction and maximal lowercase-ξ prime conclusion. -/
theorem maximal_twoLocal_prime_divisors_of_earlier_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hsolv : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M → Group.IsSolvable M)
    (h42 : ∀ X ∈ Chapter1.Xi G (T : Subgroup G),
      IsPGroup 3 (Chapter1.XiQuotient X) ∨ IsPGroup 5 (Chapter1.XiQuotient X))
    (h43 : ∀ X ∈ Xi (T : Subgroup G),
      (∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) →
      3 < (pCore 2 X).index → (pCore 2 X).index = 5) :
    ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3 ∨ p = 5 := by
  intro M hM hTM
  exact prime_divisors_of_solvable_overgroup T M hTM (mem_H_of_twoLocal hM.1)
    (hsolv M hM hTM) (hG.twoLocal_sqtk hM.1).stronglyQuasithin h42 h43

/-- Literal 15.4.5 consumer. An extracted prime-five ξ-member is maximal
by the preceding bound, so the original 15.4.3(3) noncentrality applies. -/
theorem centralizer_prime_divisors_of_earlier_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (Z : Subgroup G) (hZT : Z ≤ (T : Subgroup G)) (hZne : Z ≠ ⊥)
    (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hsolv : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M → Group.IsSolvable M)
    (h42 : ∀ X ∈ Chapter1.Xi G (T : Subgroup G), ⁅Z, X⁆ ≠ ⊥ ∧
      (IsPGroup 3 (Chapter1.XiQuotient X) ∨ IsPGroup 5 (Chapter1.XiQuotient X)))
    (h43 : ∀ X ∈ Xi (T : Subgroup G),
      (∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) →
      3 < (pCore 2 X).index → (pCore 2 X).index = 5 ∧ ⁅Z, X⁆ ≠ ⊥) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (Z : Set G)) → p = 2 ∨ p = 3 := by
  let C := centralizer (Z : Set G)
  have hZtwo : IsPGroup 2 Z := T.isPGroup'.to_le hZT
  have hZcore := le_pCoreIn_of_normalizes hZtwo (hZT.trans hTC) (Subgroup.centralizer_le_normalizer _)
  have hC : C ∈ Chapter1.H G := fun hb => hZne (le_bot_iff.mp (hb ▸ hZcore))
  have hcore : pCore 2 C ≠ ⊥ := by
    intro hb
    apply hC
    change (pCore 2 C).map C.subtype = ⊥
    rw [hb, Subgroup.map_bot]
  obtain ⟨M, hM, hCM⟩ := Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot C hcore
  have hTM := hTC.trans hCM
  let : Group.IsSolvable M := hsolv M hM hTM
  have hs : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective (inclusion_injective hCM)
  have hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p C ≤ 2 := by
    intro p hp ho
    exact (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hCM)
      (inclusion_injective hCM)).trans ((hG.twoLocal_sqtk hM.1).stronglyQuasithin p hp ho)
  have h43bound : ∀ X ∈ Xi (T : Subgroup G),
      (∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) →
      3 < (pCore 2 X).index → (pCore 2 X).index = 5 := fun X hX hm hl => (h43 X hX hm hl).1
  intro p hp hd
  rcases prime_divisors_of_solvable_overgroup T C hTC hC hs hr
    (fun X hX => (h42 X hX).2) h43bound p hp hd with h2 | h3 | h5
  · exact Or.inl h2
  · exact Or.inr h3
  · subst p
    obtain ⟨X, hXC, hX | hX⟩ := exists_member_of_solvable_overgroup T C hTC hC hs
      5 (by decide) (by decide) hd (hr 5 (by decide) (by decide))
    · have hm : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index := by
        intro Y hY
        rw [hX.2]
        exact xi_index_le_five (T : Subgroup G) h43bound hY
      exact ((h43 X hX.1 hm (by rw [hX.2]; decide)).2
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hXC))).elim
    · exact ((h42 X hX.1).1
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hXC))).elim

end CFSG.Quasithin.Chapter15.Section04.PrimeExtraction
