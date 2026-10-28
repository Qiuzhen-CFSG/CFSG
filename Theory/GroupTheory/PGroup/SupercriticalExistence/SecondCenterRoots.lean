module

public import Theory.GroupTheory.PGroup.PrimeNormalAbelian
public import Theory.GroupTheory.PGroup.SupercriticalExistence.SecondCenterRoots.AbelianAction
public import Theory.GroupTheory.PGroup.SupercriticalExistence.SecondCenterRoots.DerivedRoots

/-!
# Propagating central prime roots from the second center

In a finite odd-prime p-group Q, suppose that every p-th root of one in
the second center is central. Every normal subgroup of exponent dividing
p is then central: a nontrivial image modulo the center would meet the
quotient center, producing a forbidden noncentral root in the second center.

Choose a normal abelian self-centralizing subgroup A. Its first omega Z
is normal, hence central. The abelian automorphism calculation puts the
commutators of X = first omega in Q with A into Z. The three-subgroups lemma
then gives X' ≤ C_Q(A) ≤ A. Thus the prime roots in X' lie in Z and are
central in X. The derived-root exponent theorem shows that X has exponent
dividing p, so the initial normal-subgroup argument makes X central.

This specializes the mechanisms of Aschbacher, *Finite Group Theory*,
Second Edition, (23.15)–(23.16), printed pp.111–112, to the second-center
hypothesis used in (24.9), printed p.114. It proves root propagation without
assuming supercritical existence or a maximal elementary-centralizer theorem.
-/

open Subgroup
open scoped commutatorElement

/-- If all prime roots in the second center are central, every normal
subgroup of exponent dividing p is central. -/
public theorem IsPGroup.normal_exponent_subgroup_le_center_of_second_center
    {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q)
    (hsecond : ∀ x : Q, x ∈ Subgroup.upperCentralSeries Q 2 → x ^ p = 1 → x ∈ center Q)
    (N : Subgroup Q) [N.Normal] (hexp : ∀ x : N, x ^ p = 1) :
    N ≤ center Q := by
  by_contra hn
  obtain ⟨x, hxN, hxZ⟩ := SetLike.not_le_iff_exists.mp hn
  let q : Q →* Q ⧸ center Q := QuotientGroup.mk' (center Q)
  let B := N.map q
  let : Fact (IsPGroup p (Q ⧸ center Q)) := ⟨hQ.to_quotient (center Q)⟩
  let : B.Normal := QuotientGroup.map_normal (center Q) N
  have hqx : q x ≠ 1 := fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h)
  have : Nontrivial B := ⟨⟨q x, mem_map_of_mem q hxN⟩, 1,
    fun h => hqx (congrArg Subtype.val h)⟩
  obtain ⟨z, hzne, hz⟩ := exists_nontrivial_center_mem_normal (p := p) B
  obtain ⟨y, hyN, hyz⟩ := z.property
  have hysecond : y ∈ Subgroup.upperCentralSeries Q 2 := by
    rw [← Subgroup.comap_upperCentralSeries_quotient_center, Subgroup.upperCentralSeries_one]
    change q y ∈ center (Q ⧸ center Q)
    rwa [hyz]
  have hyexp : y ^ p = 1 := congrArg Subtype.val (hexp ⟨y, hyN⟩)
  have hycenter := hsecond y hysecond hyexp
  apply hzne
  apply Subtype.ext
  exact hyz.symm.trans ((QuotientGroup.eq_one_iff y).mpr hycenter)

/-- In a finite odd-prime p-group, centrality of the prime roots in the
second center forces centrality of every prime root in the group. -/
public theorem IsPGroup.prime_roots_central_of_second_center
    {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) (hp : p ≠ 2)
    (hsecond : ∀ x : Q, x ∈ Subgroup.upperCentralSeries Q 2 → x ^ p = 1 → x ∈ center Q) :
    ∀ x : Q, x ^ p = 1 → x ∈ center Q := by
  obtain ⟨A, hAn, hAc, hCA⟩ := hQ.exists_normal_abelian_selfCentralizing
  let : A.Normal := hAn
  let : IsMulCommutative A := hAc
  let Z := (omega₁ A (p := p)).map A.subtype
  let : (omega₁ A (p := p)).Characteristic := omega₁_characteristic A
  let : IsElementaryAbelian p (omega₁ A (p := p)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative A
  let : IsElementaryAbelian p Z := IsElementaryAbelian.map_subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZ : Z ≤ center Q := hQ.normal_exponent_subgroup_le_center_of_second_center hsecond Z
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p Z))
  have hroots (a : Q) (ha : a ∈ A) (hap : a ^ p = 1) : a ∈ center Q := by
    apply hZ
    refine ⟨⟨a, ha⟩, subset_closure ?_, rfl⟩
    change (⟨a, ha⟩ : A) ^ (p ^ 1) = 1
    exact Subtype.ext (by simpa using hap)
  let X := omega₁ Q (p := p)
  let : X.Characteristic := omega₁_characteristic Q
  have hXA : ⁅X, A⁆ ≤ center Q := by
    apply Subgroup.commutator_le.mpr
    intro x hx a ha
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        have hxp : x ^ p = 1 := by simpa using hx
        apply hroots _ (Subgroup.commutator_le_right ⊤ A
          (commutator_mem_commutator (mem_top x) ha))
        exact hQ.commutator_prime_root_of_fixes_abelian_roots hp A x hxp
          (fun b hb hp => (mem_center_iff.mp (hroots b hb hp) x)) a ha
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact (center Q).mul_mem
          ((inferInstance : (center Q).Normal).conj_mem _ ihy x) ihx
    | inv x hx ih =>
        rw [commutatorElement_inv_left, ← commutatorElement_inv]
        simpa only [inv_inv] using
          (inferInstance : (center Q).Normal).conj_mem _ ((center Q).inv_mem ih) x⁻¹
  have hrot : ⁅⁅X, A⁆, X⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hXA.trans (center_le_centralizer _))
  have hderiv : ⁅X, X⁆ ≤ A := by
    apply le_trans (commutator_eq_bot_iff_le_centralizer.mp
      (commutator_commutator_eq_bot_of_rotate hrot (by rwa [commutator_comm A X]))) hCA
  have hXroots (z : X) (hz : z ∈ _root_.commutator X) (hzp : z ^ p = 1) :
      z ∈ center X := by
    have hzmap : (z : Q) ∈ ⁅X, X⁆ := by
      have hm := mem_map_of_mem X.subtype hz
      simpa only [map_subtype_commutator, Subgroup.coe_subtype] using hm
    have hzZ := hroots z (hderiv hzmap) (congrArg Subtype.val hzp)
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hzZ y))
  have hXexp := (hQ.to_subgroup X).exponent_omega_one_dvd_of_derived_prime_roots_central
    hp hXroots
  have hXpow : ∀ x : X, x ^ p = 1 := by
    intro x
    have hxomega : x ∈ omega₁ X (p := p) := by
      have hall : ∀ q : Q, ∀ hq : q ∈ X, (⟨q, hq⟩ : X) ∈ omega₁ X (p := p) := by
        intro q hq
        induction hq using Subgroup.closure_induction with
        | mem q hq =>
            apply subset_closure
            exact Subtype.ext hq
        | one => exact (omega₁ X (p := p)).one_mem
        | mul q r hq hr ihq ihr => exact (omega₁ X (p := p)).mul_mem ihq ihr
        | inv q hq ih => exact (omega₁ X (p := p)).inv_mem ih
      exact hall x x.property
    exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hXexp ⟨x, hxomega⟩)
  have hXZ : X ≤ center Q := hQ.normal_exponent_subgroup_le_center_of_second_center hsecond X hXpow
  intro x hx
  exact hXZ (subset_closure (by simpa using hx))
