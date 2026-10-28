module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Mathlib.Data.Nat.Choose.Dvd

/-!
# Odd prime rank one and cyclic Sylow subgroups

A noncyclic finite odd-prime group contains a normal elementary abelian
subgroup of order `p²`. Induct on the group order, factoring out a central
subgroup of order `p`. In the preimage of an elementary subgroup of order
`p²`, the central commutators have exponent `p`; hence the `p`-power map is
a homomorphism. Its kernel has order at least `p²` and contains the desired
normal subgroup. The cyclic quotient case is abelian.

Consequently, bounding every elementary abelian subgroup by `p` forces
cyclic Sylow subgroups. Schreier's generator bound supplies the bridge from
`primeRank p G ≤ 1`, including trivial Sylow subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.2,
printed p. 407. The elementary subgroup proof is adapted from this repository's
`FeitThompson/BGsection3/Remaining.lean` (the private Proposition 3.9 helpers)
and `FeitThompson/BGsection4/lemma_4_5_a.lean`, using only Theory dependencies.
-/

open scoped IsMulCommutative commutatorElement

private theorem oddRankOne_pow_mul_swap_of_relation
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_y : Commute c y) :
    ∀ n : ℕ, y ^ n * x = c ^ n * x * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        y ^ (n + 1) * x = y * (y ^ n * x) := by simp [pow_succ', mul_assoc]
        _ = y * (c ^ n * x * y ^ n) := by
              rw [oddRankOne_pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = y * c ^ n * x * y ^ n := by simp [mul_assoc]
        _ = c ^ n * y * x * y ^ n := by
              have hycn : Commute (c ^ n) y := hc_y.pow_left n
              rw [hycn.eq]
        _ = c ^ n * (y * x) * y ^ n := by simp [mul_assoc]
        _ = c ^ n * (c * x * y) * y ^ n := by rw [hrel]
        _ = (c ^ n * c) * x * (y * y ^ n) := by simp [mul_assoc]
        _ = (c ^ n * c) * x * (y ^ n * y) := by
              have hy_pow_comm : y * y ^ n = y ^ n * y := by
                calc
                  y * y ^ n = y ^ (n + 1) := (pow_succ' y n).symm
                  _ = y ^ n * y := pow_succ y n
              rw [hy_pow_comm]
        _ = c ^ (n + 1) * x * y ^ (n + 1) := by
              simp [pow_succ, mul_assoc]

private theorem oddRankOne_pow_mul_eq_cpow_mul_pow_mul_pow
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_x : Commute c x)
    (hc_y : Commute c y) :
    ∀ n : ℕ, (x * y) ^ n = c ^ (Nat.choose n 2) * x ^ n * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by simp [pow_succ]
        _ = (c ^ (Nat.choose n 2) * x ^ n * y ^ n) * (x * y) := by
              rw [oddRankOne_pow_mul_eq_cpow_mul_pow_mul_pow x y c hrel hc_x hc_y n]
        _ = c ^ (Nat.choose n 2) * x ^ n * (y ^ n * x) * y := by simp [mul_assoc]
        _ = c ^ (Nat.choose n 2) * x ^ n * (c ^ n * x * y ^ n) * y := by
              rw [oddRankOne_pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = c ^ (Nat.choose n 2) * (x ^ n * c ^ n) * x * y ^ n * y := by
              simp [mul_assoc]
        _ = c ^ (Nat.choose n 2) * (c ^ n * x ^ n) * x * y ^ n * y := by
              have hcxnn : Commute (c ^ n) (x ^ n) := (hc_x.pow_left n).pow_right n
              rw [hcxnn.symm.eq]
        _ = (c ^ (Nat.choose n 2) * c ^ n) * (x ^ n * x) * (y ^ n * y) := by
              simp [mul_assoc]
        _ = c ^ (Nat.choose (n + 1) 2) * x ^ (n + 1) * y ^ (n + 1) := by
              have hchoose : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
                simpa [Nat.choose_one_right, Nat.add_comm] using
                  (Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n))
              rw [hchoose, pow_add, pow_succ, pow_succ]

private theorem oddRankOne_prime_dvd_choose_two {p : ℕ} [Fact (Nat.Prime p)]
    (hpodd : p ≠ 2) :
    p ∣ Nat.choose p 2 := by
  have hlt : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hpodd)
  exact Nat.Prime.dvd_choose_self (Fact.out : Nat.Prime p) (k := 2) (by decide) hlt

private theorem oddRankOne_choose_two_pow_eq_one
    {p : ℕ} [Fact (Nat.Prime p)] {M : Type*} [Group M] {c : M}
    (hpodd : p ≠ 2) (hc : c ^ p = 1) :
    c ^ Nat.choose p 2 = 1 := by
  rcases oddRankOne_prime_dvd_choose_two (p := p) hpodd with ⟨k, hk⟩
  calc
    c ^ Nat.choose p 2 = c ^ (p * k) := by simp [hk]
    _ = (c ^ p) ^ k := by rw [pow_mul]
    _ = 1 := by simp [hc]

private theorem oddRankOne_pth_mul_eq_mul_pows_of_class2
    {T : Type*} [Group T] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (hc : _root_.commutator T ≤ Subgroup.center T)
    (hpow : ∀ {x : T}, x ∈ _root_.commutator T → x ^ p = 1) {u v : T} :
    (u * v) ^ p = u ^ p * v ^ p := by
  have hm : ⁅v, u⁆ ∈ _root_.commutator T :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [oddRankOne_pow_mul_eq_cpow_mul_pow_mul_pow u v ⁅v, u⁆
    (by simp [commutatorElement_def, mul_assoc])
    ((Subgroup.mem_center_iff.mp (hc hm) u).symm)
    ((Subgroup.mem_center_iff.mp (hc hm) v).symm)]
  simp [oddRankOne_choose_two_pow_eq_one hpodd (hpow hm)]

private theorem oddRankOne_exists_elementaryAbelian_p2_preimage_case
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact (Nat.Prime p)]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)] (Z : Subgroup R) [Z.Normal]
    (hZ_le_center : Z ≤ Subgroup.center R) (hZcard : Nat.card Z = p ^ 1)
    (Sbar : Subgroup (R ⧸ Z)) [Sbar.Normal] (hSbar_card : Nat.card Sbar = p ^ 2)
    (hSbar_elem : IsElementaryAbelian p Sbar) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  let q : R →* R ⧸ Z := QuotientGroup.mk' Z
  let T : Subgroup R := Sbar.comap q
  have hT_normal : T.Normal := by
    simpa [T, q] using (inferInstance : (Sbar.comap (QuotientGroup.mk' Z)).Normal)
  let : T.Normal := hT_normal
  have hker_le_T : q.ker ≤ T := by
    simpa [T] using (Subgroup.ker_le_comap (f := q) (H := Sbar))
  let ZT : Subgroup T := q.ker.subgroupOf T
  have hZT_card : Nat.card ZT = p ^ 1 := by
    calc
      Nat.card ZT = Nat.card q.ker := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_T).toEquiv
      _ = Nat.card Z := by simp [q, QuotientGroup.ker_mk']
      _ = p ^ 1 := hZcard
  have hT_card : Nat.card T = p ^ 3 := by
    have hquot_card : Nat.card (T ⧸ ZT) = p ^ 2 := by
      simpa [T, ZT, q] using
        (card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective Z)
          (H := Sbar)).trans hSbar_card
    calc
      Nat.card T = Nat.card (T ⧸ ZT) * Nat.card ZT := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := ZT))
      _ = p ^ 2 * p ^ 1 := by rw [hquot_card, hZT_card]
      _ = p ^ 3 := by ring_nf
  let qT : T →* T.map q := q.subgroupMap T
  have hTmap_eq : T.map q = Sbar := by
    simpa [T] using
      (Subgroup.map_comap_eq_self_of_surjective (f := q)
        (h := QuotientGroup.mk'_surjective Z) Sbar)
  have hTmap_comm : IsMulCommutative (T.map q) := by
    rw [hTmap_eq]
    exact hSbar_elem.toIsMulCommutative
  have hder_le_ZT : _root_.commutator T ≤ ZT := by
    let : IsMulCommutative (T.map q) := hTmap_comm
    let : CommGroup ↥qT.range := by infer_instance
    have hquot_comm' : Std.Commutative (· * · : T ⧸ qT.ker → _ → _) := by
      let e : T ⧸ qT.ker ≃* qT.range := QuotientGroup.quotientKerEquivRange qT
      let : CommGroup (T ⧸ qT.ker) := MonoidHom.commGroupOfInjective e.toMonoidHom e.injective
      infer_instance
    have hquot_comm : IsMulCommutative (T ⧸ qT.ker) := ⟨hquot_comm'⟩
    have hder_le_ker : _root_.commutator T ≤ qT.ker := by
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := qT.ker)).1 hquot_comm
    simpa [qT, ZT, Subgroup.ker_subgroupMap] using hder_le_ker
  have hZT_le_centerT : ZT ≤ Subgroup.center T := by
    intro z hz
    have hzZ : ((z : T) : R) ∈ Z := by
      change ((z : T) : R) ∈ q.ker at hz
      simpa [q, QuotientGroup.ker_mk'] using hz
    have hzcenter : ((z : T) : R) ∈ Subgroup.center R := hZ_le_center hzZ
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hzcenter) (t : R)
  let φ : T →* ZT :=
    { toFun := fun x =>
        ⟨x ^ p, by
          let xbar : Sbar := ⟨q x, show q (x : R) ∈ Sbar from x.2⟩
          have hxbar_pow : xbar ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p Sbar) xbar
          have hxpow_one : (qT x) ^ p = 1 := by
            apply Subtype.ext
            simpa [qT] using congrArg Subtype.val hxbar_pow
          have hxker : x ^ p ∈ qT.ker := by
            rw [MonoidHom.mem_ker]
            simpa [MonoidHom.map_pow] using hxpow_one
          simpa [ZT, q, qT, QuotientGroup.ker_mk', Subgroup.ker_subgroupMap] using hxker⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        have hder_pow : ∀ {z : T}, z ∈ _root_.commutator T → z ^ p = 1 := by
          intro z hz
          have hzZT : z ∈ ZT := hder_le_ZT hz
          have : (⟨z, hzZT⟩ : ZT) ^ Nat.card ZT = 1 := by
            simp
          simpa [hZT_card] using congrArg Subtype.val this
        ext
        exact congrArg Subtype.val (oddRankOne_pth_mul_eq_mul_pows_of_class2
          hpodd (hder_le_ZT.trans hZT_le_centerT) hder_pow (u := x) (v := y)) }
  let ΩT : Subgroup T := omega₁ (G := T) (p := p)
  have hOmega_eq_ker : ΩT = φ.ker := by
    apply le_antisymm
    · intro x hx
      change φ x = 1
      refine Subgroup.closure_induction (k := {z : T | z ^ (p ^ 1) = 1}) (x := x) ?_ ?_ ?_ ?_ hx
      · intro z hz
        ext
        have hz' : (z : T) ^ p = 1 := by
          simpa [pow_one] using hz
        simpa [φ] using congrArg Subtype.val hz'
      · simp [φ]
      · intro a b _ _ ha hb
        simp [MonoidHom.map_mul, ha, hb]
      · intro a _ ha
        simp [MonoidHom.map_inv, ha]
    · intro x hx
      refine Subgroup.subset_closure ?_
      change φ x = 1 at hx
      have hxpow : x ^ p = 1 := by
        simpa [φ] using congrArg Subtype.val hx
      simpa [omega₁, omega, pow_one] using hxpow
  have hOmegaT_card_eq_ker : Nat.card ΩT = Nat.card φ.ker := by
    simp [hOmega_eq_ker]
  have hphi_range_le_p : Nat.card φ.range ≤ p ^ 1 := by
    calc
      Nat.card φ.range ≤ Nat.card (⊤ : Subgroup ZT) := Subgroup.card_le_of_le le_top
      _ = Nat.card ZT := by simp
      _ = p ^ 1 := hZT_card
  have hT_card_expr : Nat.card T = Nat.card φ.range * Nat.card φ.ker := by
    have hquot_card : Nat.card (T ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    calc
      Nat.card T = Nat.card (T ⧸ φ.ker) * Nat.card φ.ker := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker))
      _ = Nat.card φ.range * Nat.card φ.ker := by rw [hquot_card]
  have hOmegaT_big : p ^ 2 ≤ Nat.card ΩT := by
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hmul : p ^ 3 ≤ p ^ 1 * Nat.card φ.ker := by
      calc
        p ^ 3 = Nat.card φ.range * Nat.card φ.ker := by rw [← hT_card, hT_card_expr]
        _ ≤ p ^ 1 * Nat.card φ.ker := Nat.mul_le_mul_right _ hphi_range_le_p
    have hcancel : p ^ 2 ≤ Nat.card φ.ker := by
      have hmul' : p * p ^ 2 ≤ p * Nat.card φ.ker := by
        simpa [pow_succ, pow_one, mul_assoc] using hmul
      exact Nat.le_of_mul_le_mul_left hmul' hp_pos
    simpa [hOmegaT_card_eq_ker] using hcancel
  let Ω : Subgroup R := ΩT.map T.subtype
  have hΩ_normal : Ω.Normal := by
    let : ΩT.Characteristic := omega₁_characteristic T
    simpa [Ω] using (inferInstance : (ΩT.map T.subtype).Normal)
  let : Ω.Normal := hΩ_normal
  have hΩ_card_eq : Nat.card Ω = Nat.card ΩT := by
    exact Subgroup.card_map_of_injective (f := T.subtype) Subtype.coe_injective
  have hΩ_p : IsPGroup p Ω := (Fact.out : IsPGroup p R).to_subgroup Ω
  obtain ⟨m, hmΩ⟩ := IsPGroup.iff_card.mp hΩ_p
  have hm_ge_two : 2 ≤ m := by
    have hΩ_big : p ^ 2 ≤ Nat.card Ω := by simpa [hΩ_card_eq] using hOmegaT_big
    have hpow : p ^ 2 ≤ p ^ m := by simpa [hmΩ] using hΩ_big
    exact (Nat.pow_le_pow_iff_right (show 1 < p from (Fact.out : Nat.Prime p).one_lt)).1 hpow
  obtain ⟨K, hK_normal, hK_le_Ω, hKcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p) Ω inferInstance hmΩ 2 hm_ge_two
  let : K.Normal := hK_normal
  have hOmegaT_pow : ∀ x : ΩT, ((x : T) : R) ^ p = 1 := by
    intro x
    have hxker : (x : T) ∈ φ.ker := by simpa [hOmega_eq_ker] using x.2
    have hxpowT : (x : T) ^ p = 1 := by
      change φ (x : T) = 1 at hxker
      simpa [φ] using congrArg Subtype.val hxker
    simpa using congrArg Subtype.val hxpowT
  have hKpow : ∀ y : K, y ^ p = 1 := by
    intro y
    apply Subtype.ext
    change ((y : R) ^ p = 1)
    have hyΩ : (y : R) ∈ Ω := hK_le_Ω y.2
    rcases Subgroup.mem_map.mp hyΩ with ⟨x, hxΩT, hxy⟩
    simpa [← hxy] using hOmegaT_pow ⟨x, hxΩT⟩
  have hKcyc : IsCyclic (K ⧸ Subgroup.center K) :=
    IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq (p := p) (G := K) hKcard
  let : IsCyclic (↥K ⧸ Subgroup.center ↥K) := hKcyc
  let : CommGroup ↥K :=
    commGroupOfCyclicCenterQuotient (QuotientGroup.mk' (Subgroup.center ↥K))
      (QuotientGroup.ker_mk' (Subgroup.center ↥K)).le
  let : IsMulCommutative ↥K :=
    { is_comm := by infer_instance }
  refine ⟨K, hK_normal, hKcard, ?_⟩
  refine {
    toIsMulCommutative := by infer_instance
    exponent_dvd_p := ?_
  }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hKpow

private theorem oddRankOne_exists_elementaryAbelian_p2_cyclic_case {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (Z : Subgroup R) [Z.Normal] (hZ_le_center : Z ≤ Subgroup.center R)
    (hZcard : Nat.card Z = p ^ 1) (hQcyc : IsCyclic (R ⧸ Z)) (hncyc : ¬ IsCyclic R) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  obtain ⟨q0, hq0⟩ := (isCyclic_iff_exists_zpowers_eq_top).1 hQcyc
  obtain ⟨x, hxq0⟩ := Quotient.exists_rep q0
  let q : R →* R ⧸ Z := QuotientGroup.mk' Z
  let C : Subgroup R := Subgroup.zpowers x
  have hxq0' : q x = q0 := by simpa [q] using hxq0
  have hq0x : Subgroup.zpowers (q x) = ⊤ := by
    rw [hxq0']
    exact hq0
  have hCmap_top : C.map q = ⊤ := by
    calc
      C.map q = Subgroup.zpowers (q x) := by
        simp [C, q]
      _ = ⊤ := hq0x
  have hCZ_top : C ⊔ Z = ⊤ := by
    apply (Subgroup.eq_top_iff' (H := C ⊔ Z)).2
    intro r
    have hqr : q r ∈ C.map q := by simp [hCmap_top]
    rcases Subgroup.mem_map.mp hqr with ⟨c, hcC, hqc⟩
    have hker : c⁻¹ * r ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) (x := c⁻¹ * r)).1
      have : (q c)⁻¹ * q r = 1 := by
        simpa using congrArg (fun t => t⁻¹ * q r) hqc
      simpa [q, MonoidHom.map_mul] using this
    exact (Subgroup.mem_sup_of_normal_right).2 ⟨c, hcC, c⁻¹ * r, hker, by simp⟩
  have hZ_not_le_C : ¬ Z ≤ C := by
    intro hZleC
    have hC_top : C = ⊤ := by
      simpa [sup_eq_left.mpr hZleC] using hCZ_top
    exact hncyc <|
      (isCyclic_iff_exists_zpowers_eq_top).2 ⟨x, by simpa [C] using hC_top⟩
  let π : R ⧸ Z →* R ⧸ Subgroup.center R :=
    QuotientGroup.map Z (Subgroup.center R) (MonoidHom.id R) hZ_le_center
  have hπ_surj : Function.Surjective π := by
    intro y
    refine Quotient.inductionOn y ?_
    intro r
    exact ⟨QuotientGroup.mk' Z r, rfl⟩
  have hQcenter_cyc : IsCyclic (R ⧸ Subgroup.center R) :=
    isCyclic_of_surjective π hπ_surj
  let : IsCyclic (R ⧸ Subgroup.center R) := hQcenter_cyc
  let : IsMulCommutative R := isMulCommutative_of_isCyclic_quotient_center_self R
  let C' : Subgroup R := C
  let : C'.Normal := Subgroup.normal_of_isMulCommutative C'
  have hx_ne : x ≠ 1 := by
    intro hx1
    have hCbot : C' = ⊥ := by simp [C', C, hx1]
    have hZ_top : Z = ⊤ := by
      have hCbot' : C = ⊥ := by simpa [C'] using hCbot
      simpa [hCbot'] using hCZ_top
    have hR_card : Nat.card R = p := by simpa [hZ_top] using hZcard
    exact hncyc (isCyclic_of_prime_card (α := R) hR_card)
  have hC_nontriv : Nontrivial C' := by
    have hxC : x ∈ C := Subgroup.mem_zpowers x
    refine ⟨⟨1, ⟨⟨x, by simpa [C'] using hxC⟩, ?_⟩⟩⟩
    intro hEq
    exact hx_ne (Subtype.ext_iff.mp hEq).symm
  have hCp : IsPGroup p C' := (Fact.out : IsPGroup p R).to_subgroup C'
  obtain ⟨mC, hmC⟩ := IsPGroup.iff_card.mp hCp
  have hmC_pos : 0 < mC := by
    by_contra hmC0
    have hmC_eq_zero : mC = 0 := Nat.eq_zero_of_not_pos hmC0
    have hC_card_one : Nat.card C' = 1 := by simpa [hmC_eq_zero] using hmC
    have hC_sub : Subsingleton C' := (Nat.card_eq_one_iff_unique.mp hC_card_one).1
    exact (not_subsingleton_iff_nontrivial.mpr hC_nontriv) hC_sub
  obtain ⟨U, hU_normal, hU_le_C, hUcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p)
      (N := C') inferInstance hmC 1 (Nat.succ_le_of_lt hmC_pos)
  let : U.Normal := hU_normal
  have hU_ne_Z : U ≠ Z := by
    intro hUZ
    exact hZ_not_le_C (hUZ ▸ hU_le_C)
  let Ω : Subgroup R := U ⊔ Z
  let : Ω.Normal := Subgroup.normal_of_isMulCommutative Ω
  have hOmega_pow : ∀ y : Ω, y ^ p = 1 := by
    intro y
    rcases (Subgroup.mem_sup_of_normal_right).1 y.2 with ⟨u, huU, z, hzZ, huz⟩
    have hu_pow : u ^ p = 1 := by
      have : (⟨u, huU⟩ : U) ^ Nat.card U = 1 := by
        simp
      simpa [hUcard] using congrArg Subtype.val this
    have hz_pow : z ^ p = 1 := by
      have : (⟨z, hzZ⟩ : Z) ^ Nat.card Z = 1 := by
        simp
      simpa [hZcard] using congrArg Subtype.val this
    apply Subtype.ext
    change ((y : R) ^ p = 1)
    calc
      (y : R) ^ p = (u * z) ^ p := congrArg (· ^ p) huz.symm
      _ = u ^ p * z ^ p := Commute.mul_pow (mul_comm' u z) p
      _ = 1 := by rw [hu_pow, hz_pow, one_mul]
  have hU_le_Ω : U ≤ Ω := le_sup_left
  have hZ_le_Ω : Z ≤ Ω := le_sup_right
  have hΩ_p : IsPGroup p Ω := (Fact.out : IsPGroup p R).to_subgroup Ω
  obtain ⟨m, hmΩ⟩ := IsPGroup.iff_card.mp hΩ_p
  have hΩ_card_ne_p : Nat.card Ω ≠ p := by
    intro hΩp
    have hU_eq_Ω : U = Ω :=
      Subgroup.eq_of_le_of_card_ge hU_le_Ω (by simp [hUcard, hΩp])
    have hZ_eq_Ω : Z = Ω :=
      Subgroup.eq_of_le_of_card_ge hZ_le_Ω (by simp [hZcard, hΩp])
    exact hU_ne_Z (hU_eq_Ω.trans hZ_eq_Ω.symm)
  have hm_ge_two : 2 ≤ m := by
    have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
    by_contra hm_lt
    have hm_lt_two : m < 2 := lt_of_not_ge hm_lt
    cases m with
    | zero =>
        have hΩ_card_one : Nat.card Ω = 1 := by simpa using hmΩ
        have hp_le_one : p ≤ 1 := by
          have := Subgroup.card_le_of_le hZ_le_Ω
          simpa [hZcard, hΩ_card_one] using this
        exact (not_le_of_gt hp_one_lt) hp_le_one
    | succ m' =>
        cases m' with
        | zero =>
            exact hΩ_card_ne_p (by simpa using hmΩ)
        | succ m'' =>
            exact False.elim (by omega)
  obtain ⟨K, hK_normal, hK_le_Ω, hKcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p) Ω inferInstance hmΩ 2 hm_ge_two
  let : K.Normal := hK_normal
  have hKpow : ∀ y : K, y ^ p = 1 := by
    intro y
    apply Subtype.ext
    simpa using hOmega_pow ⟨(y : R), hK_le_Ω y.2⟩
  have hKcyc : IsCyclic (K ⧸ Subgroup.center K) :=
    IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq (p := p) (G := K) hKcard
  let : IsCyclic (K ⧸ Subgroup.center K) := hKcyc
  let : IsMulCommutative K := isMulCommutative_of_isCyclic_quotient_center_self K
  refine ⟨K, hK_normal, hKcard, ?_⟩
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := ?_
  }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hKpow

universe u

/-- Every noncyclic finite odd-prime group contains a normal elementary
abelian subgroup of order `p²`. -/
public theorem IsPGroup.exists_normal_elementary_prime_sq_of_odd_not_isCyclic
    {R : Type u} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hpodd : p ≠ 2) (hncyc : ¬ IsCyclic R) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  let : Fact (IsPGroup p R) := ⟨hR⟩
  let rec aux {S : Type u} [Group S] [Finite S] [Fact (IsPGroup p S)]
      (hSncyc : ¬ IsCyclic S) :
      ∃ A : Subgroup S, A.Normal ∧ Nat.card A = p ^ 2 ∧ IsElementaryAbelian p A := by
    have hS_nontriv : Nontrivial S := Nontrivial.of_not_isCyclic hSncyc
    have hSp : IsPGroup p S := Fact.out
    obtain ⟨nS, hSpow⟩ := IsPGroup.iff_card.mp hSp
    have hnS_pos : 0 < nS := by
      by_contra hnS
      have hnS0 : nS = 0 := Nat.eq_zero_of_not_pos hnS
      have hS_card_one : Nat.card S = 1 := by simpa [hnS0] using hSpow
      let : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hS_card_one).1
      exact hSncyc (isCyclic_of_subsingleton (α := S))
    obtain ⟨k, hk_pos, hcenter_card⟩ :=
      IsPGroup.card_center_eq_prime_pow (G := S) (p := p) hSpow hnS_pos
    obtain ⟨Z, hZ_normal, hZ_le_center, hZcard⟩ :=
      exists_normal_subgroup_card_pow_of_normal (G := S) (p := p)
        (N := Subgroup.center S) inferInstance hcenter_card 1 (Nat.succ_le_of_lt hk_pos)
    let : Z.Normal := hZ_normal
    by_cases hQcyc : IsCyclic (S ⧸ Z)
    · exact oddRankOne_exists_elementaryAbelian_p2_cyclic_case
        (p := p) Z hZ_le_center hZcard hQcyc hSncyc
    · have hQ_card : Nat.card S = Nat.card (S ⧸ Z) * p := by
        calc
          Nat.card S = Nat.card (S ⧸ Z) * Nat.card Z := by
            simpa using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := S) (s := Z))
          _ = Nat.card (S ⧸ Z) * p := by simp [hZcard]
      have hQ_lt : Nat.card (S ⧸ Z) < Nat.card S := by
        rw [hQ_card]
        simpa [one_mul] using
          (Nat.mul_lt_mul_of_pos_left ((Fact.out : Nat.Prime p).one_lt)
            (Nat.card_pos (α := S ⧸ Z)))
      have hQp : IsPGroup p (S ⧸ Z) := (Fact.out : IsPGroup p S).to_quotient Z
      let : Fact (IsPGroup p (S ⧸ Z)) := ⟨hQp⟩
      obtain ⟨Sbar, hSbar_normal, hSbar_card, hSbar_elem⟩ :=
        aux (S := S ⧸ Z) hQcyc
      let : Sbar.Normal := hSbar_normal
      exact
        oddRankOne_exists_elementaryAbelian_p2_preimage_case
          (R := S) (p := p) hpodd Z hZ_le_center hZcard Sbar hSbar_card hSbar_elem
  termination_by Nat.card S
  decreasing_by
    exact hQ_lt
  exact aux (S := R) hncyc


/-- An elementary abelian subgroup has order at most `p` when ambient
`p`-rank is at most one. This bridge does not require oddness. -/
public theorem IsElementaryAbelian.card_le_prime_of_primeRank_le_one
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hr : primeRank p G ≤ 1) (E : Subgroup G) [IsElementaryAbelian p E] :
    Nat.card E ≤ p := by
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hbound : Group.rank E ≤ 1 :=
    (E.rank_le_primeRank p (IsElementaryAbelian.isPGroup p E)).trans hr
  have hdvd : Nat.card E ∣ p ^ Group.rank E :=
    card_dvd_exponent_pow_rank' E
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E))
  calc
    Nat.card E ≤ p ^ Group.rank E := Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) hdvd
    _ ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hbound
    _ = p := pow_one p

/-- A finite odd-prime group with no elementary abelian subgroup larger
than order `p` is cyclic. -/
public theorem IsPGroup.isCyclic_of_odd_of_elementary_card_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (hp : Odd p)
    (hE : ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E ≤ p) :
    IsCyclic G := by
  by_contra hn
  obtain ⟨E, _, hcard, he⟩ :=
    IsPGroup.exists_normal_elementary_prime_sq_of_odd_not_isCyclic
      hG (by rintro rfl; obtain ⟨k, hk⟩ := hp; omega) hn
  have hle := hE E he
  rw [hcard] at hle
  have hprime := (Fact.out : p.Prime).one_lt
  nlinarith

/-- At an odd prime, bounding every elementary abelian subgroup by `p`
forces every Sylow subgroup to be cyclic, including trivial ones. -/
public theorem Sylow.isCyclic_of_odd_of_elementary_card_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : Odd p)
    (hE : ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E ≤ p) :
    IsCyclic P := by
  apply P.isPGroup'.isCyclic_of_odd_of_elementary_card_le hp
  intro E he
  let : IsElementaryAbelian p E := he
  have h := hE (E.map (P : Subgroup G).subtype) (IsElementaryAbelian.map_subtype)
  rwa [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective] at h

/-- Odd prime rank at most one forces each Sylow subgroup to be cyclic. -/
public theorem Sylow.isCyclic_of_odd_of_primeRank_le_one
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : Odd p) (hr : primeRank p G ≤ 1) : IsCyclic P := by
  apply P.isCyclic_of_odd_of_elementary_card_le hp
  intro E he
  let : IsElementaryAbelian p E := he
  exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E

/-- For an odd prime, prime rank at most one is equivalent to cyclicity
of any chosen Sylow subgroup. -/
public theorem Sylow.primeRank_le_one_iff_isCyclic_of_odd
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : Odd p) : primeRank p G ≤ 1 ↔ IsCyclic P :=
  ⟨P.isCyclic_of_odd_of_primeRank_le_one hp, P.primeRank_le_one_of_isCyclic⟩
