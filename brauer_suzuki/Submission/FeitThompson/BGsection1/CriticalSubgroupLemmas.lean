/-
Authors: Tianjiao Nie
-/

module

public import Submission.FeitThompson.BGsection1.Defs
import Mathlib.Data.Nat.Choose.Dvd

open scoped Pointwise commutatorElement

section CriticalSubgroupLemmas

variable {G : Type*} [Group G]

/-- The second term `Z₂(G)` of the upper central series is characteristic. -/
public theorem upperCentralSeries_two_characteristic (G : Type*) [Group G] :
    (Subgroup.upperCentralSeries G 2).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  exact Subgroup.comap_upperCentralSeries (G := G) (H := G) φ 2

/-- Any subgroup of `Z₂(G)` has commutator with `G` contained in `Z(G)`. -/
public theorem commutator_le_center_of_le_upperCentralSeries_two
    (H : Subgroup G) (hH : H ≤ Subgroup.upperCentralSeries G 2) :
    ⁅H, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G := by
  refine Subgroup.commutator_le.2 ?_
  intro x hx y hy
  have hxZ2 : x ∈ Subgroup.upperCentralSeries G 2 := hH hx
  have hxStep : ∀ z : G, x * z * x⁻¹ * z⁻¹ ∈ Subgroup.upperCentralSeries G 1 := by
    exact (Subgroup.mem_upperCentralSeries_succ_iff (G := G) (n := 1) (x := x)).1 hxZ2
  have hxy : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.upperCentralSeries G 1 := hxStep y
  simpa [Subgroup.upperCentralSeries_one, commutatorElement_def] using hxy

/-- Any subgroup of `Z₂(G)` satisfies `⁅H,G⁆ ≤ centerIn(H)`. -/
public theorem commutator_le_centerIn_of_le_upperCentralSeries_two
    (H : Subgroup G) [H.Normal] (hH : H ≤ Subgroup.upperCentralSeries G 2) :
    ⁅H, (⊤ : Subgroup G)⁆ ≤ centerIn (G := G) H := by
  intro x hx
  refine ⟨(Subgroup.commutator_le_left (H₁ := H) (H₂ := (⊤ : Subgroup G)) hx), ?_⟩
  exact Subgroup.center_le_centralizer (H : Set G)
    ((commutator_le_center_of_le_upperCentralSeries_two (G := G) H hH) hx)

/-- Convert an ambient commutator containment `⁅H,G⁆ ≤ centerIn(H)` into
`commutator(H) ≤ center(H)` for the subgroup `H`. -/
public theorem subgroup_commutator_le_center_of_commutator_le_centerIn
    (H : Subgroup G)
    (hcomm : ⁅H, (⊤ : Subgroup G)⁆ ≤ centerIn (G := G) H) :
    _root_.commutator (↥H) ≤ Subgroup.center (↥H) := by
  have hcommHH : ⁅H, H⁆ ≤ centerIn (G := G) H :=
    (Subgroup.commutator_mono (le_rfl : H ≤ H) (show H ≤ (⊤ : Subgroup G) by simp)).trans hcomm
  intro x hx
  have hx_map : H.subtype x ∈ (_root_.commutator (↥H)).map H.subtype :=
    Subgroup.mem_map_of_mem H.subtype hx
  have hxHH : H.subtype x ∈ ⁅H, H⁆ := by
    simpa using ((Subgroup.map_subtype_commutator (H := H)).symm ▸ hx_map)
  have hx_centH : H.subtype x ∈ centerIn (G := G) H := hcommHH hxHH
  have hx_centralizer : (x : G) ∈ Subgroup.centralizer (H : Set G) := hx_centH.2
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simpa using
    (Subgroup.mem_centralizer_iff (g := (x : G)) (s := (H : Set G))).1 hx_centralizer
      (y : G) y.property

/-- If `⁅H,G⁆ ≤ centerIn(H)`, then `H` has nilpotency class at most `2`. -/
public theorem nilpotencyClassLe_two_of_commutator_le_centerIn
    (H : Subgroup G)
    (hcomm : ⁅H, (⊤ : Subgroup G)⁆ ≤ centerIn (G := G) H) :
    NilpotencyClassLe 2 (↥H) := by
  have hcomm_sub : _root_.commutator (↥H) ≤ Subgroup.center (↥H) :=
    subgroup_commutator_le_center_of_commutator_le_centerIn (G := G) H hcomm
  have hL1_le_center :
      (⊤ : Subgroup (↥H)).lowerCentralSeries 1 ≤ Subgroup.center (↥H) := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact hcomm_sub
  have hL2_bot : (⊤ : Subgroup (↥H)).lowerCentralSeries 2 = ⊥ := by
    simpa [Nat.succ_eq_add_one] using
      (Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup (↥H)) (n := 1) hL1_le_center)
  have hnil : Group.IsNilpotent (↥H) :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↥H)).2 ⟨2, hL2_bot⟩
  letI : Group.IsNilpotent (↥H) := hnil
  have hclass : Group.nilpotencyClass (↥H) ≤ 2 :=
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := ↥H)).1 hL2_bot
  unfold NilpotencyClassLe
  exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := ↥H)).2 hclass

/-- Any subgroup of `Z₂(G)` has nilpotency class at most `2`. -/
public theorem nilpotencyClassLe_two_of_le_upperCentralSeries_two
    (H : Subgroup G) [H.Normal] (hH : H ≤ Subgroup.upperCentralSeries G 2) :
    NilpotencyClassLe 2 (↥H) :=
  nilpotencyClassLe_two_of_commutator_le_centerIn (G := G) H
    (commutator_le_centerIn_of_le_upperCentralSeries_two (G := G) H hH)

/-- If `H` is characteristic in `G` and `K` is characteristic in `H`, then the image of `K` in
`G` is characteristic. -/
public theorem characteristic_map_subtype_of_characteristic
    (H : Subgroup G) [H.Characteristic] (K : Subgroup H) [K.Characteristic] :
    (K.map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hHmap : H.map φ.toMonoidHom = H :=
    (Subgroup.characteristic_iff_map_eq.mp (inferInstance : H.Characteristic)) φ
  let φH : H ≃* H := (φ.subgroupMap H).trans (MulEquiv.subgroupCongr hHmap)
  have hKmap : K.map φH.toMonoidHom = K :=
    (Subgroup.characteristic_iff_map_eq.mp (inferInstance : K.Characteristic)) φH
  have hcomp :
      φ.toMonoidHom.comp H.subtype = H.subtype.comp φH.toMonoidHom := by
    ext x
    rfl
  calc
    (K.map H.subtype).map φ.toMonoidHom
        = K.map (φ.toMonoidHom.comp H.subtype) := by
            simp [Subgroup.map_map]
    _ = K.map (H.subtype.comp φH.toMonoidHom) := by rw [hcomp]
    _ = (K.map φH.toMonoidHom).map H.subtype := by
          simp [Subgroup.map_map]
    _ = K.map H.subtype := by rw [hKmap]

/-- The subgroup of a subgroup of automorphisms fixing all elements of `G` pointwise is trivial. -/
public theorem fixingSubgroupOf_univ_eq_bot (A : Subgroup (MulAut G)) :
    fixingSubgroupOf A G (Set.univ : Set G) = ⊥ := by
  ext a
  constructor
  · intro ha
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    ext g
    exact (mem_fixingSubgroup_iff (M := A) (s := (Set.univ : Set G))).1 ha g (Set.mem_univ g)
  · intro ha
    rw [Subgroup.mem_bot] at ha
    subst ha
    exact (mem_fixingSubgroup_iff (M := A) (s := (Set.univ : Set G))).2 (by
      intro g hg
      simp)

/-- `p`-group criterion by prime-order elimination:
if every prime-order element of a finite subgroup has order `p`,
then that subgroup is a `p`-group. -/
public theorem isPGroup_of_prime_order_eq_p [Finite G]
    (p : ℕ) [Fact p.Prime] (H : Subgroup G)
    (hprime : ∀ x : H, Nat.Prime (orderOf x) → orderOf x = p) :
    IsPGroup p H := by
  refine (IsPGroup.iff_orderOf (p := p) (G := H)).2 ?_
  intro x
  refine ⟨(Nat.primeFactorsList (orderOf x)).length, ?_⟩
  have h0 : orderOf x ≠ 0 := (Nat.pos_iff_ne_zero.mp (orderOf_pos x))
  exact Nat.eq_prime_pow_of_unique_prime_dvd h0 (by
    intro q hq hqd
    have hqd_card : q ∣ Nat.card (Subgroup.zpowers x) := by
      simpa [Nat.card_zpowers] using hqd
    letI : Fintype (Subgroup.zpowers x) := Fintype.ofFinite (Subgroup.zpowers x)
    have hqd_card' : q ∣ Fintype.card (Subgroup.zpowers x) := by
      simpa [Nat.card_eq_fintype_card] using hqd_card
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨y, hy⟩ :=
      _root_.exists_prime_orderOf_dvd_card (G := Subgroup.zpowers x) q hqd_card'
    have hy' : Nat.Prime (orderOf (y : H)) := by
      simpa [Subgroup.orderOf_coe, hy] using hq
    have hqy : orderOf (y : H) = p := hprime (y : H) hy'
    have hyq' : orderOf (y : H) = q := by
      simpa [Subgroup.orderOf_coe] using hy
    exact hyq'.symm.trans hqy)

section Z2Omega

variable (p : ℕ)

lemma pow_mul_swap_of_relation
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_y : Commute c y) :
    ∀ n : ℕ, y ^ n * x = c ^ n * x * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        y ^ (n + 1) * x = y * (y ^ n * x) := by simp [pow_succ', mul_assoc]
        _ = y * (c ^ n * x * y ^ n) := by rw [pow_mul_swap_of_relation x y c hrel hc_y n]
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

lemma pow_mul_eq_cpow_mul_pow_mul_pow
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_x : Commute c x)
    (hc_y : Commute c y) :
    ∀ n : ℕ, (x * y) ^ n = c ^ (n.choose 2) * x ^ n * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by simp [pow_succ]
        _ = (c ^ (n.choose 2) * x ^ n * y ^ n) * (x * y) := by
              rw [pow_mul_eq_cpow_mul_pow_mul_pow x y c hrel hc_x hc_y n]
        _ = c ^ (n.choose 2) * x ^ n * (y ^ n * x) * y := by simp [mul_assoc]
        _ = c ^ (n.choose 2) * x ^ n * (c ^ n * x * y ^ n) * y := by
              rw [pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = c ^ (n.choose 2) * (x ^ n * c ^ n) * x * y ^ n * y := by simp [mul_assoc]
        _ = c ^ (n.choose 2) * (c ^ n * x ^ n) * x * y ^ n * y := by
              have hcxnn : Commute (c ^ n) (x ^ n) := (hc_x.pow_left n).pow_right n
              rw [hcxnn.symm.eq]
        _ = (c ^ (n.choose 2) * c ^ n) * (x ^ n * x) * (y ^ n * y) := by simp [mul_assoc]
        _ = c ^ ((n + 1).choose 2) * x ^ (n + 1) * y ^ (n + 1) := by
              have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
                simpa [Nat.choose_one_right, Nat.add_comm] using
                  (Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n))
              rw [hchoose, pow_add, pow_succ, pow_succ]

lemma prime_dvd_choose_two [Fact p.Prime] (hpodd : p ≠ 2) : p ∣ p.choose 2 := by
  have hlt : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hpodd)
  exact (Fact.out : Nat.Prime p).dvd_choose_self (k := 2) (by decide) hlt

lemma choose_two_pow_eq_one
    {M : Type*} [Group M] [Fact p.Prime] {c : M}
    (hpodd : p ≠ 2) (hc : c ^ p = 1) : c ^ (p.choose 2) = 1 := by
  rcases prime_dvd_choose_two (p := p) hpodd with ⟨k, hk⟩
  calc
    c ^ (p.choose 2) = c ^ (p * k) := by simp [hk]
    _ = (c ^ p) ^ k := by rw [pow_mul]
    _ = 1 := by simp [hc]

public lemma pth_mul_eq_one_of_class2 [Fact p.Prime]
    (hpodd : p ≠ 2) (x y : G)
    (hxy_center : ⁅y, x⁆ ∈ Subgroup.center G)
    (hx : x ^ p = 1) (hy : y ^ p = 1) :
    (x * y) ^ p = 1 := by
  let c : G := ⁅y, x⁆
  have hc_x : Commute c x := by
    exact (Subgroup.mem_center_iff.mp hxy_center x).symm
  have hc_y : Commute c y := by
    exact (Subgroup.mem_center_iff.mp hxy_center y).symm
  have hrel : y * x = c * x * y := by
    change y * x = ⁅y, x⁆ * x * y
    simp [commutatorElement_def, mul_assoc]
  have hswap := pow_mul_swap_of_relation x y c hrel hc_y p
  have hc_p : c ^ p = 1 := by
    have hx' : x = c ^ p * x := by simpa [hy, mul_assoc] using hswap
    have hx'' := congrArg (fun t => t * x⁻¹) hx'
    exact (by simpa [mul_assoc] using hx''.symm)
  have hpow := pow_mul_eq_cpow_mul_pow_mul_pow x y c hrel hc_x hc_y p
  calc
    (x * y) ^ p = c ^ (p.choose 2) * x ^ p * y ^ p := hpow
    _ = c ^ (p.choose 2) := by simp [hx, hy]
    _ = 1 := choose_two_pow_eq_one (p := p) hpodd hc_p

public lemma pth_pow_eq_one_of_mem_omega₁_upperCentralSeries_two [Fact p.Prime]
    (hpodd : p ≠ 2)
    {x : Subgroup.upperCentralSeries G 2}
    (hx : x ∈ omega₁ (G := ↥(Subgroup.upperCentralSeries G 2)) (p := p)) :
    ((x : G) ^ p = 1) := by
  refine Subgroup.closure_induction
    (k := {z : Subgroup.upperCentralSeries G 2 | z ^ (p ^ 1) = 1})
    (x := x) ?mem ?one ?mul ?inv hx
  · intro z hz
    have hz' : z ^ p = 1 := by simpa [pow_one] using hz
    exact congrArg Subtype.val hz'
  · simp
  · intro z₁ z₂ _hz₁ _hz₂ hz₁ hz₂
    have hcomm_le :
        ⁅Subgroup.upperCentralSeries G 2, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G :=
      commutator_le_center_of_le_upperCentralSeries_two (G := G)
        (Subgroup.upperCentralSeries G 2) le_rfl
    have hcomm_mem : ⁅(z₂ : G), (z₁ : G)⁆ ∈ Subgroup.center G := by
      exact hcomm_le (Subgroup.commutator_mem_commutator z₂.property (by simp))
    simpa using
      (pth_mul_eq_one_of_class2 (G := G) (p := p) hpodd (z₁ : G) (z₂ : G) hcomm_mem hz₁ hz₂)
  · intro z _hz hz
    simpa [inv_pow] using congrArg Inv.inv hz

lemma pth_pow_eq_one_of_mem_z2OmegaCandidate_raw [Fact p.Prime]
    (hpodd : p ≠ 2) {x : G}
    (hx :
      x ∈ (omega₁ (G := ↥(Subgroup.upperCentralSeries G 2)) (p := p)).map
        (Subgroup.upperCentralSeries G 2).subtype) :
    x ^ p = 1 := by
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact pth_pow_eq_one_of_mem_omega₁_upperCentralSeries_two (G := G) (p := p) hpodd hy

/-- Canonical `Z₂`-omega candidate subgroup in `G`. -/
@[expose] public def z2OmegaCandidate : Subgroup G :=
  (omega₁ (G := ↥(Subgroup.upperCentralSeries G 2)) (p := p)).map
    (Subgroup.upperCentralSeries G 2).subtype

/-- Automorphisms of `G` fixing the canonical `Z₂`-omega candidate pointwise. -/
@[expose] public def z2OmegaCandidateFixingSubgroup : Subgroup (MulAut G) :=
  fixingSubgroup (M := MulAut G) (α := G)
    ((z2OmegaCandidate (G := G) p : Subgroup G) : Set G)

section PrimeOrderReduction

variable [Finite G] [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- Prime-order elimination criterion specialized to the fixer of `z2OmegaCandidate`. -/
public theorem isPGroup_z2OmegaCandidateFixingSubgroup_of_primeOrder_eq_p
    (hprime :
      ∀ σ : z2OmegaCandidateFixingSubgroup (G := G) p,
        Nat.Prime (orderOf σ) → orderOf σ = p) :
    IsPGroup p (↥(z2OmegaCandidateFixingSubgroup (G := G) p)) := by
  simpa [z2OmegaCandidateFixingSubgroup] using
    (isPGroup_of_prime_order_eq_p (G := MulAut G) (p := p)
      (H := fixingSubgroup (M := MulAut G) (α := G)
        ((z2OmegaCandidate (G := G) p : Subgroup G) : Set G)) hprime)

omit [Finite G] [Fact (Nat.Prime p)] in
/-- Convert a `q ≠ p` prime-order elimination statement into full prime-order equality to `p`. -/
public theorem prime_order_eq_p_of_prime_ne_p_elimination
    {H : Subgroup G}
    (helim : ∀ x : H, Nat.Prime (orderOf x) → orderOf x ≠ p → x = 1) :
    ∀ x : H, Nat.Prime (orderOf x) → orderOf x = p := by
  intro x hxprime
  by_cases hx : orderOf x = p
  · exact hx
  · have hx1 : x = 1 := helim x hxprime hx
    have horder1 : orderOf x = 1 := by simp [hx1]
    exact (hxprime.ne_one horder1).elim

end PrimeOrderReduction

public theorem z2OmegaCandidate_le_upperCentralSeries_two :
    z2OmegaCandidate (G := G) p ≤ Subgroup.upperCentralSeries G 2 := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact y.property

public theorem z2OmegaCandidate_characteristic :
    (z2OmegaCandidate (G := G) p).Characteristic := by
  let Z2 : Subgroup G := Subgroup.upperCentralSeries G 2
  let Ω : Subgroup Z2 := omega₁ (G := ↥Z2) (p := p)
  have hZ2 : Z2.Characteristic := upperCentralSeries_two_characteristic (G := G)
  have hΩ : Ω.Characteristic := by
    simpa [Ω] using (omega₁_characteristic (G := ↥Z2) (p := p))
  simpa [z2OmegaCandidate, Z2, Ω] using
    (characteristic_map_subtype_of_characteristic (G := G) Z2 Ω)

public theorem z2OmegaCandidate_commutator_le_centerIn :
    ⁅z2OmegaCandidate (G := G) p, (⊤ : Subgroup G)⁆ ≤
      centerIn (G := G) (z2OmegaCandidate (G := G) p) := by
  let H : Subgroup G := z2OmegaCandidate (G := G) p
  have hHle : H ≤ Subgroup.upperCentralSeries G 2 :=
    z2OmegaCandidate_le_upperCentralSeries_two (G := G) p
  have hHchar : H.Characteristic := by
    simpa [H] using (z2OmegaCandidate_characteristic (G := G) p)
  letI : H.Characteristic := hHchar
  letI : H.Normal := inferInstance
  simpa [H] using
    (commutator_le_centerIn_of_le_upperCentralSeries_two (G := G) H hHle)

public theorem z2OmegaCandidate_nilpotencyClassLe_two :
    NilpotencyClassLe 2 (↥(z2OmegaCandidate (G := G) p)) := by
  let H : Subgroup G := z2OmegaCandidate (G := G) p
  have hHle : H ≤ Subgroup.upperCentralSeries G 2 :=
    z2OmegaCandidate_le_upperCentralSeries_two (G := G) p
  have hHchar : H.Characteristic := by
    simpa [H] using (z2OmegaCandidate_characteristic (G := G) p)
  letI : H.Characteristic := hHchar
  letI : H.Normal := inferInstance
  simpa [H] using
    (nilpotencyClassLe_two_of_le_upperCentralSeries_two (G := G) H hHle)

set_option backward.isDefEq.respectTransparency false in
public theorem z2OmegaCandidate_isPGroup [Fact (IsPGroup p G)] :
    IsPGroup p (↥(z2OmegaCandidate (G := G) p)) := by
  let Z2 : Subgroup G := Subgroup.upperCentralSeries G 2
  let Ω : Subgroup Z2 := omega₁ (G := ↥Z2) (p := p)
  have hZ2p : IsPGroup p (↥Z2) := (Fact.out : IsPGroup p G).to_subgroup Z2
  have hΩp : IsPGroup p Ω := hZ2p.to_subgroup Ω
  have hmap : IsPGroup p (↥(Ω.map Z2.subtype)) := IsPGroup.map (p := p) hΩp Z2.subtype
  simpa [z2OmegaCandidate, Z2, Ω] using hmap

set_option backward.isDefEq.respectTransparency false in
public theorem z2OmegaCandidate_exponent_dvd_p_of_odd [Fact p.Prime] (hpodd : p ≠ 2) :
    Monoid.exponent (↥(z2OmegaCandidate (G := G) p)) ∣ p := by
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  simpa [z2OmegaCandidate] using
    (pth_pow_eq_one_of_mem_z2OmegaCandidate_raw (G := G) (p := p) hpodd x.property)

public theorem z2OmegaCandidate_ne_bot [Finite G] [Nontrivial G] [Fact p.Prime]
    [Fact (IsPGroup p G)] :
    z2OmegaCandidate (G := G) p ≠ ⊥ := by
  let Z2 : Subgroup G := Subgroup.upperCentralSeries G 2
  have hcenter_nontriv : Nontrivial (Subgroup.center G) :=
    (Fact.out : IsPGroup p G).center_nontrivial
  have hcenter_ne_bot : Subgroup.center G ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (H := Subgroup.center G)).1 hcenter_nontriv
  have hcenter_le_Z2 : Subgroup.center G ≤ Z2 := by
    simpa [Z2, Subgroup.upperCentralSeries_one] using
      (Subgroup.upperCentralSeries_mono (G := G) (show 1 ≤ 2 by decide))
  have hZ2_ne_bot : Z2 ≠ ⊥ := by
    intro hZ2bot
    have hcenter_bot : Subgroup.center G = ⊥ :=
      le_antisymm (hcenter_le_Z2.trans (by simp [hZ2bot])) bot_le
    exact hcenter_ne_bot hcenter_bot
  have hZ2_nontriv : Nontrivial (↥Z2) :=
    (Subgroup.nontrivial_iff_ne_bot (H := Z2)).2 hZ2_ne_bot
  have hZ2p : IsPGroup p (↥Z2) := (Fact.out : IsPGroup p G).to_subgroup Z2
  rcases (IsPGroup.nontrivial_iff_card (p := p) (G := ↥Z2) (hG := hZ2p)).1 hZ2_nontriv with
    ⟨n, hn, hcard⟩
  have hpdvdZ2 : p ∣ Nat.card (↥Z2) := by
    rw [hcard]
    exact dvd_pow_self p (Nat.ne_of_gt hn)
  simpa [z2OmegaCandidate, Z2] using omega₁_map_subtype_ne_bot (M := Z2) (p := p) hpdvdZ2

public theorem z2OmegaCandidate_nontrivial [Finite G] [Nontrivial G] [Fact p.Prime]
    [Fact (IsPGroup p G)] :
    Nontrivial (↥(z2OmegaCandidate (G := G) p)) :=
  (Subgroup.nontrivial_iff_ne_bot (H := z2OmegaCandidate (G := G) p)).2
    (z2OmegaCandidate_ne_bot (G := G) (p := p))

public theorem p_dvd_exponent_z2OmegaCandidate [Finite G] [Nontrivial G] [Fact p.Prime]
    [Fact (IsPGroup p G)] :
    p ∣ Monoid.exponent (↥(z2OmegaCandidate (G := G) p)) := by
  let H : Subgroup G := z2OmegaCandidate (G := G) p
  have hHp : IsPGroup p (↥H) := by
    simpa [H] using z2OmegaCandidate_isPGroup (G := G) (p := p)
  have hHnontriv : Nontrivial (↥H) := by
    simpa [H] using z2OmegaCandidate_nontrivial (G := G) (p := p)
  rcases (IsPGroup.nontrivial_iff_card (p := p) (G := ↥H) (hG := hHp)).1 hHnontriv with
    ⟨n, hn, hcard⟩
  have hpdvdH : p ∣ Nat.card (↥H) := by
    rw [hcard]
    exact dvd_pow_self p (Nat.ne_of_gt hn)
  letI : Fintype (↥H) := Fintype.ofFinite (↥H)
  have hpdvdHf : p ∣ Fintype.card (↥H) := by
    simpa [Nat.card_eq_fintype_card] using hpdvdH
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥H) p hpdvdHf
  have horder_dvd : orderOf x ∣ Monoid.exponent (↥H) := Monoid.order_dvd_exponent x
  have horder_eq_p : orderOf x = p := by simpa using hx
  have hpdvdExpH : p ∣ Monoid.exponent (↥H) := by
    simpa [horder_eq_p] using horder_dvd
  simpa [H] using hpdvdExpH

public theorem z2OmegaCandidate_exponent_eq_p_of_dvd [Finite G] [Nontrivial G] [Fact p.Prime]
    [Fact (IsPGroup p G)]
    (hexp_dvd : Monoid.exponent (↥(z2OmegaCandidate (G := G) p)) ∣ p) :
    Monoid.exponent (↥(z2OmegaCandidate (G := G) p)) = p := by
  exact Nat.dvd_antisymm hexp_dvd
    (p_dvd_exponent_z2OmegaCandidate (G := G) (p := p))

end Z2Omega

end CriticalSubgroupLemmas
