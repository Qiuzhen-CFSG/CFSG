module

public import Stellmacher.Recognition.SuzukiThreeSquareAction
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Centralizers in Suzuki's degree-28 action

If a point swap centralizes a torus element, the centralizer consists of a
small cell `P K` and a large cell `P K t P`, where `P` is its centralizer in
the root group. Uniqueness of the root and Bruhat coordinates gives the order
`8 * |P| * (|P| + 1)`. For the unique torus involution the square-action
fixed point and faithfulness exclude root centralizer orders one and 27;
Lagrange's theorem excludes nine. Thus its root centralizer has order three,
its ambient centralizer has order 96, and its conjugacy class has size 63.

Source: Suzuki (1965), Section II, Lemmas 1–3.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

/-- The root elements centralizing a given torus element. -/
public def rootCentralizer (b : Ω) (k : stabilizer (stabilizer G a) b) : Subgroup Q :=
  (Subgroup.centralizer ({((k : stabilizer G a) : G)} : Set G)).comap
    ((stabilizer G a).subtype.comp Q.subtype)

omit [Q.Normal] in
public theorem mem_rootCentralizer (b : Ω) (k : stabilizer (stabilizer G a) b)
    (q : Q) : q ∈ rootCentralizer b k ↔
      Commute ((k : stabilizer G a) : G) ((q : stabilizer G a) : G) := by
  change ((q : stabilizer G a) : G) ∈ Subgroup.centralizer _ ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

include h

/-- Multiplication supplies unique coordinates in the point stabilizer. -/
public theorem root_torus_bijective (b : Ω) (hb : b ≠ a) :
    Function.Bijective (fun p : Q × stabilizer (stabilizer G a) b =>
      (p.1 : stabilizer G a) * (p.2 : stabilizer G a)) := by
  exact (Subgroup.isComplement_iff_bijective _ _).mp
    (Subgroup.isComplement'_def.mp (h.root_complement b hb))

omit [Q.Normal] h in
/-- A large-cell expression cannot fix the base point. -/
public theorem bruhat_not_mem_stabilizer (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (u : Q) (l : stabilizer (stabilizer G a) b) (v : Q) :
    ((u : stabilizer G a) : G) * ((l : stabilizer G a) : G) * t *
      ((v : stabilizer G a) : G) ∉ stabilizer G a := by
  have hva : ((v : stabilizer G a) : G) • a = a := v.val.property
  have hlb : ((l : stabilizer G a) : G) • b = b := l.property
  have hua : ((u : stabilizer G a) : G) • a = a := u.val.property
  intro he
  change (_ * _ * t * _) • a = a at he
  rw [mul_smul, mul_smul, mul_smul, hva, hta, hlb] at he
  exact hb ((MulAction.injective ((u : stabilizer G a) : G)) (he.trans hua.symm))

/-- A torus element commutes with a small-cell expression exactly when it
commutes with the root coordinate. -/
public theorem commute_root_torus_iff (b : Ω) (hb : b ≠ a)
    (k l : stabilizer (stabilizer G a) b) (u : Q) :
    Commute ((k : stabilizer G a) : G)
      (((u : stabilizer G a) : G) * ((l : stabilizer G a) : G)) ↔
    Commute ((k : stabilizer G a) : G) ((u : stabilizer G a) : G) := by
  let : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  have hkl : Commute ((k : stabilizer G a) : G) ((l : stabilizer G a) : G) :=
    congrArg (fun z : stabilizer (stabilizer G a) b => ((z : stabilizer G a) : G))
      (mul_comm' k l)
  constructor
  · intro he
    have he' := he.mul_right hkl.inv_right
    simpa only [mul_inv_cancel_right] using he'
  · exact fun he => he.mul_right hkl

/-- A torus element fixed by the swap commutes with a large-cell expression
exactly when it commutes with both root coordinates. -/
public theorem commute_bruhat_iff (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b)
    (hkt : Commute ((k : stabilizer G a) : G) t)
    (u : Q) (l : stabilizer (stabilizer G a) b) (v : Q) :
    Commute ((k : stabilizer G a) : G)
      (((u : stabilizer G a) : G) * ((l : stabilizer G a) : G) * t *
        ((v : stabilizer G a) : G)) ↔
      Commute ((k : stabilizer G a) : G) ((u : stabilizer G a) : G) ∧
      Commute ((k : stabilizer G a) : G) ((v : stabilizer G a) : G) := by
  let : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  have hkl : Commute ((k : stabilizer G a) : G) ((l : stabilizer G a) : G) :=
    congrArg (fun z : stabilizer (stabilizer G a) b => ((z : stabilizer G a) : G))
      (mul_comm' k l)
  constructor
  · intro he
    let u' : Q := ⟨k.val * u.val * k.val⁻¹,
      (inferInstance : Q.Normal).conj_mem u.val u.property k.val⟩
    let v' : Q := ⟨k.val * v.val * k.val⁻¹,
      (inferInstance : Q.Normal).conj_mem v.val v.property k.val⟩
    have heq : (u', l, v') = (u, l, v) := by
      apply h.bruhat_injective b hb t hta htb
      change (_ * _ * _) * _ * t * (_ * _ * _) = _
      calc
        _ = ((k : stabilizer G a) : G) * ((u : stabilizer G a) : G) *
            (((k : stabilizer G a) : G)⁻¹ * ((l : stabilizer G a) : G)) *
            (t * ((k : stabilizer G a) : G)) * ((v : stabilizer G a) : G) *
            ((k : stabilizer G a) : G)⁻¹ := by simp only [Subgroup.coe_inv]; group
        _ = ((k : stabilizer G a) : G) *
            (((u : stabilizer G a) : G) * ((l : stabilizer G a) : G) * t *
              ((v : stabilizer G a) : G)) * ((k : stabilizer G a) : G)⁻¹ := by
          rw [hkl.inv_left.eq, ← hkt.eq]
          group
        _ = _ := by rw [he.eq]; group
    have hu : u' = u := congrArg Prod.fst heq
    have hv : v' = v := congrArg (fun p => p.2.2) heq
    constructor
    · have hu' := congrArg (fun q : Q => ((q : stabilizer G a) : G)) hu
      change _ * _ * _⁻¹ = _ at hu'
      exact (mul_inv_eq_iff_eq_mul.mp hu' : _)
    · have hv' := congrArg (fun q : Q => ((q : stabilizer G a) : G)) hv
      change _ * _ * _⁻¹ = _ at hv'
      exact (mul_inv_eq_iff_eq_mul.mp hv' : _)
  · rintro ⟨hu, hv⟩
    exact ((hu.mul_right hkl).mul_right hkt).mul_right hv

/-- The two Bruhat cells give the order of a torus element's centralizer. -/
public theorem centralizer_card_of_commute_swap (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b)
    (hkt : Commute ((k : stabilizer G a) : G) t) :
    Nat.card (Subgroup.centralizer ({((k : stabilizer G a) : G)} : Set G)) =
      8 * Nat.card (rootCentralizer (Q := Q) b k) * (Nat.card (rootCentralizer (Q := Q) b k) + 1) := by
  classical
  let P := rootCentralizer (Q := Q) b k
  let K := stabilizer (stabilizer G a) b
  let C := Subgroup.centralizer ({((k : stabilizer G a) : G)} : Set G)
  let : Finite G := Nat.finite_of_card_ne_zero (by rw [h.group_card]; decide)
  let small : P × K → C := fun p =>
    ⟨((p.1.val : stabilizer G a) : G) * ((p.2 : stabilizer G a) : G), by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact ((h.commute_root_torus_iff b hb k p.2 p.1.val).mpr
        ((mem_rootCentralizer (Q := Q) b k p.1.val).mp p.1.property)).symm.eq⟩
  let large : P × K × P → C := fun p =>
    ⟨((p.1.val : stabilizer G a) : G) * ((p.2.1 : stabilizer G a) : G) * t *
      ((p.2.2.val : stabilizer G a) : G), by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact ((h.commute_bruhat_iff b hb t hta htb k hkt p.1.val p.2.1 p.2.2.val).mpr
        ⟨(mem_rootCentralizer (Q := Q) b k p.1.val).mp p.1.property,
          (mem_rootCentralizer (Q := Q) b k p.2.2.val).mp p.2.2.property⟩).symm.eq⟩
  have hs (p : P × K) : (small p : G) ∈ stabilizer G a :=
    (stabilizer G a).mul_mem p.1.val.val.property p.2.val.property
  have hl (p : P × K × P) : (large p : G) ∉ stabilizer G a :=
    bruhat_not_mem_stabilizer b hb t hta p.1.val p.2.1 p.2.2.val
  have hsmall : Function.Injective small := by
    intro p q he
    have hv : ((p.1.val : stabilizer G a) : G) * ((p.2 : stabilizer G a) : G) =
        ((q.1.val : stabilizer G a) : G) * ((q.2 : stabilizer G a) : G) :=
      congrArg (fun z : C => (z : G)) he
    have he' : (p.1.val, p.2) = (q.1.val, q.2) :=
      (h.root_torus_bijective b hb).injective (a₁ := (p.1.val, p.2))
        (a₂ := (q.1.val, q.2))
      (show (p.1.val : stabilizer G a) * p.2.val = q.1.val.val * q.2.val from
        Subtype.ext hv)
    exact Prod.ext (Subtype.ext (congrArg (fun z : Q × K => z.1) he'))
      (congrArg (fun z : Q × K => z.2) he')
  have hlarge : Function.Injective large := by
    intro p q he
    have he' : (p.1.val, p.2.1, p.2.2.val) = (q.1.val, q.2.1, q.2.2.val) :=
      h.bruhat_injective b hb t hta htb (congrArg Subtype.val he)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he'))
      (Prod.ext (congrArg (fun x => x.2.1) he')
        (Subtype.ext (congrArg (fun x => x.2.2) he')))
  have hf : Function.Bijective (Sum.elim small large) := by
    constructor
    · intro p q he
      cases p with
      | inl p =>
        cases q with
        | inl q => exact congrArg Sum.inl (hsmall he)
        | inr q => exact (hl q (congrArg Subtype.val he ▸ hs p)).elim
      | inr p =>
        cases q with
        | inl q => exact (hl p (congrArg Subtype.val he ▸ hs q)).elim
        | inr q => exact congrArg Sum.inr (hlarge he)
    · intro x
      have hx : Commute ((k : stabilizer G a) : G) (x : G) :=
        (Subgroup.mem_centralizer_singleton_iff.mp x.property).symm
      by_cases hxH : (x : G) ∈ stabilizer G a
      · obtain ⟨⟨u, l⟩, he⟩ := (h.root_torus_bijective b hb).surjective ⟨x, hxH⟩
        have heG : ((u : stabilizer G a) : G) * ((l : stabilizer G a) : G) = (x : G) :=
          congrArg (fun z : stabilizer G a => (z : G)) he
        have hu : u ∈ P := (mem_rootCentralizer (Q := Q) b k u).mpr
          ((h.commute_root_torus_iff b hb k l u).mp (heG.symm ▸ hx))
        exact ⟨Sum.inl (⟨u, hu⟩, l), Subtype.ext heG⟩
      · obtain ⟨u, l, v, he⟩ := h.exists_bruhat b hb t hta htb x hxH
        have huv := (h.commute_bruhat_iff b hb t hta htb k hkt u l v).mp (he ▸ hx)
        exact ⟨Sum.inr (⟨u, (mem_rootCentralizer (Q := Q) b k u).mpr huv.1⟩, l,
          ⟨v, (mem_rootCentralizer (Q := Q) b k v).mpr huv.2⟩), Subtype.ext he.symm⟩
  have hc := (Nat.card_congr (Equiv.ofBijective _ hf)).symm
  rw [Nat.card_sum, Nat.card_prod, Nat.card_prod, Nat.card_prod] at hc
  change Nat.card C = _
  rw [hc, show Nat.card K = 8 from h.twoPoint_card b hb]
  ring

private theorem twoPoint_unique_involution
    [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a) :
    ∃ j : stabilizer (stabilizer G a) b,
      orderOf (j : G) = 2 ∧
        ∀ k : stabilizer (stabilizer G a) b,
          orderOf (k : G) = 2 → k = j := by
  let T := stabilizer (stabilizer G a) b
  let : Finite G := h.finite_group
  let : Finite T := Nat.finite_of_card_ne_zero (by
    rw [h.twoPoint_card b hb]
    decide)
  let : Fintype T := Fintype.ofFinite T
  let : IsCyclic T := h.twoPoint_cyclic b hb
  have htwo : 2 ∣ Fintype.card T := by
    have hc : Nat.card T = 8 := h.twoPoint_card b hb
    rw [Nat.card_eq_fintype_card] at hc
    rw [hc]
    decide
  have hcount : Fintype.card {x : T // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype]
    simpa using (IsCyclic.card_orderOf_eq_totient (α := T) htwo)
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 2 (G := T) (by
    rw [h.twoPoint_card b hb]
    decide)
  have hjG : orderOf (j : G) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hj
  refine ⟨j, hjG, ?_⟩
  intro k hk
  have hkT : orderOf k = 2 := by
    simpa only [Subgroup.orderOf_coe] using hk
  have huniq : ∀ x : {x : T // orderOf x = 2}, x = ⟨j, hj⟩ := by
    intro x
    obtain ⟨x₀, hx₀⟩ := Fintype.card_eq_one_iff.mp hcount
    exact (hx₀ x).trans (hx₀ ⟨j, hj⟩).symm
  exact congrArg Subtype.val (huniq ⟨k, hkT⟩)

/-- The cyclic two-point stabilizer has exactly one involution. -/
public theorem twoPoint_exists_unique_involution [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) :
    ∃ j : stabilizer (stabilizer G a) b,
      orderOf (j : G) = 2 ∧
        ∀ k : stabilizer (stabilizer G a) b,
          orderOf (k : G) = 2 → k = j := by
  exact twoPoint_unique_involution h b hb

/-- The involution in the torus centralizes a nonidentity root element. -/
public theorem exists_root_ne_one_commute_involution [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (j : stabilizer (stabilizer G a) b)
    (hj : orderOf (j : G) = 2) :
    ∃ q : Q, q ≠ 1 ∧ Commute ((j : stabilizer G a) : G) ((q : stabilizer G a) : G) := by
  let K := stabilizer (stabilizer G a) b
  let : Finite G := h.finite_group
  let : IsCyclic K := h.twoPoint_cyclic b hb
  obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have hk8 : orderOf k = 8 := hk.trans (h.twoPoint_card b hb)
  have hk4 : orderOf ((k ^ 4 : K) : G) = 2 := by
    have he : orderOf (k ^ 4) = 2 := by rw [orderOf_pow, hk8]; decide
    simpa only [Subgroup.orderOf_coe] using he
  obtain ⟨j₀, _, huniq⟩ := h.twoPoint_exists_unique_involution b hb
  have he : k ^ 4 = j := (huniq _ hk4).trans (huniq j hj).symm
  obtain ⟨q, hq, hcomm⟩ := h.exists_root_ne_one_commute_square b hb (k ^ 2)
  refine ⟨q, hq, ?_⟩
  have hpow : (((k ^ 2 : K) : stabilizer G a) : G) ^ 2 = ((j : stabilizer G a) : G) := by
    rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← pow_mul]
    exact congrArg (fun z : K => ((z : stabilizer G a) : G)) he
  rwa [hpow] at hcomm

/-- Faithfulness prevents a nonidentity torus element from centralizing all
27 root elements. -/
public theorem rootCentralizer_card_ne_twentySeven [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (k : stabilizer (stabilizer G a) b) (hk : k ≠ 1) :
    Nat.card (rootCentralizer (Q := Q) b k) ≠ 27 := by
  let : Finite G := h.finite_group
  intro hc
  have htop : rootCentralizer (Q := Q) b k = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (hc.trans h.root_card.symm)
  apply hk
  apply h.twoPoint_eq_one_of_centralizes_root b hb k
  intro q
  exact ((mem_rootCentralizer b k q).mp (by rw [htop]; trivial)).eq

/-- The root centralizer of the torus involution has order three. The
alternatives one, nine and twenty-seven are excluded by the square-action
fixed point, Lagrange's theorem and faithfulness, respectively. -/
public theorem rootCentralizer_involution_card [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (hta : t • a = b) (htb : t • b = a)
    (j : stabilizer (stabilizer G a) b) (hj : orderOf (j : G) = 2)
    (hjt : Commute ((j : stabilizer G a) : G) t) :
    Nat.card (rootCentralizer (Q := Q) b j) = 3 := by
  let : Finite G := h.finite_group
  let P := rootCentralizer (Q := Q) b j
  have hd : Nat.card P ∣ 27 := h.root_card ▸ P.card_subgroup_dvd_card
  have hn27 : Nat.card P ≠ 27 := h.rootCentralizer_card_ne_twentySeven b hb j (by
    intro he
    simp [he] at hj)
  have hn1 : Nat.card P ≠ 1 := by
    intro he
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_card _).mpr he
    obtain ⟨q, hq, hqj⟩ := h.exists_root_ne_one_commute_involution b hb j hj
    have hqP : q ∈ P := (mem_rootCentralizer b j q).mpr hqj
    rw [hbot] at hqP
    exact hq hqP
  have hc : 8 * Nat.card P * (Nat.card P + 1) ∣ 6048 := by
    rw [← h.centralizer_card_of_commute_swap b hb t hta htb j hjt, ← h.group_card]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card P ∣ 3 ^ 3 from hd)
  change Nat.card P = 3
  interval_cases n <;> norm_num at he <;> simp_all

/-- The torus involution has centralizer order 96 in the centralizing-swap
branch. This calculation does not require any transfer theorem. -/
public theorem torus_involution_centralizer_card [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (hta : t • a = b) (htb : t • b = a)
    (j : stabilizer (stabilizer G a) b) (hj : orderOf (j : G) = 2)
    (hjt : Commute ((j : stabilizer G a) : G) t) :
    Nat.card (Subgroup.centralizer ({((j : stabilizer G a) : G)} : Set G)) = 96 := by
  rw [h.centralizer_card_of_commute_swap b hb t hta htb j hjt,
    h.rootCentralizer_involution_card b hb t hta htb j hj hjt]

/-- The conjugacy class of the torus involution has 63 elements. -/
public theorem torus_involution_conjugacyClass_card [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (hta : t • a = b) (htb : t • b = a)
    (j : stabilizer (stabilizer G a) b) (hj : orderOf (j : G) = 2)
    (hjt : Commute ((j : stabilizer G a) : G) t) :
    Nat.card (ConjClasses.mk ((j : stabilizer G a) : G)).carrier = 63 := by
  have hc := ConjClasses.nat_card_carrier_mul_card_centralizer
    ((j : stabilizer G a) : G)
  rw [h.torus_involution_centralizer_card b hb t hta htb j hj hjt,
    h.group_card] at hc
  omega

end Stellmacher.Recognition.SuzukiThreeHypotheses
