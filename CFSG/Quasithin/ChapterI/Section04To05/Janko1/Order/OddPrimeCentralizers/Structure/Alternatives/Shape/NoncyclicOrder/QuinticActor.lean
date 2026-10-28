module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.NoncyclicOrder.FixedFusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.FixedInvolution
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.FieldTheory.Finite.Basic

/-!
# A cubic actor in the order-125 branch

Assume the actual odd centralizer complement A is abelian of order 125.
The marked prime and all three fixed orders of its normalizing four-group
are five. A two-subgroup of N_G(A) containing the marked involution acts
on its fixed C₅. Its image is cyclic of exponent dividing two, and its
kernel embeds in C_G(x), of order 250. Both have order at most two, so
the normalizing four-group is Sylow in N_G(A).

Equal-fixed-order fusion and Burnside fusion now give a nontrivial odd
automizer of this four-group. Its order divides six, hence is three.
Cauchy's theorem constructs an actual cubic subgroup X normalizing A and
the four-group. The existing four-centralizer calculation gives an
involution fixed by X. The fixed-point congruence |C_A(X)| ≡ 125 (mod 3)
gives a nonidentity fixed element of A.

This is the conditional quintic-branch construction used in the noncyclic
order restriction of Bender, *Finite groups with large subgroups* (1974),
proof of (4.1), printed p.225 (PDF p.3), citing Janko (1966), proof of
Lemma 3.1, DOI 10.1016/0021-8693(66)90010-X. No exceptional normalizer,
universal complement commutativity, or Sylow status is assumed.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- A two-subgroup containing z acts on C_A(z) = C₅ with kernel and image
both of order at most two. -/
private theorem two_subgroup_bound
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 5)
    (hc : Nat.card A = 125) (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (A : Set G)) (hzP : h.z ∈ P) : Nat.card P ≤ 4 := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hPd : Nat.card P ∣ 8 := h.any_sylow_card S ▸ card_dvd_of_le hPS
  have hpow (u : P) : u ^ 2 = 1 :=
    Subtype.ext (congrArg (fun v : S => (v : G)) (h.any_sylow_square S ⟨u, hPS u.property⟩))
  have hcomm (u v : P) : Commute u v :=
    Commute.of_orderOf_dvd_two (fun w => orderOf_dvd_of_pow_eq_one (hpow w)) u v
  let U := zpowers x
  have hPU : P ≤ normalizer (U : Set G) := by
    rw [show U = A ⊓ centralizer ({h.z} : Set G) from
      (a.inf_centralizer_eq_zpowers h 5 (Or.inr rfl) hxC hx).symm]
    apply le_trans (le_inf hPN ?_) inf_normalizer_le_normalizer_inf
    intro g hg
    apply (centralizer ({h.z} : Set G)).le_normalizer
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hcomm ⟨g, hg⟩ ⟨h.z, hzP⟩).eq)
  let f : P →* MulAut U := U.normalizerMonoidHom.comp (inclusion hPU)
  have hU : Nat.card U = 5 := by rw [Nat.card_zpowers, hx]
  let : Fact (Nat.card U).Prime := ⟨by rw [hU]; decide⟩
  let : IsCyclic (MulAut U) :=
    isCyclic_of_injective (IsCyclic.mulAutMulEquiv U).toMonoidHom
      (IsCyclic.mulAutMulEquiv U).injective
  have hRd : Nat.card f.range ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨w, u, rfl⟩
    apply Subtype.ext
    change f u ^ 2 = 1
    rw [← map_pow, hpow, map_one]
  let j : f.ker →* centralizer ({x} : Set G) := {
    toFun := fun u => ⟨u.val.val, by
      have hf := congrArg (fun e : MulAut U => e ⟨x, mem_zpowers x⟩)
        (show f u.val = 1 from u.property)
      have hfG := congrArg Subtype.val hf
      change u.val.val * x * u.val.val⁻¹ = x at hfG
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfG)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro u v he
    exact Subtype.ext (Subtype.ext (congrArg (fun v : centralizer ({x} : Set G) => (v : G)) he))
  have hKd : Nat.card f.ker ∣ 2 := by
    have hd := Nat.dvd_gcd (f.ker.card_subgroup_dvd_card.trans hPd)
      (card_dvd_of_injective j hj)
    rw [a.centralizer_card, hc] at hd
    exact hd
  have hm := f.ker.card_mul_index
  rw [index_ker] at hm
  have hk := Nat.le_of_dvd (by decide : 0 < 2) hKd
  have hr := Nat.le_of_dvd (by decide : 0 < 2) hRd
  nlinarith
end CFSG.Quasithin.Janko1CentralizerData

open Subgroup
open scoped IsMulCommutative

/-- Nontrivial fusion in an abelian Sylow four-group forces a cubic
factor in its normalizer: its nontrivial automizer has odd order dividing six. -/
private theorem sylow_four_three_dvd_of_fused
    {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (hP : Nat.card P = 4)
    (hpow : ∀ u : P, u ^ 2 = 1)
    (s t g : H) (hs : s ∈ P) (ht : t ∈ P) (hst : s ≠ t)
    (hgt : g * s * g⁻¹ = t) : 3 ∣ Nat.card (normalizer (P : Set H)) := by
  have hcomm (u v : P) : Commute u v :=
    Commute.of_orderOf_dvd_two (fun w => orderOf_dvd_of_pow_eq_one (hpow w)) u v
  let : IsMulCommutative P := ⟨⟨fun u v => (hcomm u v).eq⟩⟩
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have he : Monoid.exponent P = 2 := by
    have hd := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
    exact (Nat.prime_two.eq_one_or_self_of_dvd _ hd).resolve_left
      (Nat.ne_of_gt Monoid.one_lt_exponent)
  let : IsKleinFour P := ⟨hP, he⟩
  let N := normalizer (P : Set H)
  let f := (P : Subgroup H).normalizerMonoidHom
  have hd : Nat.card f.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut P]
    exact f.range.card_subgroup_dvd_card
  have hle : (P : Subgroup H).subgroupOf N ≤ f.ker := by
    rw [normalizerMonoidHom_ker]
    intro u hu
    exact Subgroup.le_centralizer (P : Subgroup H) hu
  have hn : ¬ 2 ∣ Nat.card f.range := by
    intro hh
    apply (P.subtype (P : Subgroup H).le_normalizer).not_dvd_index
    have hi := index_dvd_of_le hle
    rw [index_ker] at hi
    exact hh.trans hi
  have hne : Nat.card f.range ≠ 1 := by
    intro hc
    have hbot : f.range = ⊥ := f.range.eq_bot_iff_card.mpr hc
    have hf : f = 1 := f.range_eq_bot_iff.mp hbot
    obtain ⟨n, hn, heq⟩ := P.conj_eq_normalizer_conj_of_mem s g⁻¹ hs
      (by simpa only [inv_inv, hgt] using ht)
    have hh := congrArg (fun k : MulAut P => k ⟨s, hs⟩)
      (congrArg (fun k : N →* MulAut P => k ⟨n⁻¹, N.inv_mem hn⟩) hf)
    have hh' := congrArg Subtype.val hh
    change n⁻¹ * s * (n⁻¹)⁻¹ = s at hh'
    apply hst
    calc
      s = n⁻¹ * s * n := by simpa only [inv_inv] using hh'.symm
      _ = t := by simpa only [inv_inv, hgt] using heq.symm
  have hc : Nat.card f.range = 3 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
    interval_cases hc : Nat.card f.range <;> norm_num at *
  rw [← hc]
  exact card_range_dvd f
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- In the order-125 branch, an actual cubic subgroup normalizes both the
complement and an actual normalizing four-group. -/
public theorem OddCentralizerComplement.exists_three_normalizing_four_of_card_125
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (ha : IsMulCommutative A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hc : Nat.card A = 125) :
    ∃ V X : Subgroup G, Nat.card V = 4 ∧ Nat.card X = 3 ∧
      V ≤ normalizer (A : Set G) ∧ X ≤ normalizer (A : Set G) ∧
      X ≤ normalizer (V : Set G) := by
  have hp5 : p = 5 := by
    have hd := Subgroup.orderOf_dvd_natCard A a.x_mem
    rw [hx, hc] at hd
    rcases hp with rfl | hp
    · norm_num at hd
    · exact hp
  have hx5 : orderOf x = 5 := hx.trans hp5
  obtain ⟨t, htC, ht, htz, hti⟩ := h.exists_local_inverter 5 (Or.inr rfl) x hxC hx5
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htfixed : Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = 5 := by
    have he := a.four_fixed_card 5 (Or.inr rfl) hxC hx5 t htC ht htz hti
    obtain ⟨hq, hr⟩ := a.four_fixed_orders t htC ht htz
    rw [hc] at he
    have hq5 : Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) ≤ 5 := by
      rcases hq with hq | hq | hq <;> omega
    have hr5 : Nat.card (A ⊓ centralizer ({h.z * t} : Set G) : Subgroup G) ≤ 5 := by
      rcases hr with hr | hr | hr <;> omega
    have hb := Nat.mul_le_mul_left
      (Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G)) hr5
    nlinarith
  let V := zpowers h.z ⊔ zpowers t
  have htnz : t ∈ normalizer (zpowers h.z : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (t * h.z * t⁻¹) = zpowers h.z
    rw [mem_centralizer_singleton_iff.mp htC, mul_assoc, mul_inv_cancel, mul_one]
  have hV : Nat.card V = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers h.z) t ht2 htz htnz,
      Nat.card_zpowers, h.involution]
  let N := normalizer (A : Set G)
  have hVN : V ≤ N := sup_le (zpowers_le.mpr a.z_mem_normalizer)
    (zpowers_le.mpr (a.inverter_mem_normalizer t hti))
  have hzV : h.z ∈ V := (show zpowers h.z ≤ V from le_sup_left) (mem_zpowers h.z)
  have htV : t ∈ V := (show zpowers t ≤ V from le_sup_right) (mem_zpowers t)
  let W := V.subgroupOf N
  have hW : Nat.card W = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv).trans hV
  obtain ⟨P, hWP⟩ := (IsPGroup.of_card (p := 2) (n := 2)
    (show Nat.card W = 2 ^ 2 by omega)).exists_le_sylow
  let Q := (P : Subgroup N).map N.subtype
  have hQ : IsPGroup 2 Q := P.isPGroup'.map N.subtype
  have hQN : Q ≤ N := by
    rintro _ ⟨v, _, rfl⟩
    exact v.property
  have hzQ : h.z ∈ Q := mem_map.mpr
    ⟨⟨h.z, hVN hzV⟩, hWP hzV, rfl⟩
  have hQcard : Nat.card Q = Nat.card P := card_map_of_injective N.subtype_injective
  have hPbound : Nat.card P ≤ 4 := by
    rw [← hQcard]
    exact two_subgroup_bound a hxC hx5 hc Q hQ hQN hzQ
  have hPW : (P : Subgroup N) = W :=
    (eq_of_le_of_card_ge hWP (by rw [hW]; exact hPbound)).symm
  have hP : Nat.card P = 4 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hPW).toEquiv).trans hW
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  have hpow (v : P) : v ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : S => (w : G)) (h.any_sylow_square S
      ⟨v.val.val, hQS (mem_map.mpr ⟨v.val, v.property, rfl⟩)⟩)
  obtain ⟨g, hgN, hgt⟩ := a.exists_normalizer_conj_of_fixed_card ha 5 (Or.inr rfl)
    hxC hx5 t ht htfixed
  let tN : N := ⟨t, hVN htV⟩
  let zN : N := ⟨h.z, hVN hzV⟩
  have htP : tN ∈ P := hWP htV
  have hzP : zN ∈ P := hWP hzV
  have htzN : tN ≠ zN := by
    intro he
    have he' : t = h.z := congrArg (fun v : N => (v : G)) he
    apply htz
    rw [he']
    exact mem_zpowers h.z
  have h3 : 3 ∣ Nat.card (normalizer (P : Set N)) :=
    sylow_four_three_dvd_of_fused P hP hpow tN zN ⟨g, hgN⟩ htP hzP htzN
      (Subtype.ext hgt)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (P : Set N)) 3 h3
  have huG : orderOf (u.val.val : G) = 3 := by
    exact (Subgroup.orderOf_mk _ _).symm.trans
      ((Subgroup.orderOf_mk _ _).symm.trans hu)
  have huV : u.val.val ∈ normalizer (V : Set G) := by
    have hn := u.property
    change u.val ∈ normalizer ((P : Subgroup N) : Set N) at hn
    rw [hPW, ← subgroupOf_normalizer_eq hVN] at hn
    exact hn
  refine ⟨V, zpowers (u.val.val : G), hV, ?_, hVN, ?_, zpowers_le.mpr huV⟩
  · rw [Nat.card_zpowers, huG]
  · exact zpowers_le.mpr u.val.property

/-- The cubic actor fixes an involution and a nonidentity element of the
order-125 complement, using only local complement commutativity. -/
public theorem OddCentralizerComplement.exists_fixed_three_of_card_125
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (ha : IsMulCommutative A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hc : Nat.card A = 125) :
    ∃ u t y : G, orderOf u = 3 ∧ orderOf t = 2 ∧ Commute u t ∧
      y ∈ A ∧ y ≠ 1 ∧ Commute u y := by
  obtain ⟨V, X, hV, hX, _, hXA, hXV⟩ :=
    a.exists_three_normalizing_four_of_card_125 ha p hp hxC hx hc
  obtain ⟨t, _, ht, hXt⟩ := h.three_normalizing_four_fixes_involution V X hV hX hXV
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX])
  let _ := conjMulDistribMulActionOfLeNormalizer X A hXA
  let F := FixedPoints.subgroup X A
  have hpg : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX)
  have hm := hpg.card_modEq_card_fixedPoints A
  change Nat.card A % 3 = Nat.card F % 3 at hm
  rw [hc] at hm
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by
    have hpos := Nat.card_pos (α := F)
    omega)
  obtain ⟨y, hy⟩ := exists_ne (1 : F)
  have hyG : (y.val.val : G) ≠ 1 := by
    intro he
    exact hy (Subtype.ext (Subtype.ext he))
  have hfix := congrArg (fun w : A => (w : G)) (y.property u)
  change (u : G) * y.val.val * (u : G)⁻¹ = y.val.val at hfix
  exact ⟨u, t, y.val.val, (Subgroup.orderOf_mk _ _).symm.trans hu, ht,
    mem_centralizer_singleton_iff.mp (hXt u.property), y.val.property, hyG,
    mul_inv_eq_iff_eq_mul.mp hfix⟩

end CFSG.Quasithin.Janko1CentralizerData
