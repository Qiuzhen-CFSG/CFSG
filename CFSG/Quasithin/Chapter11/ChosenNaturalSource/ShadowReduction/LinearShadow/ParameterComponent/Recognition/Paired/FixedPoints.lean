module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.HallProduct
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanPower
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Exchange

/-!
# A fixed diagonal for the actual Hall exchange element

Choose p=3 at even natural-module degree n. Every common binary field
power has square one on the literal 3-torsion. At odd n, a common field
power on p-torsion for p dividing 2^n-1 has period dividing n, whereas
conjugation by the specified Sylow element has two-power order; the
induced action is therefore trivial. In either case the square of that
same element centralizes the actual Hall p-torsion.

HallProduct supplies abelianness of the whole Hall subgroup. The original
SL3/Sp4 marking and preceding 11.0.4 clauses place its p-torsion in the
original Cartan normalizer and supply its common field power. Multiplying
an element of one factor by its conjugate now constructs a nonidentity
fixed diagonal. The original moved prime-order point and the same Sylow
actor are retained. No square-centralizer premise remains.

CartanExclusion consumes these witnesses in the all-fixed-or-fixed-point-free
contradiction. Recognition at generationParameter H remains this owner's
obligation; qt-d-1222-shadow-linear-geometry retains discharge of the genuine
preceding source inputs, produced by qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired

private theorem power_automorphism_iterate {Q : Type*} [Group Q]
    (a : MulAut Q) (m : ℕ) (ha : ∀ x, a x = x ^ m) (k : ℕ) (x : Q) :
    (a ^ k) x = x ^ (m ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',MulAut.mul_apply,ha,ih,←pow_mul,pow_succ]

private theorem field_power_period {Q : Type*} [Group Q]
    (a : MulAut Q) (p n j : ℕ) (hp : ∀ x : Q, x ^ p = 1)
    (hd : p ∣ 2 ^ n - 1) (ha : ∀ x, a x = x ^ (2 ^ j)) : a ^ n = 1 := by
  ext x
  rw [power_automorphism_iterate a (2^j) ha n x,MulAut.one_apply]
  have hd' : p ∣ (2 ^ j) ^ n - 1 := by
    rw [←pow_mul,Nat.mul_comm j n,pow_mul]
    exact hd.trans (by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2^n) 1 j)
  obtain ⟨r,hr⟩ := hd'
  have hx : x ^ ((2 ^ j) ^ n - 1) = 1 := by rw [hr,pow_mul,hp,one_pow]
  have hpos : 1 ≤ (2 ^ j) ^ n := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide))
  calc
    x ^ ((2 ^ j) ^ n) = x ^ (((2 ^ j) ^ n - 1) + 1) := by rw [Nat.sub_add_cancel hpos]
    _ = x := by rw [pow_succ,hx,one_mul]

/-- Choose the cubic prime at even degree and a divisor of 2^n-1 at odd
degree. This choice makes the square of a two-element's field action trivial. -/
theorem exists_square_fixed_prime {n : ℕ} (hn : 1 < n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧ (p = 3 ∨ Odd n) := by
  by_cases he : Even n
  · obtain ⟨r,hr⟩ := he
    have hd : 3 ∣ 2 ^ n - 1 := by
      rw [hr,←two_mul,pow_mul]
      convert Nat.sub_dvd_pow_sub_pow 4 1 r using 1
      norm_num
    exact ⟨3,by decide,by decide,hd,Or.inl rfl⟩
  · have ho := Nat.not_even_iff_odd.mp he
    have hpow : 4 ≤ 2 ^ n := pow_le_pow_right' (by decide : 1 ≤ (2:ℕ)) (by omega : 2 ≤ n)
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n - 1 ≠ 1)
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      have hh := dvd_pow_self 2 (by omega : n ≠ 0)
      have h1 := Nat.mod_eq_zero_of_dvd hd
      have h2 := Nat.mod_eq_zero_of_dvd hh
      omega
    exact ⟨p,hp,hp2,hd,Or.inr ho⟩

variable {G : Type*} [Group G] [Finite G]
/-- On the literal Hall prime torsion, the selected prime forces the square
of the same Sylow actor to centralize. This uses its actual common field power. -/
theorem square_centralizes_selected_prime (T : Sylow 2 G) (A : Subgroup G)
    [IsMulCommutative A] (p n : ℕ) [Fact p.Prime]
    (hd : p ∣ 2 ^ n - 1) (hsel : p = 3 ∨ Odd n)
    (t : T) (ht : (t : G) ∈ normalizer (A : Set G))
    (j : ℕ) (hj : ∀ x ∈ primeTorsion A p, (t : G)*x*(t : G)⁻¹ = x^(2^j)) :
    (t : G)^2 ∈ centralizer (primeTorsion A p : Set G) := by
  let Q := primeTorsion A p
  let u : normalizer (Q : Set G) := ⟨t,primeTorsion_normalizer A p ht⟩
  let a := Q.normalizerMonoidHom u
  have hp : ∀ x : Q, x ^ p = 1 := fun x => Subtype.ext
    ((mem_primeTorsion_iff A p x).mp x.property).2
  have ha : ∀ x : Q, a x = x ^ (2 ^ j) := fun x => Subtype.ext (hj x x.property)
  have hs : a ^ 2 = 1 := by
    rcases hsel with rfl | ho
    · exact field_power_period a 3 2 j hp (by decide) ha
    · have han := field_power_period a p n j hp hd ha
      obtain ⟨r,hr⟩ := T.isPGroup' t
      have hu : u ^ (2 ^ r) = 1 := Subtype.ext (congrArg (fun x : T => (x : G)) hr)
      have har : a ^ (2 ^ r) = 1 := by
        change (Q.normalizerMonoidHom u) ^ (2 ^ r) = 1
        rw [←map_pow,hu,map_one]
      have hone : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes
        ((Nat.coprime_two_right.mpr ho).pow_right r)
        (orderOf_dvd_of_pow_eq_one han) (orderOf_dvd_of_pow_eq_one har)
      rw [orderOf_eq_one_iff.mp hone,one_pow]
  have hs' : Q.normalizerMonoidHom (u ^ 2) = 1 := by rw [map_pow]; exact hs
  intro x hx
  have he := congrArg (fun b : MulAut Q => ((b ⟨x,hx⟩ : Q) : G)) hs'
  change (t : G)^2*x*((t : G)^2)⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- The actual paired Hall subgroup supplies both movement and a nontrivial
fixed diagonal for the same Sylow actor on its literal odd-prime torsion.
The source prime is chosen to justify square centralization, not inferred
merely from exchange of the two factors. -/
theorem ComponentSeed.exists_paired_hall_mixed_action (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (hk : ChapterE.generationParameter H = S.field.degree ∨
      ChapterE.generationParameter H = 2 * S.field.degree)
    (hmark : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ S.field.degree - 1 ∧
      ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
        IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
        IsMulCommutative A ∧
        ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
          (t : G) ∉ normalizer (K : Set G) ∧
          (t : G)^2 ∈ centralizer (Paired.primeTorsion A p : Set G) ∧
          (∃ x ∈ Paired.primeTorsion (A ⊓ K) p, orderOf x = p ∧
            (t : G)*x*(t : G)⁻¹ ≠ x) ∧
          (∃ z ∈ Paired.primeTorsion A p, z ≠ 1 ∧ (t : G)*z*(t : G)⁻¹ = z) ∧
          ∃ j : ℕ, ∀ x ∈ Paired.primeTorsion A p,
            (t : G)*x*(t : G)⁻¹ = x^(2^j) := by
  have hf : 0 < ChapterE.generationParameter H :=
    S.field.degree_pos.trans_le (degree_le_parameter h pr hc hs)
  obtain ⟨p,hp,hp2,hd,hsel⟩ := Paired.exists_square_fixed_prime S.nonbinary
  let : Fact p.Prime := ⟨hp⟩
  have htorus : 2 ^ S.field.degree - 1 ∣ 2 ^ ChapterE.generationParameter H - 1 := by
    rcases hk with he | he
    · rw [he]
    · rw [he,Nat.mul_comm 2 S.field.degree,pow_mul]
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2
  have hdiv := hd.trans (htorus.trans (s.paired_linear_overlap_torus_dvd h pr hc hs hn hm))
  obtain ⟨A,hA,hHall,ho,t,htA,htK,hdis,x,hx,hox,hmx⟩ :=
    s.exists_paired_hall_prime_element h pr hc hs hn hm p hp hp2 hdiv
  have hab := (s.paired_hall_abelian_card h pr hc hs hn hf hm A hA hHall t htA htK).1
  let := hab
  have hinside
      (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
        Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)) :
      Paired.primeTorsion A p ≤ cartanNormalizer T L := by
    have hQL := Paired.source_primeTorsion_le S A hA p hp hd halt hres hcubic
    exact (le_inf (Paired.primeTorsion_le A p) hQL).trans
      ((inf_le_inf_right L (hA.trans inf_le_left)).trans
        (s.paired_linear_inner_sylow h pr hc hs hn hm halt))
  have hpower : ∃ j : ℕ, ∀ x ∈ Paired.primeTorsion A p,
      (t : G)*x*(t : G)⁻¹ = x^(2^j) := by
    rcases hmark with hmL | hmL
    · obtain ⟨m⟩ := hmL
      exact Paired.source_primeTorsion_power_sl3 m A p hp2
        (hinside (.inl ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩)) t htA
    · obtain ⟨m⟩ := hmL
      exact Paired.source_primeTorsion_power_sp4 m A p hp2
        (hinside (.inr ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩)) t htA
  obtain ⟨j,hj⟩ := hpower
  have hsq := Paired.square_centralizes_selected_prime T A p S.field.degree hd hsel t htA j hj
  let : IsMulCommutative (A ⊓ K : Subgroup G) := .of_setLike_mul_comm
    (fun a ha b hb => setLike_mul_comm ha.1 hb.1)
  have hpB : p ∣ Nat.card (A ⊓ K : Subgroup G) := by
    rw [←hox,orderOf_coe (⟨x,hx⟩ : (A ⊓ K : Subgroup G))]
    exact orderOf_dvd_natCard _
  have hBQ : Paired.primeTorsion (A ⊓ K) p ≤ Paired.primeTorsion A p := by
    intro b hb
    obtain ⟨hbB,hbp⟩ := (Paired.mem_primeTorsion_iff (A ⊓ K) p b).mp hb
    exact (Paired.mem_primeTorsion_iff A p b).mpr ⟨hbB.1,hbp⟩
  have hsqB : (t : G)^2 ∈ centralizer (Paired.primeTorsion (A ⊓ K) p : Set G) :=
    centralizer_le hBQ hsq
  obtain ⟨_,z,hz,hz1,hzt⟩ := Paired.exchanged_primeTorsion_mixed A (A ⊓ K) inf_le_left p
    hpB t htA hdis hsqB
  have hxP : x ∈ Paired.primeTorsion (A ⊓ K) p :=
    (Paired.mem_primeTorsion_iff (A ⊓ K) p x).mpr ⟨hx,hox ▸ pow_orderOf_eq_one x⟩
  exact ⟨p,hp,hp2,hd,A,hA,hHall,hab,t,htA,htK,hsq,⟨x,hxP,hox,hmx⟩,
    ⟨z,hz,hz1,hzt⟩,j,hj⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
