module

public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Odd involutions and the Frattini quotient of a commutator subgroup

Let `P` be a finite odd p-subgroup normalized by an elementary abelian
2-subgroup `A`, and let `t` be an involution in `A`. We use the literal
ambient subgroups `R = [P, ⟨t⟩]` and `Rw = [C_P(w), ⟨t⟩]`.
Both are normalized by `A`; their conjugation actions and their inclusion
are compatible. The induced action of `t` inverts `R / Φ(R)`, and the image
of `Rw.subgroupOf R` under the quotient homomorphism is precisely the
fixed subgroup of `w` there.

For inversion, each commutator generator of `R` is inverted by `t`, and
`R / Φ(R)` is abelian. For the fixed-subgroup equality, odd-order fixed-point
lifting supplies a `w`-fixed preimage in `R`; taking its commutator with `t`
squares its quotient image. Squaring is bijective on the odd fixed subgroup.
Coprime commutator idempotence gives `[R,t] = R` and `[Rw,t] = Rw`.
Finally, the Frattini automorphism kernel is a p-group, so a coprime
involutory automorphism trivial on the quotient is trivial on `R`.
No faithfulness of the actor is required.

Source: GLS, *The Classification of the Finite Simple Groups*, volume 4,
Chapter 2, Proposition 16.5, the passage beginning “Set R̄ = R/Φ(R)”
(`refs/KGroup/GLS4/Chapter2.tex`, around lines 2936–2948).
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace OddInvolutionFrattini
variable {G : Type*} [Group G]
/-- The actual ambient commutator subgroup `[P, ⟨t⟩]`. -/
def R (P : Subgroup G) (t : G) : Subgroup G := ⁅P, zpowers t⁆
/-- The actual ambient subgroup `[C_P(w), ⟨t⟩]`, using the relative centralizer in `P`. -/
def Rw (P : Subgroup G) (t w : G) : Subgroup G := ⁅P ⊓ centralizer ({w} : Set G), zpowers t⁆
/-- Each fixed-centralizer commutator subgroup lies in `R`. -/
theorem rw_le (P : Subgroup G) (t w : G) : Rw P t w ≤ R P t :=
  commutator_mono inf_le_left le_rfl

private theorem normalizes_commutator (P T A : Subgroup G)
    (hP : A ≤ normalizer P) (hT : A ≤ normalizer T) : A ≤ normalizer (⁅P,T⁆ : Subgroup G) := by
  apply subgroup_le_normalizer_of_conj_mem
  intro a x hx
  have hm : (⁅P,T⁆).map (MulAut.conj (a : G)).toMonoidHom ≤ ⁅P,T⁆ := by
    rw [map_commutator]
    apply commutator_mono
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp (hP a.property) x).mp hx
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp (hT a.property) x).mp hx
  exact hm (mem_map_of_mem _ hx)

private theorem centralizes_zpowers (A : Subgroup G) [IsMulCommutative A]
    {t : G} (ht : t ∈ A) : A ≤ centralizer (zpowers t : Set G) := by
  intro a ha x hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  exact (show Commute t a from Subtype.ext_iff.mp (mul_comm (⟨t,ht⟩ : A) ⟨a,ha⟩)).zpow_left n

/-- An abelian actor normalizing `P` and containing `t` normalizes `R`. -/
theorem normalizes_R (P A : Subgroup G) [IsMulCommutative A]
    (hAP : A ≤ normalizer P) {t : G} (ht : t ∈ A) : A ≤ normalizer (R P t) := by
  exact normalizes_commutator P (zpowers t) A hAP
    ((centralizes_zpowers A ht).trans (centralizer_le_normalizer _))

private theorem normalizes_centralizer (A : Subgroup G) [IsMulCommutative A]
    {w : G} (hw : w ∈ A) : A ≤ normalizer (centralizer ({w} : Set G)) := by
  apply subgroup_le_normalizer_of_conj_mem
  intro a x hx
  have haw : Commute w (a : G) := Subtype.ext_iff.mp (mul_comm (⟨w,hw⟩ : A) a)
  have hwx : Commute w x := (mem_centralizer_singleton_iff.mp hx).symm
  exact mem_centralizer_singleton_iff.mpr ((haw.mul_right hwx).mul_right haw.inv_right).symm

/-- The actor also normalizes every fixed-centralizer commutator subgroup. -/
theorem normalizes_Rw (P A : Subgroup G) [IsMulCommutative A]
    (hAP : A ≤ normalizer P) {t w : G} (ht : t ∈ A) (hw : w ∈ A) :
    A ≤ normalizer (Rw P t w) := by
  exact normalizes_commutator _ _ A
    ((le_inf hAP (normalizes_centralizer A hw)).trans inf_normalizer_le_normalizer_inf)
    ((centralizes_zpowers A ht).trans (centralizer_le_normalizer _))

/-- The conjugation action, encoded as a homomorphism to actual automorphisms. -/
def conjugation (A H : Subgroup G) (hn : A ≤ normalizer H) : A →* MulAut H := by
  letI := conjMulDistribMulActionOfLeNormalizer A H hn
  exact MulDistribMulAction.toMulAut A H

/-- The subgroup action is literal ambient conjugation. -/
theorem conjugation_apply (A H : Subgroup G) (hn : A ≤ normalizer H) (a : A) (x : H) :
    (conjugation A H hn a x : G) = (a : G) * x * (a : G)⁻¹ := rfl

/-- Subgroup inclusions are equivariant for the actual conjugation actions.
In particular this applies to `Rw ≤ R` with their proved normalization hypotheses. -/
theorem conjugation_inclusion (A H K : Subgroup G)
    (hnH : A ≤ normalizer H) (hnK : A ≤ normalizer K) (hHK : H ≤ K)
    (a : A) (x : H) :
    inclusion hHK (conjugation A H hnH a x) =
      conjugation A K hnK a (inclusion hHK x) := by
  apply Subtype.ext
  rfl

/-- The induced action on the literal Frattini quotient. -/
def quotientConjugation (A H : Subgroup G) (hn : A ≤ normalizer H) :
    A →* MulAut (H ⧸ frattini H) :=
  (quotientAut (frattini H)).comp (conjugation A H hn)

/-- The quotient action agrees with conjugation on representatives. -/
theorem quotientConjugation_mk (A H : Subgroup G) (hn : A ≤ normalizer H)
    (a : A) (x : H) : quotientConjugation A H hn a (QuotientGroup.mk' (frattini H) x) =
      QuotientGroup.mk' (frattini H) (conjugation A H hn a x) := by
  exact quotientAut_apply_mk _ _ _

/-- A noncyclic finite group has noncyclic Frattini quotient. -/
theorem noncyclic_frattini_quotient {K : Type*} [Group K] [Finite K]
    (hK : ¬ IsCyclic K) : ¬ IsCyclic (K ⧸ frattini K) := by
  intro hq
  obtain ⟨q,hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hq
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini K) q
  have hm : (zpowers x).map (QuotientGroup.mk' (frattini K)) = ⊤ := by
    simpa only [MonoidHom.map_zpowers] using hq
  have hs : zpowers x ⊔ frattini K = ⊤ := by
    have := congrArg (Subgroup.comap (QuotientGroup.mk' (frattini K))) hm
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using this
  exact hK (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, frattini_nongenerating hs⟩)

/-- A coprime-order automorphism of a finite p-group trivial modulo its Frattini subgroup is trivial. -/
theorem automorphism_eq_one_of_quotient_eq_one {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hK : IsPGroup p K) (f : MulAut K)
    (hcop : Nat.Coprime (orderOf f) p) (hf : quotientAut (frattini K) f = 1) : f = 1 := by
  let a : (quotientAut (frattini K)).ker := ⟨f,hf⟩
  obtain ⟨n,hn⟩ := (isPGroup_quotientAut_frattini_kernel hK).exists_orderOf_dvd_pow a
  have hd : orderOf f ∣ p ^ n := by
    change orderOf (⟨f,hf⟩ : (quotientAut (frattini K)).ker) ∣ p ^ n at hn
    exact (Subgroup.orderOf_coe a) ▸ hn
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hcop.pow_right n) (dvd_refl _) hd)

/-- An automorphism of order dividing two is detected on an odd p-group’s Frattini quotient.
The automorphism is allowed to be the identity. -/
theorem involution_eq_one_of_quotient_eq_one {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hK : IsPGroup p K) (hp : Nat.Coprime 2 p) (f : MulAut K)
    (hf2 : f ^ 2 = 1) (hf : quotientAut (frattini K) f = 1) : f = 1 :=
  automorphism_eq_one_of_quotient_eq_one hK f
    (hp.of_dvd_left (orderOf_dvd_of_pow_eq_one hf2)) hf

/-- Normalization of `P` by `t` places the commutator subgroup inside `P`. -/
theorem r_le (P : Subgroup G) {t : G} (hn : t ∈ normalizer P) : R P t ≤ P :=
  le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hn)

/-- Odd-order coprime action gives `[R,t] = R`. -/
theorem repeated_commutator [Finite G] (P : Subgroup G) {t : G}
    (hn : t ∈ normalizer P) (ht : t ≠ 1 ∧ t ^ 2 = 1)
    (hodd : Nat.Coprime 2 (Nat.card P)) : ⁅R P t, zpowers t⁆ = R P t := by
  have h := commutator_closure_coprime_idempotent P {t}
    (by simpa only [← zpowers_eq_closure] using (zpowers_le.mpr hn))
    (by intro a ha; obtain rfl := Set.mem_singleton_iff.mp ha
        simpa only [orderOf_eq_prime ht.2 ht.1] using hodd)
  simpa only [← zpowers_eq_closure, R] using h

private theorem mem_zpowers_involution {t x : G} (ht : t ≠ 1 ∧ t ^ 2 = 1)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
  have hr : t ^ n = t ^ (n % 2) := by
    simpa only [orderOf_eq_prime ht.2 ht.1, Nat.cast_ofNat] using
      (zpow_mod_orderOf t n).symm
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [hr,h]; simp
  · right; rw [hr,h]; simp

private theorem conjugate_commutator_involution {t : G} (ht : t ^ 2 = 1) (x : G) :
    t * ⁅x,t⁆ * t⁻¹ = ⁅x,t⁆⁻¹ := by
  have hi : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht)
  simp only [commutatorElement_def, mul_inv_rev, inv_inv]
  calc
    t * (x * t * x⁻¹ * t⁻¹) * t⁻¹ = t * x * t * x⁻¹ * (t⁻¹ * t⁻¹) := by group
    _ = t * x * t * x⁻¹ := by rw [hi, ← pow_two, ht, mul_one]
    _ = t * (x * (t⁻¹ * x⁻¹)) := by rw [hi]; group

/-- The involution inverts the actual Frattini quotient of `[P, ⟨t⟩]`.
Inversion follows from the commutator generators, without assuming it on the quotient. -/
theorem inverts_frattini_quotient [Finite G] {p : ℕ} [Fact p.Prime]
    (P A : Subgroup G) [IsMulCommutative A] (hP : IsPGroup p P)
    (hAP : A ≤ normalizer P) {t : G} (htA : t ∈ A) (ht : t ≠ 1 ∧ t ^ 2 = 1) :
    ∀ q : R P t ⧸ frattini (R P t),
      quotientConjugation A (R P t) (normalizes_R P A hAP htA) ⟨t,htA⟩ q = q⁻¹ := by
  let H := R P t
  let hn := normalizes_R P A hAP htA
  let f := quotientConjugation A H hn ⟨t,htA⟩
  let π := QuotientGroup.mk' (frattini H)
  have hHP : H ≤ P := r_le P (hAP htA)
  have hHp : IsPGroup p H := hP.of_injective (Subgroup.inclusion hHP) (Subgroup.inclusion_injective hHP)
  let : Fact (IsPGroup p H) := ⟨hHp⟩
  let : IsElementaryAbelian p (H ⧸ frattini H) := isElementaryAbelian_quotient_frattini
  have hi : ∀ (x : G) (hx : x ∈ H), f (π ⟨x,hx⟩) = (π ⟨x,hx⟩)⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y,hy,z,hz,rfl⟩ := hx
      rcases mem_zpowers_involution ht hz with hz1 | hzt
      · subst z
        simp only [commutatorElement_one_right]
        change f (π 1) = (π 1)⁻¹
        simp
      · subst z
        rw [show f (π _) = π (conjugation A H hn ⟨t,htA⟩ _) from
          quotientConjugation_mk A H hn _ _]
        rw [← map_inv]
        congr 1
        apply Subtype.ext
        exact conjugate_commutator_involution ht.2 y
    | one => change f (π 1) = (π 1)⁻¹; simp
    | mul x y hx hy ihx ihy =>
      change f (π (⟨x,hx⟩ * ⟨y,hy⟩)) = (π (⟨x,hx⟩ * ⟨y,hy⟩))⁻¹
      simp only [map_mul, ihx, ihy, mul_inv_rev]
      exact mul_comm _ _
    | inv x hx ih =>
      change f (π (⟨x,hx⟩ : H)⁻¹) = (π (⟨x,hx⟩ : H)⁻¹)⁻¹
      simp only [map_inv, ih]
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini H) q
  exact hi x x.property

private theorem odd_card_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (hp : Odd p) : Odd (Nat.card G) := by
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  rw [hn]
  exact hp.pow

private theorem involutive_of_pow_two {B K : Type*} [Group B] [Group K]
    (f : B →* MulAut K) (b : B) (hb : b ^ 2 = 1) : Function.Involutive (f b) := by
  intro x
  have hh : (f b) ^ 2 = 1 := by rw [← map_pow, hb, map_one]
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using
    congrArg (fun a : MulAut K => a x) hh

/-- Being fixed by the subgroup action means centralizing the ambient actor element. -/
theorem conjugation_fixed_iff (A H : Subgroup G) (hn : A ≤ normalizer H)
    (a : A) (x : H) : conjugation A H hn a x = x ↔
      (x : G) ∈ centralizer ({(a : G)} : Set G) := by
  rw [Subtype.ext_iff, conjugation_apply, mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

/-- Every element of `Rw` centralizes `w`. -/
theorem rw_le_centralizer (P A : Subgroup G) [IsMulCommutative A]
    {t w : G} (ht : t ∈ A) (hw : w ∈ A) :
    Rw P t w ≤ centralizer ({w} : Set G) := by
  apply le_trans (commutator_le_sup _ _)
  apply sup_le inf_le_right
  apply zpowers_le.mpr
  apply mem_centralizer_singleton_iff.mpr
  exact Subtype.ext_iff.mp (mul_comm (⟨t,ht⟩ : A) ⟨w,hw⟩)

/-- For an involutory conjugation action on an odd-order subgroup, fixed points lift through
the Frattini quotient. The actor may act trivially. -/
theorem fixed_frattini_map [Finite G] (A H : Subgroup G)
    (hn : A ≤ normalizer H) (hodd : Odd (Nat.card H))
    (a : A) (ha : a ^ 2 = 1) :
    (MulAut.fixedSubgroup (conjugation A H hn a)).map (QuotientGroup.mk' (frattini H)) =
      MulAut.fixedSubgroup (quotientConjugation A H hn a) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [MulAut.mem_fixedSubgroup, quotientConjugation_mk,
      (MulAut.mem_fixedSubgroup _ _).mp hx]
  · intro hq
    obtain ⟨x, hx, he⟩ := MulAut.exists_fixed_preimage_of_odd_card hodd
      (hodd.of_dvd_nat (card_quotient_dvd_card (frattini H)))
      (conjugation A H hn a) (quotientConjugation A H hn a)
      (involutive_of_pow_two _ a ha) (involutive_of_pow_two _ a ha)
      (QuotientGroup.mk' (frattini H)) (QuotientGroup.mk'_surjective _)
      (fun x => (quotientConjugation_mk A H hn a x).symm) q
      ((MulAut.mem_fixedSubgroup _ _).mp hq)
    exact ⟨x, (MulAut.mem_fixedSubgroup _ _).mpr hx, he⟩

/-- Commutating an element of `R` with `t` squares its image in `R / Φ(R)`. -/
theorem quotient_commutator_eq_sq [Finite G] {p : ℕ} [Fact p.Prime]
    (P A : Subgroup G) [IsMulCommutative A] (hP : IsPGroup p P)
    (hAP : A ≤ normalizer P) {t : G} (htA : t ∈ A) (ht : t ≠ 1 ∧ t ^ 2 = 1)
    (x : R P t) :
    QuotientGroup.mk' (frattini (R P t))
      ⟨⁅(x : G),t⁆, commutator_mem_commutator (r_le P (hAP htA) x.property) (mem_zpowers t)⟩ =
      (QuotientGroup.mk' (frattini (R P t)) x) ^ 2 := by
  let hn := normalizes_R P A hAP htA
  have hc : (⟨⁅(x : G),t⁆, commutator_mem_commutator
      (r_le P (hAP htA) x.property) (mem_zpowers t)⟩ : R P t) =
      x * (conjugation A (R P t) hn ⟨t,htA⟩ x)⁻¹ := by
    apply Subtype.ext
    simp only [coe_mul, coe_inv, conjugation_apply, commutatorElement_def]
    group
  rw [hc, map_mul, map_inv, ← quotientConjugation_mk,
    inverts_frattini_quotient P A hP hAP htA ht, inv_inv, pow_two]

/-- The image of the actual `Rw` in the literal quotient `R / Φ(R)` equals its `w`-fixed subgroup.
This holds for every `w ∈ A`, including the identity. -/
theorem image_rw_eq_fixed [Finite G] {p : ℕ} [Fact p.Prime]
    (P A : Subgroup G) [IsElementaryAbelian 2 A] (hP : IsPGroup p P) (hp : Odd p)
    (hAP : A ≤ normalizer P) {t w : G} (htA : t ∈ A) (hwA : w ∈ A)
    (ht : t ≠ 1 ∧ t ^ 2 = 1) :
    ((Rw P t w).subgroupOf (R P t)).map (QuotientGroup.mk' (frattini (R P t))) =
      MulAut.fixedSubgroup
        (quotientConjugation A (R P t) (normalizes_R P A hAP htA) ⟨w,hwA⟩) := by
  let H := R P t
  let hn := normalizes_R P A hAP htA
  let π := QuotientGroup.mk' (frattini H)
  let b := quotientConjugation A H hn ⟨w,hwA⟩
  have hHP : H ≤ P := r_le P (hAP htA)
  have hHodd : Odd (Nat.card H) := odd_card_of_isPGroup
    (hP.of_injective (inclusion hHP) (inclusion_injective hHP)) hp
  have hw2 : (⟨w,hwA⟩ : A) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) _
  have hlift := fixed_frattini_map A H hn hHodd ⟨w,hwA⟩ hw2
  apply le_antisymm
  · rintro q ⟨x, hx, rfl⟩
    rw [MulAut.mem_fixedSubgroup, quotientConjugation_mk]
    congr 1
    apply (conjugation_fixed_iff A H hn _ x).mpr
    exact rw_le_centralizer P A htA hwA hx
  · intro q hq
    have hCodd : Odd (Nat.card (MulAut.fixedSubgroup b)) :=
      (hHodd.of_dvd_nat (card_quotient_dvd_card (frattini H))).of_dvd_nat
        (card_subgroup_dvd_card _)
    obtain ⟨s, hs⟩ := (powCoprime (G := MulAut.fixedSubgroup b)
      (n := 2) hCodd.coprime_two_right).surjective ⟨q,hq⟩
    have hs2 : (s : H ⧸ frattini H) ^ 2 = q := congrArg Subtype.val hs
    have hsfix : (s : H ⧸ frattini H) ∈
        (MulAut.fixedSubgroup (conjugation A H hn ⟨w,hwA⟩)).map π := by
      rw [hlift]
      exact s.property
    obtain ⟨x, hx, hxs⟩ := hsfix
    have hxw : (x : G) ∈ centralizer ({w} : Set G) :=
      (conjugation_fixed_iff A H hn _ x).mp ((MulAut.mem_fixedSubgroup _ _).mp hx)
    have hcRw : ⁅(x : G),t⁆ ∈ Rw P t w :=
      commutator_mem_commutator ⟨hHP x.property, hxw⟩ (mem_zpowers t)
    refine ⟨⟨⁅(x : G),t⁆, rw_le P t w hcRw⟩, hcRw, ?_⟩
    change π _ = q
    rw [quotient_commutator_eq_sq P A hP hAP htA ht, hxs, hs2]

/-- The repeated-commutator identity for an odd p-subgroup. -/
theorem repeated_commutator_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P) (hp : Odd p) {t : G}
    (hn : t ∈ normalizer P) (ht : t ≠ 1 ∧ t ^ 2 = 1) :
    ⁅R P t, zpowers t⁆ = R P t :=
  repeated_commutator P hn ht (odd_card_of_isPGroup hP hp).coprime_two_left

/-- The fixed-centralizer commutator subgroup also satisfies `[Rw,t] = Rw`. -/
theorem repeated_rw_commutator [Finite G] {p : ℕ} [Fact p.Prime]
    (P A : Subgroup G) [IsMulCommutative A] (hP : IsPGroup p P) (hp : Odd p)
    (hAP : A ≤ normalizer P) {t w : G} (htA : t ∈ A) (hwA : w ∈ A)
    (ht : t ≠ 1 ∧ t ^ 2 = 1) : ⁅Rw P t w, zpowers t⁆ = Rw P t w := by
  have hn : A ≤ normalizer (P ⊓ centralizer ({w} : Set G)) :=
    (le_inf hAP (normalizes_centralizer A hwA)).trans inf_normalizer_le_normalizer_inf
  exact repeated_commutator_of_isPGroup _
    (hP.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)) hp (hn htA) ht

/-- Trivial involutory action on the Frattini quotient gives actual ambient centralization,
without any assumption that the actor acts faithfully. -/
theorem centralizes_of_quotientConjugation_eq_one [Finite G] {p : ℕ}
    (A H : Subgroup G) (hH : IsPGroup p H) (hp : Odd p)
    (hn : A ≤ normalizer H) (a : A) (ha : a ^ 2 = 1)
    (hq : quotientConjugation A H hn a = 1) :
    H ≤ centralizer ({(a : G)} : Set G) := by
  have h2 : (conjugation A H hn a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have he : conjugation A H hn a = 1 :=
    involution_eq_one_of_quotient_eq_one hH hp.coprime_two_left _ h2 hq
  intro x hx
  apply (conjugation_fixed_iff A H hn a ⟨x,hx⟩).mp
  rw [he]
  rfl

end OddInvolutionFrattini
