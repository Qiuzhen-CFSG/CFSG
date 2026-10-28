module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PrimeRankCentralizer
public import Theory.GroupAction.NormalizerFrattini
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# Group-theoretic reductions for irreducible rank-two actions

The odd class-two omega theorem supplies elementary or Heisenberg models
and bounds their Frattini quotients. Assuming the action on R/Φ(R) is
trivial, Burnside's kernel theorem gives coprime centralization and A.1.23
gives the inner-action alternative. At ambient rank two, centralizing
elements of order p are absorbed by an elementary plane; irreducibility
then identifies the actual normal subgroup with P or its center image.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.32, printed pp.28–29. These are conditional reductions: the small
linear-action argument forcing triviality on R/Φ(R) remains separate.
The omitted trivial case R = 1 is retained in the second conclusion.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.IrreducibleActions
variable {G : Type*} [Group G]

private theorem derived_le_center {Y : Type*} [Group Y]
    (hclass : (⊤ : Subgroup Y).lowerCentralSeries 2 = ⊥) :
    _root_.commutator Y ≤ center Y := by
  apply commutator_top_right_eq_bot_iff_le_center.mp
  rw [show 2 = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
    top_lowerCentralSeries_one] at hclass
  exact hclass

/-- The small odd class-two omega groups are elementary or the concrete prime Heisenberg group; the trivial case is included. -/
public theorem small_models {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    (hp : Odd p) (hY : IsPGroup p Y) (ho : omega₁ Y (p := p) = ⊤)
    (hc : (⊤ : Subgroup Y).lowerCentralSeries 2 = ⊥) (hr : primeRank p Y ≤ 2) :
    IsElementaryAbelian p Y ∨
      (Nat.card Y = p ^ 3 ∧ IsExtraspecial p Y ∧ Nonempty (Y ≃* HeisenbergPrime p)) := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  have hexp := exponent_dvd_prime_of_omega_one_eq_top hp2 (derived_le_center hc) ho
  by_cases ht : primeRank p Y = 2
  · rcases lemma_A_1_24 hp2 hY ho (derived_le_center hc) ht with ⟨_, ⟨e⟩⟩ | h
    · left
      exact { toIsMulCommutative := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
              exponent_dvd_p := hexp }
    · exact Or.inr h
  · left
    have hr1 : primeRank p Y ≤ 1 := by omega
    let : IsCyclic Y := hY.isCyclic_of_odd_of_elementary_card_le hp
      (fun E hE => by
        let := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr1 E)
    exact { exponent_dvd_p := hexp }

/-- The Frattini quotient has order at most p², including the trivial group. -/
public theorem small_frattini_card {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    (hp : Odd p) (hY : IsPGroup p Y) (ho : omega₁ Y (p := p) = ⊤)
    (hc : (⊤ : Subgroup Y).lowerCentralSeries 2 = ⊥) (hr : primeRank p Y ≤ 2) :
    Nat.card (Y ⧸ frattini Y) ≤ p ^ 2 := by
  rcases small_models hp hY ho hc hr with he | ⟨hy, he, _⟩
  · let := he
    have hcard : Nat.card Y ≤ p ^ 2 := by
      have ht := (primeRank_le_iff_elementary_card_le Y).mp hr (⊤ : Subgroup Y)
      let : IsElementaryAbelian p (⊤ : Subgroup Y) := {
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
          (fun x => Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p Y) x)) }
      simpa only [card_top] using ht inferInstance
    exact (Nat.le_of_dvd (Nat.card_pos (α := Y))
      (card_quotient_dvd_card (frattini Y))).trans hcard
  · let := he
    have hphi : Nat.card (frattini Y) = p := by
      rw [IsExtraspecial.frattini_eq_center (p := p), IsExtraspecial.center_order_p p Y]
    have hprod := (frattini Y).index_mul_card
    change Nat.card (Y ⧸ frattini Y) * Nat.card (frattini Y) = Nat.card Y at hprod
    rw [hphi, hy, show 3 = 2 + 1 from rfl, pow_succ] at hprod
    exact (mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hprod).le

private theorem centralizes_of_frattiniConjugationHom_eq_one_coprime [Finite G]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (R P : Subgroup G) [R.Normal]
    (hR : IsPGroup r R) (hP : IsPGroup p P) (hrp : r ≠ p)
    (hfix : frattiniConjugationHom P R le_normalizer_of_normal = 1) : ⁅R, P⁆ = ⊥ := by
  let _ := conjMulDistribMulActionOfLeNormalizer P R le_normalizer_of_normal
  let ρ := MulDistribMulAction.toMulAut P R
  have hdis := IsPGroup.disjoint_of_ne p r hrp.symm ρ.range
    (quotientAut (frattini R)).ker (hP.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective)
    (isPGroup_quotientAut_frattini_kernel hR)
  have hid (a : P) : ρ a = 1 := by
    apply Subgroup.disjoint_def.mp hdis ⟨a, rfl⟩
    change frattiniConjugationHom P R le_normalizer_of_normal a = 1
    rw [hfix, MonoidHom.one_apply]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  intro a ha
  apply mem_centralizer_iff.mpr
  intro x hx
  have hh := congrArg Subtype.val (DFunLike.congr_fun (hid ⟨a, ha⟩) (⟨x, hx⟩ : R))
  change a * x * a⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem centralizes_of_frattiniConjugationHom_eq_one_elementary [Finite G]
    {r : ℕ} [Fact r.Prime] (R P : Subgroup G) [R.Normal]
    [IsElementaryAbelian r R]
    (hfix : frattiniConjugationHom P R le_normalizer_of_normal = 1) : ⁅R, P⁆ = ⊥ := by
  let : Fact (IsPGroup r R) := ⟨IsElementaryAbelian.isPGroup r R⟩
  have hphi : frattini R = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := r)
  have hq : Function.Injective (QuotientGroup.mk' (frattini R)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hphi])
  let _ := conjMulDistribMulActionOfLeNormalizer P R le_normalizer_of_normal
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  intro a ha
  apply mem_centralizer_iff.mpr
  intro x hx
  have hf := DFunLike.congr_fun (DFunLike.congr_fun hfix (⟨a, ha⟩ : P))
    (QuotientGroup.mk' (frattini R) (⟨x, hx⟩ : R))
  change quotientAut (frattini R) (MulDistribMulAction.toMulAut P R ⟨a, ha⟩)
    (QuotientGroup.mk' (frattini R) ⟨x, hx⟩) = QuotientGroup.mk' (frattini R) ⟨x, hx⟩ at hf
  rw [quotientAut_apply_mk] at hf
  have hh := congrArg Subtype.val (hq hf)
  change a * x * a⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem le_sup_centralizer_of_frattiniConjugationHom_eq_one_extraspecial [Finite G]
    {r : ℕ} [Fact r.Prime] (R P : Subgroup G) [R.Normal]
    [IsExtraspecial r R]
    (hfix : frattiniConjugationHom P R le_normalizer_of_normal = 1) :
    P ≤ R ⊔ centralizer (R : Set G) := by
  let _ := conjMulDistribMulActionOfLeNormalizer P R le_normalizer_of_normal
  let ρ := MulDistribMulAction.toMulAut P R
  intro a ha
  have hk : ρ ⟨a, ha⟩ ∈ (quotientAut (frattini R)).ker := by
    change frattiniConjugationHom P R le_normalizer_of_normal (⟨a, ha⟩ : P) = 1
    rw [hfix, MonoidHom.one_apply]
  rw [← lemma_A_1_23 (p := r)] at hk
  obtain ⟨y, hy⟩ := hk
  have hz : (y : G)⁻¹ * a ∈ centralizer (R : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun hy (⟨x, hx⟩ : R))
    change (y : G) * x * (y : G)⁻¹ = a * x * a⁻¹ at hh
    have hax : a * x = (y : G) * x * (y : G)⁻¹ * a := by
      rw [hh, inv_mul_cancel_right]
    calc
      x * ((y : G)⁻¹ * a) = (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹ * a) := by group
      _ = (y : G)⁻¹ * (a * x) := by rw [hax]
      _ = (y : G)⁻¹ * a * x := by group
  have hm := (R ⊔ centralizer (R : Set G)).mul_mem
    (mem_sup_left y.property) (mem_sup_right hz)
  simpa only [mul_inv_cancel_left] using hm

/-- The group-theoretic deduction in A.1.32(1), conditional on triviality of the Frattini action. The missing linear-action step is an explicit premise. -/
public theorem alternatives_of_frattiniConjugationHom_eq_one [Finite G]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hr : Odd r)
    (R P : Subgroup G) [R.Normal] (hR : IsPGroup r R)
    (hoR : omega₁ R (p := r) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank r R ≤ 2)
    (hP : IsPGroup p P)
    (hfix : frattiniConjugationHom P R le_normalizer_of_normal = 1) :
    ⁅R, P⁆ = ⊥ ∨ (p = r ∧ Nonempty (R ≃* HeisenbergPrime p) ∧
      P ≤ R ⊔ centralizer (R : Set G)) := by
  by_cases hrp : r = p
  · subst r
    rcases small_models hr hR hoR hcR hmR with he | ⟨_, he, hm⟩
    · let := he
      exact Or.inl (centralizes_of_frattiniConjugationHom_eq_one_elementary (r := p) R P hfix)
    · let := he
      exact Or.inr ⟨rfl, hm,
        le_sup_centralizer_of_frattiniConjugationHom_eq_one_extraspecial (r := p) R P hfix⟩
  · exact Or.inl (centralizes_of_frattiniConjugationHom_eq_one_coprime R P hR hP hrp hfix)

private theorem eq_bot_or_eq_of_le_prime_card [Finite G] {p : ℕ} [Fact p.Prime]
    {R Z : Subgroup G} (hRZ : R ≤ Z) (hZ : Nat.card Z = p) : R = ⊥ ∨ R = Z := by
  have hd : Nat.card R ∣ p := hZ ▸ card_dvd_of_le hRZ
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
  · exact Or.inl (card_eq_one.mp h)
  · exact Or.inr (eq_of_le_of_card_ge hRZ (by rw [hZ, h]))

private theorem normal_subgroup_alternatives [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (R P : Subgroup G) [R.Normal]
    (hRP : R ≤ P) (hP : IsPGroup p P) (hoP : omega₁ P (p := p) = ⊤)
    (hcP : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P) :
    R = ⊥ ∨ R = P ∨ (Nat.card R = p ∧ Nonempty (R ≃* Multiplicative (ZMod p)) ∧
      Nonempty (P ≃* HeisenbergPrime p) ∧ R = (center P).map P.subtype) := by
  rcases hirr.normal_le_frattini_or_eq hRP with hphi | heq
  · rcases small_models hp hP hoP hcP hmP.le with he | ⟨_, he, hm⟩
    · let := he
      let : Fact (IsPGroup p P) := ⟨hP⟩
      rw [frattini_eq_bot_of_isElementaryAbelian (p := p), Subgroup.map_bot] at hphi
      exact Or.inl (bot_unique hphi)
    · let := he
      have hZ : Nat.card ((center P).map P.subtype) = p := by
        rw [card_map_of_injective P.subtype_injective, IsExtraspecial.center_order_p p P]
      rw [IsExtraspecial.frattini_eq_center (p := p)] at hphi
      rcases eq_bot_or_eq_of_le_prime_card hphi hZ with hb | hz
      · exact Or.inl hb
      · have hcard : Nat.card R = p := hz ▸ hZ
        exact Or.inr (Or.inr ⟨hcard, ⟨mulEquivOfPrimeCardEq hcard (by
          rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
            Nat.card_zmod])⟩, hm, hz⟩)
  · exact Or.inr (Or.inl heq)

private theorem rank_eq_two_of_noncentral_frattini_action [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (R P : Subgroup G) [R.Normal]
    (hR : IsPGroup p R) (hoR : omega₁ R (p := p) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank p R ≤ 2)
    (hfix : frattiniConjugationHom P R le_normalizer_of_normal = 1)
    (hnc : ⁅R, P⁆ ≠ ⊥) : primeRank p R = 2 := by
  by_contra hne
  have hr1 : primeRank p R ≤ 1 := by omega
  let : IsCyclic R := hR.isCyclic_of_odd_of_elementary_card_le hp
    (fun E hE => by
      let := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr1 E)
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  let : IsElementaryAbelian p R := {
    exponent_dvd_p := exponent_dvd_prime_of_omega_one_eq_top hp2 (derived_le_center hcR) hoR }
  exact hnc (centralizes_of_frattiniConjugationHom_eq_one_elementary (r := p) R P hfix)

private theorem le_of_inner_action [Finite G]
    {p : ℕ} [Fact p.Prime] (R P : Subgroup G) [R.Normal]
    (hmG : primeRank p G ≤ 2) (hmR : primeRank p R = 2)
    (hexpR : Monoid.exponent R ∣ p) (hexpP : Monoid.exponent P ∣ p)
    (hinner : P ≤ R ⊔ centralizer (R : Set G)) : P ≤ R := by
  intro x hx
  obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_of_normal_left.mp (hinner hx)
  have hyp : y ^ p = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexpR (⟨y, hy⟩ : R))
  have hxp : x ^ p = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexpP (⟨x, hx⟩ : P))
  have hzp : z ^ p = 1 := by
    have hc : Commute y z := mem_centralizer_iff.mp hz y hy
    rw [← hyz, hc.mul_pow, hyp, one_mul] at hxp
    exact hxp
  rw [← hyz]
  exact R.mul_mem hy (mem_of_prime_pow_eq_one_of_centralizes_rank_two hmG R hmR hzp hz)

private theorem eq_of_le_extraspecial [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (R P : Subgroup G) [R.Normal]
    [IsExtraspecial p R] (hcardR : Nat.card R = p ^ 3)
    (hPR : P ≤ R) (hmG : primeRank p G ≤ 2)
    (hexpR : Monoid.exponent R ∣ p)
    (hP : IsPGroup p P) (hoP : omega₁ P (p := p) = ⊤)
    (hcP : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P) : R = P := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  rcases lemma_A_1_24 hp2 hP hoP (derived_le_center hcP) hmP with hplane | he
  · let Z := (center R).map R.subtype
    have hcardZ : Nat.card Z = p := by
      rw [card_map_of_injective R.subtype_injective, IsExtraspecial.center_order_p p R]
    let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
    have hZP : Z ≤ P := by
      rintro z ⟨y, hy, rfl⟩
      apply mem_of_prime_pow_eq_one_of_centralizes_rank_two hmG P hmP
      · exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexpR y)
      · intro x hx
        exact congrArg Subtype.val (mem_center_iff.mp hy (⟨x, hPR hx⟩ : R))
    have hphi : frattini P = ⊥ := by
      obtain ⟨e⟩ := hplane.2
      let : IsMulCommutative P :=
        ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
      let : IsElementaryAbelian p P := {
        exponent_dvd_p := exponent_dvd_prime_of_omega_one_eq_top hp2
          (derived_le_center hcP) hoP }
      let : Fact (IsPGroup p P) := ⟨hP⟩
      exact frattini_eq_bot_of_isElementaryAbelian (p := p)
    rcases hirr.normal_le_frattini_or_eq hZP with hb | ht
    · rw [hphi, Subgroup.map_bot] at hb
      have hz : Nat.card Z = 1 := card_eq_one.mpr (bot_unique hb)
      have := (Fact.out : p.Prime).one_lt
      omega
    · have hh : p = p ^ 2 := hcardZ.symm.trans (ht ▸ hplane.1)
      have := (Fact.out : p.Prime).one_lt
      nlinarith
  · exact (eq_of_le_of_card_ge hPR (by rw [hcardR, he.1])).symm

/-- The group-theoretic deduction in A.1.32(2), conditional on triviality of the Frattini action. It includes R = 1 and identifies the actual ambient center image. -/
public theorem rank_two_alternatives_of_frattiniConjugationHom_eq_one [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (R P : Subgroup G) [R.Normal]
    (hR : IsPGroup p R) (hoR : omega₁ R (p := p) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank p R ≤ 2)
    (hP : IsPGroup p P) (hoP : omega₁ P (p := p) = ⊤)
    (hcP : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P) (hmG : primeRank p G = 2)
    (hfix : frattiniConjugationHom P R le_normalizer_of_normal = 1) :
    R = ⊥ ∨ R = P ∨ (Nat.card R = p ∧ Nonempty (R ≃* Multiplicative (ZMod p)) ∧
      Nonempty (P ≃* HeisenbergPrime p) ∧ R = (center P).map P.subtype) := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  have hexpR := exponent_dvd_prime_of_omega_one_eq_top hp2 (derived_le_center hcR) hoR
  have hexpP := exponent_dvd_prime_of_omega_one_eq_top hp2 (derived_le_center hcP) hoP
  by_cases hcomm : ⁅R, P⁆ = ⊥
  · have hRP : R ≤ P := by
      intro x hx
      apply mem_of_prime_pow_eq_one_of_centralizes_rank_two hmG.le P hmP
      · exact congrArg Subtype.val
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexpR (⟨x, hx⟩ : R))
      · exact commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact normal_subgroup_alternatives hp R P hRP hP hoP hcP hmP hirr
  · have hmR2 := rank_eq_two_of_noncentral_frattini_action hp R P hR hoR hcR hmR hfix hcomm
    rcases small_models hp hR hoR hcR hmR with he | ⟨hcard, he, _⟩
    · let := he
      exact (hcomm (centralizes_of_frattiniConjugationHom_eq_one_elementary (r := p) R P hfix)).elim
    · let := he
      have hinner := le_sup_centralizer_of_frattiniConjugationHom_eq_one_extraspecial (r := p) R P hfix
      have hPR := le_of_inner_action R P hmG.le hmR2 hexpR hexpP hinner
      exact Or.inr (Or.inl (eq_of_le_extraspecial hp R P hcard hPR hmG.le hexpR
        hP hoP hcP hmP hirr))

end CFSG.Quasithin.ChapterA.IrreducibleActions
