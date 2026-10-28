module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Hall

/-!
# Prime divisors in the actual paired Hall factors

An odd subgroup of H lies in the index-two component normalizer. The
chosen odd Hall subgroup thus normalizes the component intersection,
where Hall restriction applies. Every odd prime in that overlap divides
the order of the actual Hall factor A ∩ K. Cauchy's theorem supplies a
prime-order element moved by the same Sylow exchange element. The model-indexed construction permits the
independent positive exponent of the literal PSL₂ quotient.

At n(H) = n or 2n, a divisor 2^n(H) - 1 in the component overlap supplies
the prime dividing 2^n - 1 used by the source. That overlap divisor and
PSL₂ recognition at the actual generation minimum remain explicit inputs;
neither follows merely from the paired quotient catalogue.

Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772. These lemmas
feed PrimeExclusion. The parameter-component owner retains the overlap
and recognition proofs, and the linear-geometry owner the final assembly.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- An odd subgroup of H cannot interchange a component pair. -/
theorem ComponentSeed.paired_odd_normalizes (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (A : Subgroup G) (hAH : A ≤ H) (hodd : Odd (Nat.card A)) :
    A ≤ normalizer (K : Set G) := by
  let N := (normalizer (K : Set G)).subgroupOf H
  let B := A.subgroupOf H
  have hi : N.index = 2 := by
    dsimp only [N]
    rw [subgroupOf_normalizer_eq s.component.1]
    exact s.paired_normalizer_index h p hc hs hn
  let : N.Normal := normal_of_index_eq_two hi
  have hd : N.relIndex B ∣ 2 := hi ▸ relIndex_dvd_index_of_normal N B
  have hoB : Odd (Nat.card B) := by
    change Odd (Nat.card (A.subgroupOf H))
    rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]
    exact hodd
  have ho : Odd (N.relIndex B) := hoB.of_dvd_nat (relIndex_dvd_card N B)
  have he : N.relIndex B = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact he
    · exact False.elim ((by decide : ¬ Odd (2 : ℕ)) (he ▸ ho))
  have hBN := relIndex_eq_one.mp he
  intro a ha
  exact hBN (show (⟨a,hAH ha⟩ : H) ∈ B from ha)

/-- Restrict the actual odd Hall subgroup to the component intersection.
The index-two component normalizer supplies the required normalization. -/
theorem ComponentSeed.paired_hall_factor (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    IsHallSubgroup OddHall.oddPrimes
      ((A ⊓ K).subgroupOf ((H ⊓ normalizer (L : Set G)) ⊓ K)) := by
  let B := H ⊓ normalizer (L : Set G)
  have ho : Odd (Nat.card A) := by
    have hh := OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv] at hh
  have hAN := s.paired_odd_normalizes h p hc hs hn A (hA.trans inf_le_left) ho
  have hABK : A ≤ normalizer ((B ⊓ K : Subgroup G) : Set G) :=
    (le_inf (hA.trans B.le_normalizer) hAN).trans inf_normalizer_le_normalizer_inf
  have hh := OddHall.hall_restrict_of_normalizes hHall hA
    (show B ⊓ K ≤ B from inf_le_left) hABK
  have he : A.subgroupOf (B ⊓ K) = (A ⊓ K).subgroupOf (B ⊓ K) := by
    ext x
    exact ⟨fun hx => ⟨hx,x.property.2⟩,fun hx => hx.1⟩
  exact he ▸ hh

/-- An odd prime in the actual component overlap already occurs in the
Hall factor A ∩ K. No order formula or abelian decomposition is assumed. -/
theorem ComponentSeed.paired_hall_factor_prime_dvd (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G)) :
    p ∣ Nat.card (A ⊓ K : Subgroup G) := by
  let B := (H ⊓ normalizer (L : Set G)) ⊓ K
  let C := (A ⊓ K).subgroupOf B
  have hh := s.paired_hall_factor h pr hc hs hn A hA hHall
  have hCI : ¬ p ∣ C.index := fun hd => hh.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hd hp2
  have hd' : p ∣ Nat.card C * C.index := C.card_mul_index.symm ▸ hd
  have hC := (hp.dvd_mul.mp hd').resolve_right hCI
  rwa [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ K ≤ B from
    le_inf (inf_le_left.trans hA) inf_le_right)).toEquiv] at hC

/-- Construct the original Hall subgroup, its Sylow exchange element,
and an actual moved prime-order element of A ∩ K. The prime divisor is
required only in the component overlap, not in a prescribed Hall factor. -/
theorem ComponentSeed.exists_paired_hall_prime_element_of_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G)) :
    ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
      Odd (Nat.card A) ∧ ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
        (t : G) ∉ normalizer (K : Set G) ∧
        Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) ∧
        ∃ x ∈ A ⊓ K, orderOf x = p ∧ (t : G)*x*(t : G)⁻¹ ≠ x := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨A,hA,hHall,ho,t,htA,htK,hdis⟩ :=
    s.paired_linear_hall_exchange_of_model h pr hc hs hn hf hm
  have hpA := s.paired_hall_factor_prime_dvd h pr hc hs hn A hA hHall p hp hp2 hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := (A ⊓ K : Subgroup G)) p hpA
  have hxG : orderOf (x : G) = p := (orderOf_coe x).trans hx
  refine ⟨A,hA,hHall,ho,t,htA,htK,hdis,x,x.property,hxG,?_⟩
  intro he
  have hxC : (x : G) ∈ (A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom :=
    he ▸ mem_map_of_mem _ x.property
  have hx1 : (x : G) = 1 := disjoint_def.mp hdis x.property hxC
  exact hp.ne_one (hxG.symm.trans (hx1 ▸ orderOf_one))

/-- Specialization to the original generation minimum. -/
theorem ComponentSeed.exists_paired_hall_prime_element (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G)) :
    ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
      Odd (Nat.card A) ∧ ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
        (t : G) ∉ normalizer (K : Set G) ∧
        Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) ∧
        ∃ x ∈ A ⊓ K, orderOf x = p ∧ (t : G)*x*(t : G)⁻¹ ≠ x := by
  have hf : 0 < ChapterE.generationParameter H := by
    have := degree_le_parameter h pr hc hs
    have := S.nonbinary
    omega
  exact s.exists_paired_hall_prime_element_of_model h pr hc hs hn hf hm p hp hp2 hd

/-- At either source parameter value, a torus divisor of the component
overlap supplies an odd prime dividing q - 1. The parameter here is the
actual E-generation minimum of H. -/
theorem source_prime_divisor_of_parameter (S : D.NonbinaryNaturalInput)
    (hk : ChapterE.generationParameter H = S.field.degree ∨
      ChapterE.generationParameter H = 2 * S.field.degree)
    (hdiv : 2 ^ ChapterE.generationParameter H - 1 ∣
      Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ S.field.degree - 1 ∧
      p ∣ Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G) := by
  have hn : 2 ≤ S.field.degree := by have := S.nonbinary; omega
  have hpow : 4 ≤ 2 ^ S.field.degree :=
    pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ S.field.degree - 1 ≠ 1)
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have h2 : 2 ∣ 2 ^ S.field.degree := dvd_pow_self 2 (by omega)
    have hx := Nat.mod_eq_zero_of_dvd hd
    have hy := Nat.mod_eq_zero_of_dvd h2
    omega
  have htorus : 2 ^ S.field.degree - 1 ∣ 2 ^ ChapterE.generationParameter H - 1 := by
    rcases hk with he | he
    · rw [he]
    · rw [he, Nat.mul_comm 2 S.field.degree, pow_mul]
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2
  exact ⟨p,hp,hp2,hd,hd.trans (htorus.trans hdiv)⟩

/-- Choose the prime and the actual moved Hall element at either allowed
source parameter. Only the torus divisor in the component overlap remains
explicit; the odd Hall subgroup and its exchange element are constructed. -/
theorem ComponentSeed.exists_paired_hall_prime_element_of_parameter (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (hk : ChapterE.generationParameter H = S.field.degree ∨
      ChapterE.generationParameter H = 2 * S.field.degree)
    (hdiv : 2 ^ ChapterE.generationParameter H - 1 ∣
      Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ S.field.degree - 1 ∧
      ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
        IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
        Odd (Nat.card A) ∧ ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
          (t : G) ∉ normalizer (K : Set G) ∧
          Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) ∧
          ∃ x ∈ A ⊓ K, orderOf x = p ∧ (t : G)*x*(t : G)⁻¹ ≠ x := by
  obtain ⟨p,hp,hp2,hd,ho⟩ := source_prime_divisor_of_parameter S hk hdiv
  exact ⟨p,hp,hp2,hd,s.exists_paired_hall_prime_element h pr hc hs hn hm p hp hp2 ho⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
