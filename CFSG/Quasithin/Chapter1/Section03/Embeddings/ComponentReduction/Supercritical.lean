module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Quotient
public import Theory.GroupTheory.PGroup.Supercritical
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.Quasithin.Rank

/-!
# Supercritical applications in the intrinsic Ξ reduction

The complement embeds in H/O₂(H), and its Frattini quotient intertwines
conjugation by N_T(P) with conjugation by its quotient image. Thus the full
normalizer of the image is irreducible. Odd prime ranks descend through O₂(H),
and the elementary/extraspecial complement has rank two, first omega equal
to itself, and nilpotency class at most two.

Apply A.1.32 to the image of a supercritical subgroup of each odd prime core.
For r ≠ p the complement centralizes that subgroup; coprime automorphism
detection from A.1.21(3) extends this to the core. If the p-core is noncyclic,
A.1.21(4) gives supercritical rank greater than one, excluding the order-p
alternative of A.1.32(2). The complement image is then characteristic in a
normal core, hence normal. Trivial cores require no supercritical choice.

This is a conditional application helper. The four explicitly universal
earlier-result implications remain parameters for the source assembly owner;
neither normality nor FittingConditions is an input. No Sylow hypothesis on
T in H or identification of the images of X and P is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed pp.509–510;
Definition A.1.20 and Lemma A.1.21, pp.24–25; Lemma A.1.32, pp.28–29.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

private theorem frattini_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    refine ⟨e.symm b, frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hb, e.apply_symm_apply b⟩

/-- The complement embedding identifies its actual Frattini quotients. -/
noncomputable def LocalInput.quotientComplementFrattiniEquiv
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H) :
    (P ⧸ frattini P) ≃* (quotientImage H P ⧸ frattini (quotientImage H P)) :=
  QuotientGroup.congr _ _ h.quotientComplementEquiv (by exact frattini_map_equiv _)

/-- The Frattini equivalence is induced by the actual complement embedding. -/
theorem LocalInput.quotientComplementFrattiniEquiv_apply_mk
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H) (a : P) :
    h.quotientComplementFrattiniEquiv (QuotientGroup.mk' (frattini P) a) =
      QuotientGroup.mk' (frattini (quotientImage H P)) (h.quotientComplementEquiv a) := rfl

/-- The quotient map sends N_T(P) into the normalizer of the complement image. -/
def LocalInput.quotientNormalizerHom
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H) :
    (T ⊓ normalizer P : Subgroup G) →* normalizer (quotientImage H P : Set (XiQuotient H)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : (T ⊓ normalizer P : Subgroup G) →* H :=
    inclusion (inf_le_left.trans (le_sup_right.trans h.overgroup))
  refine (q.comp f).codRestrict _ ?_
  intro s
  apply (P.subgroupOf H).le_normalizer_map q
  apply mem_map_of_mem
  apply mem_normalizer_iff.mpr
  intro a
  exact mem_normalizer_iff.mp s.property.2 a

/-- The Frattini equivalence intertwines the actual conjugation actions. -/
theorem LocalInput.quotientComplementFrattiniEquiv_equivariant
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (s : (T ⊓ normalizer P : Subgroup G)) (a : P ⧸ frattini P) :
    h.quotientComplementFrattiniEquiv
      (frattiniConjugationAction _ _ inf_le_right s a) =
    frattiniConjugationAction (normalizer (quotientImage H P : Set (XiQuotient H))) _ le_rfl
      (h.quotientNormalizerHom s) (h.quotientComplementFrattiniEquiv a) := by
  induction a using QuotientGroup.induction_on with | H a =>
    change h.quotientComplementFrattiniEquiv
      (frattiniConjugationAction _ _ inf_le_right s (QuotientGroup.mk' _ a)) =
      frattiniConjugationAction (normalizer (quotientImage H P : Set (XiQuotient H))) _ le_rfl
        (h.quotientNormalizerHom s)
          (h.quotientComplementFrattiniEquiv (QuotientGroup.mk' _ a))
    simp only [frattiniConjugationAction, MonoidHom.comp_apply,
      LocalInput.quotientComplementFrattiniEquiv_apply_mk, quotientAut_apply_mk]
    apply congrArg (QuotientGroup.mk' _)
    apply Subtype.ext
    change QuotientGroup.mk' (pCore 2 H)
      (⟨(s : G) * (a : G) * (s : G)⁻¹, _⟩ : H) =
      QuotientGroup.mk' (pCore 2 H) (⟨s, _⟩ : H) *
        QuotientGroup.mk' (pCore 2 H) (⟨a, _⟩ : H) *
          (QuotientGroup.mk' (pCore 2 H) (⟨s, _⟩ : H))⁻¹
    simp only [← map_mul, ← map_inv]
    rfl

/-- Irreducibility under N_T(P) gives irreducibility under the full quotient normalizer. -/
theorem LocalInput.quotient_normalizer_irreducible
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H) :
    ∀ A : Subgroup (quotientImage H P ⧸ frattini (quotientImage H P)),
      (∀ s : normalizer (quotientImage H P : Set (XiQuotient H)), ∀ a ∈ A,
        frattiniConjugationAction (normalizer (quotientImage H P : Set (XiQuotient H))) _ le_rfl s a ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  intro A hA
  let e := h.quotientComplementFrattiniEquiv
  have hinv : ∀ s : (T ⊓ normalizer P : Subgroup G), ∀ a ∈ A.comap e.toMonoidHom,
      frattiniConjugationAction _ _ inf_le_right s a ∈ A.comap e.toMonoidHom := by
    intro s a ha
    change e (frattiniConjugationAction _ _ inf_le_right s a) ∈ A
    rw [h.quotientComplementFrattiniEquiv_equivariant]
    exact hA _ _ ha
  rcases h.irreducible (A.comap e.toMonoidHom) hinv with hb | ht
  · left
    have hm := congrArg (Subgroup.map e.toMonoidHom) hb
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      Subgroup.map_bot] using hm
  · right
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm

/-- Odd prime rank in the quotient by the actual two-core. -/
theorem quotient_primeRank_le [Finite G] (H : Subgroup G) {r : ℕ}
    (hr : r.Prime) (ho : Odd r) : primeRank r (XiQuotient H) ≤ primeRank r H := by
  let _ : Fact r.Prime := ⟨hr⟩
  exact primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup

/-- Strong quasithinness descends through the normal two-core. -/
theorem quotient_stronglyQuasithin [Finite G] {H : Subgroup G}
    (hH : IsStronglyQuasithin H) : IsStronglyQuasithin (XiQuotient H) :=
  fun r hr ho => (quotient_primeRank_le H hr ho).trans (hH r hr ho)

private theorem cyclic_of_odd_primeRank_le_one {Y : Type*} [Group Y] [Finite Y]
    {r : ℕ} [Fact r.Prime] (hr : Odd r) (hY : IsPGroup r Y)
    (hm : primeRank r Y ≤ 1) : IsCyclic Y := by
  apply hY.isCyclic_of_odd_of_elementary_card_le hr
  intro E he
  let _ := he
  exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hm E

/-- The quotient complement has rank exactly two, including its extraspecial case. -/
theorem LocalInput.quotient_complement_primeRank [Finite G]
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsStronglyQuasithin H) : primeRank p (quotientImage H P) = 2 := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  have hu := (primeRank_subgroup_le p (quotientImage H P)).trans
    (quotient_stronglyQuasithin hH p h.prime h.odd)
  have hl : ¬ primeRank p (quotientImage H P) ≤ 1 := fun hm =>
    h.quotient_complement_not_cyclic
      (cyclic_of_odd_primeRank_le_one h.odd h.quotient_odd_complement.isPGroup hm)
  omega

/-- The full quotient has p-rank two because it contains the embedded complement. -/
theorem LocalInput.quotient_primeRank [Finite G]
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsStronglyQuasithin H) : primeRank p (XiQuotient H) = 2 := by
  apply le_antisymm (quotient_stronglyQuasithin hH p h.prime h.odd)
  exact (h.quotient_complement_primeRank hH).ge.trans (primeRank_subgroup_le p _)

private theorem xiOdd_exponent_dvd {Y : Type*} [Group Y] {p : ℕ}
    (h : XiOddQuotient p Y) : Monoid.exponent Y ∣ p := by
  rcases h with ⟨he, _⟩ | ⟨_, _, hx⟩
  · exact he.exponent_dvd_p
  · rw [hx]

private theorem xiOdd_lowerCentralSeries_two {Y : Type*} [Group Y] {p : ℕ}
    (h : XiOddQuotient p Y) : (⊤ : Subgroup Y).lowerCentralSeries 2 = ⊥ := by
  have hd : _root_.commutator Y ≤ center Y := by
    rcases h with ⟨he, _⟩ | ⟨he, _, _⟩
    · let _ := he
      rw [commutator_eq_bot]
      exact bot_le
    · let _ := he.quotient_elementary_abelian
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rw [show 2 = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ, top_lowerCentralSeries_one]
  exact bot_unique ((commutator_mono hd le_rfl).trans (commutator_center_left ⊤).le)

/-- The two defining complement types satisfy the omega and class hypotheses of A.1.32. -/
theorem LocalInput.quotient_complement_omega_class
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H) :
    omega₁ (quotientImage H P) (p := p) = ⊤ ∧
      (⊤ : Subgroup (quotientImage H P)).lowerCentralSeries 2 = ⊥ := by
  refine ⟨?_, xiOdd_lowerCentralSeries_two h.quotient_odd_complement⟩
  apply top_unique
  intro x _
  apply Subgroup.subset_closure
  change x ^ (p ^ 1) = 1
  simpa only [pow_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (xiOdd_exponent_dvd h.quotient_odd_complement) x

/-- The universal existence clause A.1.21(1), with the trivial p-group included. -/
def SupercriticalExistence : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], Odd r → ∀ (Y : Type u) [Group Y] [Finite Y],
    IsPGroup r Y → ∃ D : Subgroup Y, IsSupercriticalPSubgroup r D

/-- The pointwise-detection implication of A.1.21(3). Faithfulness on D/Φ(D)
implies this: a coprime automorphism fixing D pointwise is the identity. -/
def SupercriticalCoprimeDetection : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], Odd r → ∀ (Y : Type u) [Group Y] [Finite Y],
    IsPGroup r Y → ∀ (D : Subgroup Y), IsSupercriticalPSubgroup r D →
    ∀ a : MulAut Y, Nat.Coprime (orderOf a) r →
      (∀ d : D, a (d : Y) = (d : Y)) → a = 1

/-- The universal rank implication A.1.21(4). -/
def SupercriticalRankDetection : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], Odd r → ∀ (Y : Type u) [Group Y] [Finite Y],
    IsPGroup r Y → ∀ (D : Subgroup Y), IsSupercriticalPSubgroup r D →
      1 < primeRank r Y → 1 < primeRank r D

/-- Exactly the two implications used from A.1.32, with all its input
conditions retained. The second excludes R = 1, omitted in the printed
statement. The unused inner-action and extraspecial conclusions are not
claimed here. This universal proposition is an earlier-result parameter,
not a hypothesis of the local Ξ configuration. -/
def RankTwoActionImplications : Prop :=
  ∀ (r p : ℕ) [Fact r.Prime] [Fact p.Prime], Odd r → Odd p →
    ∀ (Y : Type u) [Group Y] [Finite Y] (R P : Subgroup Y),
      R.Normal → IsPGroup r R → omega₁ R (p := r) = ⊤ →
      (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥ → primeRank r R ≤ 2 →
      IsPGroup p P → omega₁ P (p := p) = ⊤ →
      (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ → primeRank p P = 2 →
      (∀ A : Subgroup (P ⧸ frattini P),
        (∀ s : normalizer (P : Set Y), ∀ a ∈ A,
          frattiniConjugationAction (normalizer (P : Set Y)) P le_rfl s a ∈ A) →
        A = ⊥ ∨ A = ⊤) →
      (r ≠ p → ⁅R, P⁆ = ⊥) ∧
        (r = p → primeRank p Y = 2 → R ≠ ⊥ → R = P ∨ Nat.card R = p)

private theorem supercritical_map_data {Y : Type u} [Group Y] [Finite Y]
    {r : ℕ} (N : Subgroup Y) [N.Normal] (hN : IsPGroup r N)
    (D : Subgroup N) (hD : IsSupercriticalPSubgroup r D)
    (hrank : primeRank r Y ≤ 2) :
    let R := D.map N.subtype
    R.Normal ∧ IsPGroup r R ∧ omega₁ R (p := r) = ⊤ ∧
      (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥ ∧ primeRank r R ≤ 2 := by
  let R := D.map N.subtype
  let e : D ≃* R := D.equivMapOfInjective N.subtype N.subtype_injective
  let _ : D.Characteristic := hD.characteristic
  refine ⟨ConjAct.normal_of_characteristic_of_normal, (hN.to_subgroup D).map _,
    ?_, ?_, (primeRank_subgroup_le r R).trans hrank⟩
  · apply top_unique
    intro x _
    apply Subgroup.subset_closure
    change x ^ (r ^ 1) = 1
    simpa only [pow_one, map_pow, map_one, e.apply_symm_apply] using
      congrArg e (hD.pow_eq_one (e.symm x))
  · have hm := congrArg (Subgroup.map e.toMonoidHom) hD.lowerCentralSeries_two
    simpa only [Subgroup.map_lowerCentralSeries,
      map_top_of_surjective e.toMonoidHom e.surjective, Subgroup.map_bot] using hm

private theorem primeRank_le_one_of_cyclic {Y : Type*} [Group Y] [Finite Y]
    {r : ℕ} [Fact r.Prime] (hY : IsCyclic Y) : primeRank r Y ≤ 1 := by
  classical
  let _ := hY
  let S : Sylow r Y := Classical.choice inferInstance
  exact S.primeRank_le_one_of_isCyclic inferInstance

/-- Applying A.1.21 and A.1.32 to the actual p-core gives the normal-or-cyclic
alternative. The noncyclic-core branch forces the supercritical subgroup to
be the complement image, so its characteristic normality proves the result. -/
theorem LocalInput.quotient_normal_or_cyclic_core [Finite G]
    (hA121_1 : SupercriticalExistence.{u})
    (hA121_4 : SupercriticalRankDetection.{u})
    (hA132 : RankTwoActionImplications.{u})
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsStronglyQuasithin H) :
    (quotientImage H P).Normal ∨ IsCyclic (pCore p (XiQuotient H)) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  by_cases hc : IsCyclic (pCore p (XiQuotient H))
  · exact Or.inr hc
  left
  let N := pCore p (XiQuotient H)
  obtain ⟨D, hD⟩ := hA121_1 p h.odd N pCore_isPGroup
  have hnrank : 1 < primeRank p N := by
    by_contra hm
    exact hc (cyclic_of_odd_primeRank_le_one (Y := N) h.odd pCore_isPGroup
      (Nat.le_of_not_gt hm))
  have hdrank := hA121_4 p h.odd N pCore_isPGroup D hD hnrank
  let R := D.map N.subtype
  let e : D ≃* R := D.equivMapOfInjective N.subtype N.subtype_injective
  have hRrank : 1 < primeRank p R := by
    rwa [← primeRank_congr p e]
  have hRne : R ≠ ⊥ := by
    intro he
    have hm := primeRank_le_nat_card (G := R) p
    have hcard : Nat.card R = 1 := by rw [he]; exact Subgroup.card_bot
    omega
  obtain ⟨hn, hpR, hoR, hcR, hmR⟩ := supercritical_map_data N pCore_isPGroup D hD
    (quotient_stronglyQuasithin hH p h.prime h.odd)
  have hact := hA132 p p h.odd h.odd (XiQuotient H) R (quotientImage H P)
    hn hpR hoR hcR hmR h.quotient_odd_complement.isPGroup
    h.quotient_complement_omega_class.1 h.quotient_complement_omega_class.2
    (h.quotient_complement_primeRank hH) h.quotient_normalizer_irreducible
  rcases hact.2 rfl (h.quotient_primeRank hH) hRne with he | he
  · exact he ▸ hn
  · have hcyc : IsCyclic R := isCyclic_of_prime_card he
    exact (not_le_of_gt hRrank (primeRank_le_one_of_cyclic hcyc)).elim

/-- Coprime detection extends pointwise centralization of the actual
supercritical subgroup to its entire prime core. -/
private theorem centralizes_core_of_supercritical
    (hA121_3 : SupercriticalCoprimeDetection.{u})
    {Y : Type u} [Group Y] [Finite Y] {r p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hr : Odd r) (hrp : r ≠ p) (N P : Subgroup Y) [N.Normal]
    (hN : IsPGroup r N) (hP : IsPGroup p P)
    (D : Subgroup N) (hD : IsSupercriticalPSubgroup r D)
    (hc : ⁅D.map N.subtype, P⁆ = ⊥) : P ≤ centralizer (N : Set Y) := by
  let _ := conjMulDistribMulActionOfLeNormalizer P N le_normalizer_of_normal
  let ρ : P →* MulAut N := MulDistribMulAction.toMulAut P N
  have hcop : Nat.Coprime p r := (Nat.coprime_primes Fact.out Fact.out).mpr hrp.symm
  have hcent : P ≤ centralizer (D.map N.subtype : Set Y) := by
    exact le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hc)
  intro a ha
  have hid : ρ (⟨a, ha⟩ : P) = 1 := by
    apply hA121_3 r hr N hN D hD
    · exact (hP.orderOf_coprime hcop (⟨a, ha⟩ : P)).coprime_dvd_left
        (orderOf_map_dvd ρ _)
    · intro d
      apply Subtype.ext
      change a * (d : Y) * a⁻¹ = (d : Y)
      have he := (mem_centralizer_iff.mp (hcent ha)) (d : Y)
        (mem_map_of_mem N.subtype d.property)
      calc
        a * (d : Y) * a⁻¹ = (d : Y) * a * a⁻¹ := by rw [he]
        _ = (d : Y) := mul_inv_cancel_right _ _
  apply mem_centralizer_iff.mpr
  intro n hn
  have he := congrArg (fun b : MulAut N => ((b ⟨n, hn⟩ : N) : Y)) hid
  change a * n * a⁻¹ = n at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Every other odd prime core is centralized by the actual complement image.
The zero-core case is discharged before invoking supercritical existence. -/
theorem LocalInput.quotient_centralizes_other_cores [Finite G]
    (hA121_1 : SupercriticalExistence.{u})
    (hA121_3 : SupercriticalCoprimeDetection.{u})
    (hA132 : RankTwoActionImplications.{u})
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsStronglyQuasithin H) :
    ∀ r : ℕ, r.Prime → Odd r → r ≠ p →
      quotientImage H P ≤ centralizer (pCore r (XiQuotient H) : Set (XiQuotient H)) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  intro r hr ho hrp
  let _ : Fact r.Prime := ⟨hr⟩
  by_cases hz : pCore r (XiQuotient H) = ⊥
  · rw [hz]
    intro a _
    apply mem_centralizer_iff.mpr
    intro b hb
    have hb1 : b = 1 := hb
    simp only [hb1, one_mul, mul_one]
  let N := pCore r (XiQuotient H)
  obtain ⟨D, hD⟩ := hA121_1 r ho N pCore_isPGroup
  obtain ⟨hn, hpR, hoR, hcR, hmR⟩ := supercritical_map_data N pCore_isPGroup D hD
    (quotient_stronglyQuasithin hH r hr ho)
  have hact := hA132 r p ho h.odd (XiQuotient H) (D.map N.subtype) (quotientImage H P)
    hn hpR hoR hcR hmR h.quotient_odd_complement.isPGroup
    h.quotient_complement_omega_class.1 h.quotient_complement_omega_class.2
    (h.quotient_complement_primeRank hH) h.quotient_normalizer_irreducible
  exact centralizes_core_of_supercritical hA121_3 ho hrp N (quotientImage H P)
    pCore_isPGroup h.quotient_odd_complement.isPGroup D hD (hact.1 hrp)

/-- The supercritical/Fitting step of the intrinsic Ξ reduction. Only the
universal earlier-result implications A.1.21 and A.1.32 are parameters;
all their hypotheses for this quotient and its actual cores are proved here. -/
theorem LocalInput.quotient_normal_or_fitting [Finite G]
    (hA121_1 : SupercriticalExistence.{u})
    (hA121_3 : SupercriticalCoprimeDetection.{u})
    (hA121_4 : SupercriticalRankDetection.{u})
    (hA132 : RankTwoActionImplications.{u})
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsStronglyQuasithin H) :
    (quotientImage H P).Normal ∨ FittingConditions p P H := by
  rcases h.quotient_normal_or_cyclic_core hA121_1 hA121_4 hA132 hH with hn | hc
  · exact Or.inl hn
  · exact Or.inr ⟨hc, h.quotient_centralizes_other_cores hA121_1 hA121_3 hA132 hH⟩

end CFSG.Quasithin.Chapter1.XiEmbedding
