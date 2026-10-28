module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.RankOne
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.EvenCoverLifting.Descent
public import GorensteinWalter.PSL2FourUniversalCover
public import Theory.SpecificGroups.PSL3.BinaryComparison
public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer.BinaryForms
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# Lifting even classical simple quotients

The even PSL₂, PSU₂ and PSp₂ branches, every even PSp₄ branch, and the
PSL₃(2) endpoint identify the whole quasisimple group. They retain the
actual matrix models and use the trivial two-core.
At q = 4 the universal cover is SL₂(5), with kernel C₂; q ≥ 8 uses the
universal identity cover. The binary degree-three case uses PSL₂(7).
The rank-one aliases use genuine matrix equivalences; the PSp₄ branch
uses odd-primary exclusion for arbitrary perfect covers, so needs no
independent two-primary multiplier calculation.

The higher-family adapters descend through the two-primary part of a
universal cover. For SL and SU they produce genuine central quotients of
the concrete group, preserving the coefficient field, dimension, Hermitian
form and Frobenius conjugation. For a two-group universal kernel they give
an isomorphism to the projective model itself. Their multiplier premises
remain explicit: the full implication from `IsEvenLieQuotient` to
`IsEvenLieGroup` still requires the remaining family calculations.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74, B.4.4 and K.3;
GLS3, Section 6.1, Theorem 6.1.4 and Tables 6.1.2–6.1.3. The exceptional
matrix comparisons reuse the attributed ATLAS ports through the imports.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

/-- The exceptional double cover at q = 4 becomes trivial over a target
with trivial two-core, identifying the whole group with its PSL₂(4) model. -/
theorem isPSL_of_rank_one_four (hcore : pCore 2 L = ⊥)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 4) : ClassicalGroup.IsPSL L 2 4 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  have hp : IsPGroup 2 (GorensteinWalter.PSL2Cover.fourCover F hcard).toMonoidHom.ker := by
    apply IsPGroup.of_card (n := 1)
    have hc := Nat.card_congr
      (GorensteinWalter.PSL2Cover.fourKernelEquivTwo F hcard).toEquiv
    change Nat.card (GorensteinWalter.PSL2Cover.fourCover F hcard).toMonoidHom.ker =
      Nat.card (ZMod 2) at hc
    simpa only [pow_one, Nat.card_zmod] using hc
  exact ⟨F, hF, hfin, hcard,
    nonempty_mulEquiv_of_universal_two_kernel hcore
      (GorensteinWalter.PSL2Cover.fourCover F hcard)
      (GorensteinWalter.PSL2Cover.fourCover_isUniversal F hcard) hp e⟩

/-- All permitted even PSL₂ parameters lift to the same actual PSL₂ model. -/
theorem isPSL_of_even_psl2 (hcore : pCore 2 L = ⊥)
    {q : ℕ} (hp : KnownSimple.LinearParameters 2 q) (he : Even q)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q) : ClassicalGroup.IsPSL L 2 q := by
  by_cases h4 : q = 4
  · subst q
    exact isPSL_of_rank_one_four hcore h
  have hq : 8 ≤ q := by
    obtain ⟨p, a, hprime, ha, hpa⟩ := (isPrimePow_nat_iff q).mp hp.1
    have hd : 2 ∣ p := (by decide : Nat.Prime 2).dvd_of_dvd_pow
      (hpa.symm ▸ even_iff_two_dvd.mp he)
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (by decide) hprime).mp hd |>.symm
    subst p
    have ha3 : 3 ≤ a := by
      by_contra hh
      have ha2 : a ≤ 2 := by omega
      interval_cases a <;> norm_num at hpa <;> have := hp.2.2 rfl <;> omega
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha3
      _ = q := hpa
  exact isPSL_of_even_rank_one hq he h

/-- The complete even rank-one branch has the whole-group Lie-type output. -/
theorem isEvenLieGroup_of_even_psl2 (hcore : pCore 2 L = ⊥)
    {q : ℕ} (hp : KnownSimple.LinearParameters 2 q) (he : Even q)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q) : IsEvenLieGroup L :=
  .classical ((IsClassicalAt.linear 2 hp
    (isPSL_of_even_psl2 hcore hp he h)).isEvenClassicalGroup he)

/-- The binary degree-three endpoint follows through PSL₂(7) and its
universal double cover, whose kernel dies in the trivial two-core. -/
theorem isPSL_of_psl3_two (hcore : pCore 2 L = ⊥)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 3 2) : ClassicalGroup.IsPSL L 3 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hseven : ClassicalGroup.IsPSL (L ⧸ center L) 2 7 :=
    ⟨ZMod 7, inferInstance, inferInstance, Nat.card_zmod 7,
      ⟨e.trans (Matrix.PSL3.binaryEquivPsl2Seven F hcard)⟩⟩
  obtain ⟨K, hK, hfinK, hcardK, ⟨a⟩⟩ := isPSL_of_odd_rank_one hcore
    (by decide : 3 < 7) (by decide : Odd 7) (by decide : 7 ≠ 9) hseven
  exact ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
    ⟨a.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two hcardK)⟩⟩

/-- The binary degree-three endpoint gives an actual whole-group Lie model. -/
theorem isEvenLieGroup_of_psl3_two (hcore : pCore 2 L = ⊥)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 3 2) : IsEvenLieGroup L := by
  have hp : KnownSimple.LinearParameters 3 2 :=
    ⟨(isPrimePow_nat_iff 2).mpr ⟨2, 1, by decide, by decide, by decide⟩,
      by decide, by omega⟩
  exact .classical ((IsClassicalAt.linear 3 hp
    (isPSL_of_psl3_two hcore h)).isEvenClassicalGroup (by decide))

/-- Rank-one symplectic models lift through their actual PSL₂ comparison. -/
theorem isPSp_of_even_rank_one (hcore : pCore 2 L = ⊥)
    {q : ℕ} (hp : KnownSimple.SymplecticParameters 1 q) (he : Even q)
    (h : ClassicalGroup.IsPSp (L ⧸ center L) 1 q) : ClassicalGroup.IsPSp L 1 q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  have hlin : ClassicalGroup.IsPSL (L ⧸ center L) 2 q :=
    ⟨F, hF, hfin, hc, ⟨e.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩
  have hpar : KnownSimple.LinearParameters 2 q := ⟨hp.1, by decide, fun _ => hp.2.2.1 rfl⟩
  obtain ⟨K, hK, hfinK, hcK, ⟨a⟩⟩ := isPSL_of_even_psl2 hcore hpar he hlin
  exact ⟨K, hK, hfinK, hcK,
    ⟨a.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv.symm⟩⟩

/-- The whole-group output for every even rank-one symplectic catalogue row. -/
theorem isEvenLieGroup_of_even_psp_rank_one (hcore : pCore 2 L = ⊥)
    {q : ℕ} (hp : KnownSimple.SymplecticParameters 1 q) (he : Even q)
    (h : ClassicalGroup.IsPSp (L ⧸ center L) 1 q) : IsEvenLieGroup L :=
  .classical (.symplectic 1 q hp he (isPSp_of_even_rank_one hcore hp he h))

/-- The actual fixed field reduces PSU₂ to PSL₂; field transport returns
the lifted isomorphism to the original Hermitian projective model. -/
theorem isPSU_of_even_rank_one (hcore : pCore 2 L = ⊥)
    {q : ℕ} (hp : KnownSimple.UnitaryParameters 2 q) (he : Even q)
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 2 q) : ClassicalGroup.IsPSU L 2 q := by
  obtain ⟨p, d, hprime, hd, hpow⟩ := (isPrimePow_nat_iff q).mp hp.1
  have hdiv : 2 ∣ p := (by decide : Nat.Prime 2).dvd_of_dvd_pow
    (hpow.symm ▸ even_iff_two_dvd.mp he)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (by decide) hprime).mp hdiv |>.symm
  subst p
  obtain ⟨F, hF, hfin, J, hc, hj, ⟨e⟩⟩ := h
  have hcard : Nat.card F = (2 ^ d) ^ 2 := hc.trans (congrArg (fun x => x ^ 2) hpow.symm)
  have hconj : ∀ x, J.conj x = x ^ (2 ^ d) := by simpa only [hpow] using hj
  let : CharP F 2 := Theory.SpecificGroups.UnitaryRootNormalizer.charP_binary hd hcard
  have hfixed := Theory.SpecificGroups.UnitaryRootNormalizer.fixed_card_binary J hd hcard hconj
  have hfixedq : Nat.card {x : F // J.conj x = x} = q := hfixed.trans hpow
  obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryRootNormalizer.nonempty_projectiveTwoEquiv J hc hfixedq
  let F0 := FixedBy.subfield F J.conj
  have hc0 : Nat.card F0 = q := hfixedq
  have hlin : ClassicalGroup.IsPSL (L ⧸ center L) 2 q :=
    ⟨F0, inferInstance, inferInstance, hc0, ⟨e.trans a⟩⟩
  have hpar : KnownSimple.LinearParameters 2 q := ⟨hp.1, hp.2.1, hp.2.2.1⟩
  obtain ⟨K, hK, hfinK, hcK, ⟨b⟩⟩ := isPSL_of_even_psl2 hcore hpar he hlin
  let : Fintype K := Fintype.ofFinite K
  let : Fintype F0 := Fintype.ofFinite F0
  let t : K ≃+* F0 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcK.trans hc0.symm)
  exact ⟨F, hF, hfin, J, hc, hj,
    ⟨(b.trans (Atlas.fieldEquivPSL 2 t)).trans a.symm⟩⟩

/-- The whole-group output for every even degree-two unitary catalogue row. -/
theorem isEvenLieGroup_of_even_psu2 (hcore : pCore 2 L = ⊥)
    {q : ℕ} (hp : KnownSimple.UnitaryParameters 2 q) (he : Even q)
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 2 q) : IsEvenLieGroup L :=
  .classical ((IsClassicalAt.unitary 2 hp
    (isPSU_of_even_rank_one hcore hp he h)).isEvenClassicalGroup he)

/-- Odd-primary exclusion for perfect Sp₄ covers and the trivial two-core
kill every prime divisor of the actual component-to-model kernel. This
includes the field-four endpoint and needs no two-primary multiplier theorem. -/
theorem isPSp_of_even_rank_two (hcore : pCore 2 L = ⊥)
    {q : ℕ} (he : Even q)
    (h : ClassicalGroup.IsPSp (L ⧸ center L) 2 q) : ClassicalGroup.IsPSp L 2 q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := by
    apply ringChar.of_eq
    apply FiniteField.even_card_iff_char_two.mpr
    rw [← Nat.card_eq_fintype_card, hc]
    exact Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp he)
  let s := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  let g := s.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hsurj : Function.Surjective g :=
    s.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : g.ker = center L := by
    dsimp only [g]
    rw [MonoidHom.ker_comp_of_injective _ _ s.injective, QuotientGroup.ker_mk']
  have hbot : g.ker = ⊥ := by
    apply Subgroup.card_eq_one.mp
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    by_cases htwo : p = 2
    · subst p
      exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        hcore g.ker (le_of_eq hk)
    · exact Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.not_dvd_card_kernel
        htwo g hsurj (le_of_eq hk)
  let a := MulEquiv.ofBijective g ⟨g.ker_eq_bot_iff.mp hbot, hsurj⟩
  exact ⟨F, hF, hfin, hc,
    ⟨a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv⟩⟩

/-- Every permitted even PSp₄ quotient has the actual whole-group model. -/
theorem isEvenLieGroup_of_even_psp_rank_two (hcore : pCore 2 L = ⊥)
    {q : ℕ} (hp : KnownSimple.SymplecticParameters 2 q) (he : Even q)
    (h : ClassicalGroup.IsPSp (L ⧸ center L) 2 q) : IsEvenLieGroup L :=
  .classical (.symplectic 2 q hp he (isPSp_of_even_rank_two hcore he h))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
