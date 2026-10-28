module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Exceptional
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.UnitaryPairSource
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E6
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E7
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E8
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.TwistedE6

/-!
# Higher exceptional source exclusions from actual root charts

Four marked prime-field root directions centralize an actual projective
involution. The odd central covering kernel lifts the rank-four obstruction
to the original group. Proper-section induction supplies its odd center;
no primary-center or quasithin-quotient hypothesis is required.
Source: Aschbacher–Smith A.2.17, printed p.39.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual odd-characteristic E6 carrier contradicts quasithinness. -/
public theorem e6_caseI_false {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (hqt : IsQuasithin G)
    (model : ExceptionalGroup.IsE6 G (r^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hk : iso.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr iso.injective
  exact ExceptionalSplit.OddRankFour.E6.not_quasithin_of_central_cover F r hr2
    iso.toMonoidHom iso.surjective (by rw [hk]; exact bot_le)
    (by rw [hk,card_bot]; decide) hqt

/-- The actual odd-characteristic E7 carrier contradicts quasithinness. -/
public theorem e7_caseI_false {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (hqt : IsQuasithin G)
    (model : ExceptionalGroup.IsE7 G (r^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hk : iso.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr iso.injective
  exact ExceptionalSplit.OddRankFour.E7.not_quasithin_of_central_cover F r hr2
    iso.toMonoidHom iso.surjective (by rw [hk]; exact bot_le)
    (by rw [hk,card_bot]; decide) hqt

/-- The actual odd-characteristic E8 carrier contradicts quasithinness. -/
public theorem e8_caseI_false {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (hqt : IsQuasithin G)
    (model : ExceptionalGroup.IsE8 G (r^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hk : iso.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr iso.injective
  exact ExceptionalSplit.OddRankFour.E8.not_quasithin_of_central_cover F r hr2
    iso.toMonoidHom iso.surjective (by rw [hk]; exact bot_le)
    (by rw [hk,card_bot]; decide) hqt

/-- The literal twisted E₆ carrier is excluded for every odd parameter. -/
public theorem twisted_e6_caseI_false {q : ℕ} (ho : Odd q) (hqt : IsQuasithin G)
    (model : ExceptionalGroup.IsTwistedE6 G q) : False := by
  obtain ⟨r,m,hr,hq,⟨iso⟩⟩ := model
  have hr2 : r ≠ 2 := by
    intro he
    have hd : r ∣ q := by
      rw [← hq]
      exact dvd_pow_self r (Nat.succ_ne_zero m)
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (he ▸ hd))
  have hk : iso.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr iso.injective
  exact TwistedE6.RankFour.not_isQuasithin_of_central_surjection r m hr2
    iso.toMonoidHom iso.surjective (by rw [hk]; exact bot_le)
    (by rw [hk,card_bot]; decide) hqt

variable {K : GroupClass.{u}} {S : Type u} [Group S] [Finite S] {p : ℕ}

/-- The original A.2 counterexample is excluded with only the genuine
proper-section induction, retaining the literal central quotient marking. -/
public theorem e6_caseII_false
    (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremsOnProperSections K G)
    {r e : ℕ} [Fact r.Prime] (hr : Odd r)
    (model : ExceptionalGroup.IsE6 (G ⧸ center G) (r^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  let q := iso.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hk : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ iso.injective,QuotientGroup.ker_mk']
  exact ExceptionalSplit.OddRankFour.E6.not_quasithin_of_central_cover F r hr2
    q (iso.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le
    (hk.symm ▸ h.center_odd_card ih.theoremA) h.1

/-- The original A.2 counterexample is excluded with only the genuine
proper-section induction, retaining the literal central quotient marking. -/
public theorem e7_caseII_false
    (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremsOnProperSections K G)
    {r e : ℕ} [Fact r.Prime] (hr : Odd r)
    (model : ExceptionalGroup.IsE7 (G ⧸ center G) (r^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  let q := iso.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hk : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ iso.injective,QuotientGroup.ker_mk']
  exact ExceptionalSplit.OddRankFour.E7.not_quasithin_of_central_cover F r hr2
    q (iso.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le
    (hk.symm ▸ h.center_odd_card ih.theoremA) h.1

/-- The original A.2 counterexample is excluded with only the genuine
proper-section induction, retaining the literal central quotient marking. -/
public theorem e8_caseII_false
    (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremsOnProperSections K G)
    {r e : ℕ} [Fact r.Prime] (hr : Odd r)
    (model : ExceptionalGroup.IsE8 (G ⧸ center G) (r^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  let q := iso.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hk : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ iso.injective,QuotientGroup.ker_mk']
  exact ExceptionalSplit.OddRankFour.E8.not_quasithin_of_central_cover F r hr2
    q (iso.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le
    (hk.symm ▸ h.center_odd_card ih.theoremA) h.1
/-- The actual twisted E₆ central quotient is excluded on the original
counterexample using the odd center supplied by proper-section induction. -/
public theorem twisted_e6_caseII_false
    (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremsOnProperSections K G) {q : ℕ} (ho : Odd q)
    (model : ExceptionalGroup.IsTwistedE6 (G ⧸ center G) q) : False := by
  obtain ⟨r,m,hr,hq,⟨iso⟩⟩ := model
  have hr2 : r ≠ 2 := by
    intro he
    have hd : r ∣ q := by
      rw [← hq]
      exact dvd_pow_self r (Nat.succ_ne_zero m)
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (he ▸ hd))
  exact TwistedE6.RankFour.not_isQuasithin_of_quotient_equiv r m hr2 iso
    (h.center_odd_card ih.theoremA) h.1
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
