module
public import Theory.SpecificGroups.LieType.TwoRankLower.BinaryExceptional
public import CFSG.KnownSimple.ExceptionalModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
/-!
# Characteristic-two exceptional exclusions in the original A.2 rank-two branch

Actual Sp6(2) embeddings exclude all five large exceptional carriers at every
positive binary parameter. The source applications use precisely the proved
two-rank bound for S/Z(S); neither quotient quasithinness nor a local section
is assumed.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The full binary F4 model is absent from the ordinary two-rank-two list. -/
theorem no_binary_f4_model (hr : primeRank 2 Q ≤ 2) {a : ℕ}
    (model : ExceptionalGroup.IsF4 Q (2 ^ a)) : False := by
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hb := Theory.SpecificGroups.LieType.TwoRank.f4_three_le F
  rw [← primeRank_equiv 2 e] at hb
  omega

/-- The full binary E6 model is absent from the ordinary two-rank-two list. -/
theorem no_binary_e6_model (hr : primeRank 2 Q ≤ 2) {a : ℕ}
    (model : ExceptionalGroup.IsE6 Q (2 ^ a)) : False := by
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hb := Theory.SpecificGroups.LieType.TwoRank.e6_three_le F
  rw [← primeRank_equiv 2 e] at hb
  omega

/-- The full binary E7 model is absent from the ordinary two-rank-two list. -/
theorem no_binary_e7_model (hr : primeRank 2 Q ≤ 2) {a : ℕ}
    (model : ExceptionalGroup.IsE7 Q (2 ^ a)) : False := by
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hb := Theory.SpecificGroups.LieType.TwoRank.e7_three_le F
  rw [← primeRank_equiv 2 e] at hb
  omega

/-- The full binary E8 model is absent from the ordinary two-rank-two list. -/
theorem no_binary_e8_model (hr : primeRank 2 Q ≤ 2) {a : ℕ}
    (model : ExceptionalGroup.IsE8 Q (2 ^ a)) : False := by
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hb := Theory.SpecificGroups.LieType.TwoRank.e8_three_le F
  rw [← primeRank_equiv 2 e] at hb
  omega

/-- The actual binary twisted E6 carrier is likewise excluded. -/
theorem no_binary_twisted_e6_model (hr : primeRank 2 Q ≤ 2) {a : ℕ}
    (model : ExceptionalGroup.IsTwistedE6 Q (2 ^ a)) : False := by
  obtain ⟨p,m,hp,hc,⟨e⟩⟩ := model
  have hd : p ∣ 2 ^ a := by
    rw [← hc]
    exact dvd_pow_self p (by omega : m + 1 ≠ 0)
  have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
    (hp.out.dvd_of_dvd_pow hd)
  subst p
  have hb := Theory.SpecificGroups.LieType.TwoRank.twisted_e6_three_le m
  rw [← primeRank_equiv 2 e] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p a : ℕ}

/-- The original source central quotient cannot be binary F4. -/
theorem CounterexampleToTheoremA.centralQuotient_no_binary_f4_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsF4 (S ⧸ center S) (2 ^ a)) : False :=
  Nonsemisimple.RankTwoSieve.no_binary_f4_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model

/-- The original source central quotient cannot be binary E6. -/
theorem CounterexampleToTheoremA.centralQuotient_no_binary_e6_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsE6 (S ⧸ center S) (2 ^ a)) : False :=
  Nonsemisimple.RankTwoSieve.no_binary_e6_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model

/-- The original source central quotient cannot be binary E7. -/
theorem CounterexampleToTheoremA.centralQuotient_no_binary_e7_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsE7 (S ⧸ center S) (2 ^ a)) : False :=
  Nonsemisimple.RankTwoSieve.no_binary_e7_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model

/-- The original source central quotient cannot be binary E8. -/
theorem CounterexampleToTheoremA.centralQuotient_no_binary_e8_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsE8 (S ⧸ center S) (2 ^ a)) : False :=
  Nonsemisimple.RankTwoSieve.no_binary_e8_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model

/-- The original source central quotient cannot be binary TwistedE6. -/
theorem CounterexampleToTheoremA.centralQuotient_no_binary_twisted_e6_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsTwistedE6 (S ⧸ center S) (2 ^ a)) : False :=
  Nonsemisimple.RankTwoSieve.no_binary_twisted_e6_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model

end CFSG.Quasithin.ChapterA.Section02
