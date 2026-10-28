module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleCase
public import CFSG.KnownSimple.ExceptionalModels
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.ReeOddCover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer.OddCover

/-!
# The actual Ree and F₄ source exclusions

The complete concrete odd-cover theorems exclude every large Ree and every
odd-characteristic F₄ carrier in both source cases. Case II retains the
original quasisimple counterexample, its prime-group center and the actual
central-quotient marking. The prime is odd by the original Theorem-A
failure witness. No quasithinness of a quotient is assumed.

Source: Aschbacher–Smith, A.2.13 and A.2.17, printed pp.37–39.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full large Ree carrier is excluded from source Case I by the actual
involution-centralizer rank witness. -/
public theorem ree_caseI_false {q : ℕ} (hqt : IsQuasithin G)
    (model : ExceptionalGroup.IsReeG2 G q) : False := by
  obtain ⟨m, F, hF, hfin, hchar, hp, _, ⟨iso⟩⟩ := model
  exact not_quasithin_of_ree_embedding m hp.positive hp.cardinality
    iso.symm.toMonoidHom iso.symm.injective hqt

/-- The actual F₄ odd-characteristic carrier is excluded without a
complementary-rank premise. -/
public theorem f4_caseI_false {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (hqt : IsQuasithin G)
    (model : ExceptionalGroup.IsF4 G (r ^ e)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hk : iso.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr iso.injective
  apply F4OddCover.not_quasithin_of_central_cover hr2 hcard iso.toMonoidHom iso.surjective
    (by rw [hk]; exact bot_le) _ hqt
  rw [hk, card_bot]
  decide

variable {K : GroupClass.{u}} {S : Type u} [Group S] [Finite S] [IsQuasisimple G] {p : ℕ}

omit [IsQuasisimple G] in
private theorem center_odd_of_caseII
    (h : CounterexampleToTheoremA K G S p) (hP : IsPGroup p (center G)) :
    Odd (Nat.card (center G)) := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact h.2.2.2.2.2.1.pow

/-- The original Case II group, rather than an assumed quasithin quotient,
is excluded for every large Ree central quotient. -/
public theorem ree_caseII_false
    (h : CounterexampleToTheoremA K G S p) (hP : IsPGroup p (center G)) {q : ℕ}
    (model : ExceptionalGroup.IsReeG2 (G ⧸ center G) q) : False := by
  obtain ⟨m, F, hF, hfin, hchar, hp, _, ⟨iso⟩⟩ := model
  exact ReeOddCover.not_quasithin_of_centralQuotientEquiv m hp.positive hp.cardinality
    iso (center_odd_of_caseII h hP) h.1

omit [IsQuasisimple G] in
/-- Both the defining-center and coprime-center F₄ branches are excluded
on the original source counterexample by the actual odd-cover theorem. -/
public theorem f4_caseII_false
    (h : CounterexampleToTheoremA K G S p) (hP : IsPGroup p (center G))
    {r e : ℕ} [Fact r.Prime] (hr : Odd r)
    (model : ExceptionalGroup.IsF4 (G ⧸ center G) (r ^ e)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  exact F4OddCover.not_quasithin_of_odd_center hr2 hcard iso (center_odd_of_caseII h hP) h.1
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
