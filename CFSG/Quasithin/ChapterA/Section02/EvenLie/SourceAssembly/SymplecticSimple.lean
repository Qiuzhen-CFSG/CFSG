module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.ClassicalSimple
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SplitSections.Source
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Cases

/-!
# The complete symplectic Case I branch of A.2.18

The actual proper two-local Sp6 section bounds the symplectic rank by three
using the original smaller-section induction. Rank one is the actual PSL2
model. In rank two the catalogue excludes the nonsimple field-two group.
In rank three the root-normalizer torus forces field two, and the ordinary
three-rank distinguishes the B and C lists. No quotient quasithinness is used.
Source: Aschbacher--Smith A.2.18, printed p.40.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {K : GroupClass.{u}} {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- All symplectic ranks in the original simple source case. -/
theorem caseI_symplectic (ih : TheoremAOnProperSections K G)
    (hna : ¬ IsMulCommutative G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r a : ℕ} (ha : 0 < a) (hp : KnownSimple.SymplecticParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPSp G r (2 ^ a)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hz : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hna (center_eq_top_iff.mp ht)).elim
  let ec : (G ⧸ center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hr := symplectic_center_quotient_rank_le_three ih hG hK ha (iso.of_mulEquiv ec)
  have hmin := hp.2.1
  interval_cases r
  · have hlin : ClassicalGroup.IsPSL G 2 (2 ^ a) := by
      obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
      exact ⟨F, hF, hfin, hc,
        ⟨e.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩
    exact caseI_linear hG ha ⟨hp.1, by decide, fun _ => hp.2.2.1 rfl⟩ hlin
  · have ha2 : 2 ≤ a := by
      by_contra hn
      have : a = 1 := by omega
      exact hp.2.2.2 rfl (by simp [this])
    have hc : IsTheoremCModel G := .rank_two a (.symplectic ha2 iso)
    exact ⟨hc.toTheoremBModel, fun _ => hc⟩
  · have ha1 := symplectic_exponent_eq_one hG (by decide : 3 ≤ 3) ha iso
    have hi : ClassicalGroup.IsPSp G 3 2 := by simpa [ha1] using iso
    exact ⟨.symplectic_binary hi,
      fun hs => (not_stronglyQuasithin_symplectic_six_binary hi hs).elim⟩

/-- Application to the literal simultaneous minimal-counterexample choice. -/
theorem not_minimalCounterexample_symplectic
    (h : MinimalCounterexample K G) {r a : ℕ} (ha : 0 < a)
    (hp : KnownSimple.SymplecticParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPSp G r (2 ^ a)) : False := by
  obtain ⟨hna, hqt, hk, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_symplectic h.2.theoremA hna hqt hk ha hp iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
