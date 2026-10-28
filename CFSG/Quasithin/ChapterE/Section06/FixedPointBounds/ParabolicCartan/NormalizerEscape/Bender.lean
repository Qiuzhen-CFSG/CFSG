module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.RankOneSource
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.UnitaryScalar

/-!
# Complete full-Hall escape in the single Bender source row

The three literal marked families now all give escape for every prescribed
odd-primary subgroup of the original maximal subgroup. Both stages of the
source quotient have been discharged, including the scalar prime in PSU₃.
Source: Aschbacher–Smith E.2.2(2a) and 4.4.13(1), pp.215–216,623–624.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels ChapterB
variable {X : Type*} [Group X] [Finite X]

/-- Full escape for the original prescribed subgroup in every single
Bender model, with no torus-containment or scalar coprimality premise. -/
theorem bender_original_escape
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : BenderModel (minimalParabolicMax S hP) K f)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup X) (hA : IsPGroup p A) (hAM : A ≤ minimalParabolicMax S hP) :
    ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  rcases hm with hm | hm
  · exact rank_one_original_escape S hP K hK hqK hc hm hp A hA hAM
  · exact unitary_original_escape_all_odd S hP K hK hqK hc hm hp A hA hAM

/-- The literal full-Hall generation conclusion of 4.4.13(1) in every
single Bender source row, including the trivial elementary subgroup. -/
theorem bender_original_generation
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : BenderModel (minimalParabolicMax S hP) K f)
    (Y : Subgroup X) (hYM : Y ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)))
    (p : ℕ) (hp : p.Prime) (A : Subgroup X) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y) :
    minimalParabolicMax S hP ⊔ normalizer (A : Set X) = ⊤ := by
  by_cases hbot : A = ⊥
  · rw [hbot, normalizer_eq_top, sup_top_eq]
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p A := hA
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hYodd : Odd (Nat.card Y) := by
    have ho := OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv] at ho
  have hAodd : Odd (Nat.card A) := hYodd.of_dvd_nat (card_dvd_of_le hAY)
  have hpodd : Odd p := hAodd.of_dvd_nat
    (hAp.card_eq_or_dvd.resolve_left (fun hh => hbot (eq_bot_of_card_eq A hh)))
  have hesc := bender_original_escape S hP K hK hqK hc hm hpodd A hAp (hAY.trans hYM)
  apply (minimalParabolicMax_spec S hP).1.lt_iff.mp
  exact left_lt_sup.mpr hesc

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
