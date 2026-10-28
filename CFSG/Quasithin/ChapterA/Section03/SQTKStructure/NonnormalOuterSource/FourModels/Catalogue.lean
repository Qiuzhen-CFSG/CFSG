module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Classical
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.RemainingRows

/-!
# The full Theorem C inspection at odd rank one

The classical root and torus calculations, and the literal finite/exceptional
cubic witnesses, leave precisely the four A.3.8 models. The small A₅ and
PSL₃(2) rows are transported to PSL₂(4) and PSL₂(7), so no source row is
silently omitted. Source: Aschbacher–Smith A.1.34(3), A.3.8(3), pp.29–30,45–46.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
open Chapter1.Section02

/-- The exact complete four-model inspection, with all original Theorem C rows. -/
theorem model_of_odd_ranks {S : Type*} [Group S] [Finite S]
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p S ≤ 1)
    (hmodel : LocalModels.TheoremCModel S) : NonnormalCComponentModel S := by
  have hthree := hr 3 (by decide) (by decide)
  cases hmodel with
  | alternating n hn he => exact alternating_model hthree n hn he
  | linear_odd p n hp ho hn _ he => exact linear_two_odd_model hr p n hp ho hn he
  | three_odd p hp ho unitary he =>
    cases unitary with
    | false => exact (linear_three_odd_false hr p hp ho he).elim
    | true => exact (unitary_three_odd_false hr p hp ho he).elim
  | rank_one he =>
    cases he with
    | linear n hn he => exact .linear_even n hn he
    | unitary n hn he => exact (unitary_three_binary_false hr n hn he).elim
    | suzuki m hm he => exact .suzuki m hm he
  | rank_two he =>
    rcases rank_two_rows he with ⟨n,hn,he⟩ | hrank
    · exact linear_three_binary_model hr n hn he
    · omega
  | binary_linear n hn he => have := binary_linear_three_rank n hn he; omega
  | sporadic name hne he =>
    let : Finite name.Carrier := Finite.of_injective he.some.symm he.some.symm.injective
    have hlow := sporadic_three_rank name hne
    rw [← primeRank_equiv 3 he.some] at hlow
    omega
  | janko_one he => exact .janko he

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
