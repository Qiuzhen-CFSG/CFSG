module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.ProperSL2
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.SimpleQuotient
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne
/-!
# The original odd triality quotient is excluded by its proper cubic-field SL2

The already faithful complementary map embeds SL2(q^3) into the literal
triality carrier. It is proper in the source quotient S/Z(S): a surjective
map would send its nontrivial scalar involution into the trivial center.
The original proper-section induction then contradicts its defining local
rank 3e. This avoids an unnecessary separate elementary-eight construction
and never assumes quasithinness of the quotient.
Source: Aschbacher--Smith A.2.12 and A.2.17, printed pp.36,39.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- Every actual odd triality source quotient has the forbidden proper SL2 section. -/
theorem CounterexampleToTheoremA.centralQuotient_no_odd_triality
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (P : Triality.Standard.Parameters) (hp : Odd P.prime)
    (e : (S ⧸ center S) ≃* Triality.Standard.Carrier P) : False := by
  let Q := S ⧸ center S
  let : Group.IsPerfect S := h.2.2.2.1.isPerfect
  obtain ⟨f,hf⟩ := h.exists_surjective ih.theoremA
  let q : G →* Q := (QuotientGroup.mk' (center S)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  let D := Triality.Standard.OddFundamentalCentralizer.RankOne.pinnedRankOneMaps P
  let C := Triality.Standard.OddFundamentalCentralizer.RankOne.armRootCommutation P
  let j := e.symm.toMonoidHom.comp
    (Triality.Standard.OddFundamentalCentralizer.complementHom D C)
  have hj : Function.Injective j := e.symm.injective.comp
    (Triality.Standard.OddFundamentalCentralizer.RankOne.complementHom_injective P hp)
  have hproper : j.range ≠ ⊤ := by
    intro ht
    have hs := MonoidHom.range_eq_top.mp ht
    have hz : j (-1) ∈ center Q := by
      rw [mem_center_iff]
      intro x
      obtain ⟨a,rfl⟩ := hs x
      rw [← map_mul,← map_mul]
      congr 1
      simp
    rw [Group.IsPerfect.center_quotient_center_eq_bot S] at hz
    have hn : (-1 : Matrix.SpecialLinearGroup (Fin 2) (Triality.Standard.ExtensionField P)) = 1 :=
      hj ((mem_bot.mp hz).trans (map_one j).symm)
    have he1 : (-1 : Triality.Standard.ExtensionField P) = 1 := by
      have he := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2)
        (Triality.Standard.ExtensionField P) => A.val 0 0) hn
      simpa using he
    exact Triality.Standard.OddFundamentalCentralizer.RankOne.two_ne_zero P hp
      (by linear_combination -he1)
  exact Nonsemisimple.RankTwoSieve.no_large_proper_sl2_quotient ih h.1 h.2.1 q hq hp
    (GaloisField.card P.prime (3 * P.exponent) (by have := P.exponent_pos; omega))
    (by have := P.exponent_pos; omega) j hj hproper

/-- The same contradiction for the original literal odd-parameter model predicate. -/
theorem CounterexampleToTheoremA.centralQuotient_no_odd_triality_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {q : ℕ} (hq : Odd q)
    (model : Triality.Standard.IsTrialityGroupAt q (S ⧸ center S)) : False := by
  obtain ⟨P,hP,⟨e⟩⟩ := model
  have hp : Odd P.prime := by
    by_contra hn
    have hp2 : P.prime = 2 := P.prime_prime.eq_two_or_odd.resolve_right (fun hh => hn (Nat.odd_iff.mpr hh))
    have he : Even P.q := by
      change Even (P.prime ^ P.exponent)
      rw [hp2]
      exact even_two.pow_of_ne_zero (Nat.ne_of_gt P.exponent_pos)
    exact (Nat.not_even_iff_odd.mpr (hP ▸ hq)) he
  exact h.centralQuotient_no_odd_triality ih P hp e
end CFSG.Quasithin.ChapterA.Section02
