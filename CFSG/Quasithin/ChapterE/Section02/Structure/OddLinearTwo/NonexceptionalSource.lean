module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.FieldDegree
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeElementary
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeSeven
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.QuadraticElementary
/-!
# The original nonexceptional normal odd-PSL₂ source bound

The genuine SQTK and minimal-parabolic hypotheses force the field degree
at most two. The prime-field source bound, the actual prime-seven transport
to PSL₃(2), and the quadratic semilinear centralizer calculation then show
that an elementary subgroup of the original O₂(M), normalized by the
original Sylow subgroup, has order at most two. The statement retains the
actual component isomorphism and minimal-parabolic maximal subgroup.

The parameters q = 5 and q = 9 are the source's separate binary model
exceptions. Source: Aschbacher–Smith E.2.2 and E.2.7, printed pp.215–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
/-- The genuine normal nonexceptional odd-PSL₂ row is excluded by the original E.2.7 elementary subgroup. -/
theorem odd_linear_source_not_elementary_four
    {H : Type*} [Group H] [Finite H] {κ : GroupClass}
    (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : (ChapterB.minimalParabolicMax T hP).normalCore = ⊥)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ n)
    (hlarge : 5 < Nat.card F) (hnine : Nat.card F ≠ 9)
    (eK : K ≃* PSL2 F)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVM : V ≤ (pCore 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype)
    (hVT : V ≤ (T : Subgroup H))
    (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcard : 4 ≤ Nat.card V) : False := by
  obtain ⟨hp, hn | hn⟩ := odd_linear_source_parameters hH K eK ho hF hlarge hnine
  · have hFp : Nat.card F = p := by simpa only [hn, pow_one] using hF
    have hp5 : 5 < p := by omega
    have hcase : p = 7 ∨ 9 < p := by
      by_contra! hc
      obtain ⟨hne, hsmall⟩ := hc
      have hprime : Nat.Prime p := Fact.out
      interval_cases p <;> norm_num at *
    rcases hcase with rfl | hbig
    · exact prime_seven_source_not_elementary_four T hP hcore K hgen hFp eK V hV hVT hVN hcard
    · exact prime_linear_source_not_elementary_four T hP K hgen hO ho hFp hbig eK V hV hVT hVN hcard
  · have hFs : Nat.card F = p ^ 2 := hn ▸ hF
    exact quadratic_linear_source_not_elementary_four T hP K hgen hO ho hFs hp eK V hV hVM hVN hcard
/-- The unified original normal odd-PSL₂ source bound, outside the two binary exceptions. -/
theorem odd_linear_source_elementary_card_le_two
    {H : Type*} [Group H] [Finite H] {κ : GroupClass}
    (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : (ChapterB.minimalParabolicMax T hP).normalCore = ⊥)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ n)
    (hlarge : 5 < Nat.card F) (hnine : Nat.card F ≠ 9)
    (eK : K ≃* PSL2 F)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVM : V ≤ (pCore 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype)
    (hVT : V ≤ (T : Subgroup H))
    (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) : Nat.card V ≤ 2 := by
  have hlt : Nat.card V < 4 := by
    by_contra! hc
    exact odd_linear_source_not_elementary_four hH T hP hcore K hgen hO
      ho hF hlarge hnine eK V hV hVM hVT hVN hc
  let := hV
  obtain ⟨d, hd⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  rw [hd] at hlt ⊢
  have hd2 : d < 2 := by
    by_contra! hh
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at this
    omega
  interval_cases d <;> norm_num
end CFSG.Quasithin.ChapterE.Structure
