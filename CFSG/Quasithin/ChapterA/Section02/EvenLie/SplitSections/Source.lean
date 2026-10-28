module
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SplitSections
public import Theory.SpecificGroups.Symplectic.A02ParabolicSections.SourceGeometry

/-!
# The symplectic source branch of A.2.18

The original center quotient has a proper two-local isotropic-line stabilizer
containing the actual complementary Sp₆ numerator. Its literal central quotient
is the PSp₆ section excluded by the already established smaller-section
induction and strong-quasithin bound. Thus the original group cannot have a
symplectic center quotient of rank at least four. The field witness and the
original source hypotheses are retained throughout.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, A.2.18,
first paragraph, printed p.40; GLS3 §2.6.
-/

public section
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
open Theory.SpecificGroups.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual Sp₆ section discharges all geometric premises of the higher
symplectic branch, directly under the original A.2 induction hypotheses. -/
theorem false_of_symplectic_center_quotient
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ}
    (ha : 0 < a) (hc : Nat.card F = 2 ^ a) (n : ℕ)
    (e : (G ⧸ Subgroup.center G) ≃* Matrix.PSp4Three.PSp (4+n) F) : False :=
  false_of_symplectic_six_split_parabolic ih hG hK ha hc n 0 e
    (symplecticParabolic_zero_ne_top n) (symplecticSixRange_le_parabolic n)

/-- The full symplectic model predicate has rank at most three. No geometric
witness or quasithinness of the center quotient is an extra premise. -/
theorem symplectic_center_quotient_rank_le_three
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r a : ℕ} (ha : 0 < a)
    (hmodel : ClassicalGroup.IsPSp (G ⧸ Subgroup.center G) r (2 ^ a)) : r ≤ 3 := by
  by_contra hr
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show 4≤r by omega)
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact false_of_symplectic_center_quotient ih hG hK ha hc n e

end CFSG.Quasithin.ChapterA.Section02.EvenLie
