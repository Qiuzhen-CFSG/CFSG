module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Linear
public import CFSG.Quasithin.ChapterA.Section02.OddLie.DefiningKernel
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleCase
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Geometry

/-!
# Odd triality in both source cases of A.2.17

The pinned rank-one and complementary maps are faithful. Integral arm geometry
proves their commutation. Their literal centralizer has defining rank at least
three, contradicting the fundamental centralizer bound in Case I. The same
maps give a rank-four elementary group in a scalar involution centralizer;
the odd central-extension theorem excludes the original Case II group.
No quotient quasithinness, covering classification or geometric input remains.

Source: Aschbacher–Smith, A.2.17, printed p.39.
-/

open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.OddFundamentalCentralizer
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly

/-- The literal odd triality carrier is excluded by its two faithful,
commuting fundamental maps; the integral geometry supplies commutation. -/
public theorem triality_not_quasithin (P : Parameters) (hp : Odd P.prime) :
    ¬ IsQuasithin (Carrier P) := by
  intro hqt
  let D := RankOne.pinnedRankOneMaps P
  let C := RankOne.armRootCommutation P
  have hc := fundamental_centralizer_rank_le_one hp
    (GaloisField.card P.prime P.exponent (Nat.ne_of_gt P.exponent_pos)) hqt
    (fundamentalHom D) (RankOne.fundamentalHom_injective P hp)
  rw [range_fundamentalHom D] at hc
  have hu : primeRank P.prime (residual P) ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective P.prime
      (residual P).subtype Subtype.val_injective).trans hc
  have hl := three_mul_exponent_le_residual_rank_of_geometry D C
    (RankOne.complementHom_injective P hp)
  have he := P.exponent_pos
  omega

/-- Every odd triality source Case I marking is impossible. -/
public theorem triality_caseI_false {G : Type*} [Group G] [Finite G]
    (P : Parameters) (hp : Odd P.prime) (hqt : IsQuasithin G)
    (iso : G ≃* Carrier P) : False :=
  triality_not_quasithin P hp (Theory.GroupTheory.isQuasithin_of_equiv iso hqt)

universe u
/-- The same maps yield rank four downstairs, so the checked odd central
extension theorem excludes the original Case II group for every odd triality parameter. -/
public theorem triality_caseII_false {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Finite G] [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA K G S p) (hP : IsPGroup p (center G))
    (P : Parameters) (hp : Odd P.prime) (iso : G ⧸ center G ≃* Carrier P) : False := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have ho : Odd (Nat.card (center G)) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact h.2.2.2.2.2.1.pow
  exact DefiningKernel.not_quasithin_triality_cover hp
    (RankOne.pinnedRankOneMaps P) (RankOne.armRootCommutation P)
    (RankOne.fundamentalHom_injective P hp) (RankOne.complementHom_injective P hp)
    (fundamentalHom_complementHom_commute _ _) iso ho h.1
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
