module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.Source
public import Theory.Representation.BinaryConjugationSection.CentralImage
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.NormalElementary
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.Representation.SpecialLinearNatural

/-!
# Excluding large moved images in complementary point carriers

The moved elementary image in the containing central quotient is normalized
by a full Sylow two-subgroup. Binary linear groups and the small sporadics
have insufficient two-part or two-rank; the native full-Sylow calculations
for J₄ and HS bound their normal elementary subgroups more sharply.

A four-natural binary-three module section has order 2¹², and its coordinate
map factors through this literal central image. These comparisons exclude
that entire row without irreducibility or removal of fixed vectors.
Quasisimple.Source applies the result after excluding the rank-two carriers.
Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48,750--751.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- A moved image of order at least 2¹² forces two-rank at least twelve. -/
theorem center_quotient_rank_of_large_moved [Group.IsPerfect I]
    (hbig : 2^12 ≤ Nat.card (((⁅D.fullModule,L⁆).subgroupOf I).map
      (QuotientGroup.mk' (center I)))) : 12 ≤ primeRank 2 (I ⧸ center I) := by
  obtain ⟨_,_,_,_,_,_,_,hE,_⟩ := center_quotient_data D c
  have hu := (primeRank_le_iff_elementary_card_le (I ⧸ center I)).mp le_rfl _ hE
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hbig.trans hu)

omit D c in
private theorem binary_card (r : ℕ) [NeZero r] :
    Nat.card PSL(r,ZMod 2) = ∏ i : Fin r, (2^r - 2^i.val) := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) r
  simpa only [Nat.card_zmod,show 2-1=1 from rfl,Nat.gcd_one_right,mul_one] using h

include D c in
/-- No complementary containing carrier supports this large moved image. -/
theorem not_complementary_of_large_moved [IsQuasisimple I]
    (hbig : 2^12 ≤ Nat.card (((⁅D.fullModule,L⁆).subgroupOf I).map
      (QuotientGroup.mk' (center I))))
    (hr : ¬ ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) : False := by
  have hl := center_quotient_rank_of_large_moved D c hbig
  rcases remaining_binary_or_sporadic D c hr with ⟨r,hr,hI⟩ | ⟨name,hname,⟨e⟩⟩
  · obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hI
    let := Fintype.ofFinite F
    let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let d := eI.trans (Atlas.fieldEquivPSL r f)
    have hc : ¬ 2^12 ∣ Nat.card (I ⧸ center I) := by
      rw [Nat.card_congr d.toEquiv]
      rcases hr with rfl | rfl
      · rw [binary_card]
        norm_num [Fin.prod_univ_succ]
      · rw [binary_card]
        norm_num [Fin.prod_univ_succ]
    have hu : primeRank 2 (I ⧸ center I) ≤ 11 :=
      primeRank_le_of_prime_pow_not_dvd hc
    omega
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (I ⧸ center I) ≃* Sporadic.Mathieu.M22 at e
      rw [primeRank_equiv 2 e] at hl
      have hu := Sporadic.Mathieu.m22_twoRank_le_four
      omega
    · change (I ⧸ center I) ≃* Sporadic.Mathieu.M23 at e
      rw [primeRank_equiv 2 e] at hl
      have hu := Sporadic.Mathieu.m23_twoRank_le_four
      omega
    · change (I ⧸ center I) ≃* Sporadic.Mathieu.M24 at e
      have hc : ¬ 2^12 ∣ Nat.card (I ⧸ center I) := by
        rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m24_order]
        norm_num
      have hu : primeRank 2 (I ⧸ center I) ≤ 11 :=
        primeRank_le_of_prime_pow_not_dvd hc
      omega
    · change (I ⧸ center I) ≃* Janko4.Model at e
      obtain ⟨S,_,_,_,hSN,_,_,hE,_⟩ := center_quotient_data D c
      let E := ((⁅D.fullModule,L⁆).subgroupOf I).map (QuotientGroup.mk' (center I))
      let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
      let := hE
      let : IsElementaryAbelian 2 (E.map e.toMonoidHom) :=
        IsElementaryAbelian.map e.toMonoidHom
      have hu := Janko4.LocalStructure.normal_elementary_card_le_2048
        (R.mapSurjective (f := e.toMonoidHom) e.surjective)
        (E.map e.toMonoidHom)
        ((map_mono hSN).trans (le_normalizer_map e.toMonoidHom))
      rw [card_map_of_injective e.injective] at hu
      change 4096 ≤ Nat.card E at hbig
      omega
    · change (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier at e
      obtain ⟨S,_,_,_,hSN,_,_,hE,_⟩ := center_quotient_data D c
      let E := ((⁅D.fullModule,L⁆).subgroupOf I).map (QuotientGroup.mk' (center I))
      let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
      let := hE
      have hu := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight
        (R.mapSurjective (f := e.toMonoidHom) e.surjective)
        (E.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom)
        ((map_mono hSN).trans (le_normalizer_map e.toMonoidHom))
      rw [card_map_of_injective e.injective] at hu
      change 4096 ≤ Nat.card E at hbig
      omega
    · change (I ⧸ center I) ≃* Held.He at e
      have hc : ¬ 2^12 ∣ Nat.card (I ⧸ center I) := by
        rw [Nat.card_congr e.toEquiv]
        exact Held.not_two_pow_twelve_dvd_card
      have hu : primeRank 2 (I ⧸ center I) ≤ 11 :=
        primeRank_le_of_prime_pow_not_dvd hc
      omega
    · change (I ⧸ center I) ≃* Rudvalis.Model at e
      rw [primeRank_equiv 2 e] at hl
      have hu := Rudvalis.primeRank_le_six
      omega

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02 Representation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)

/-- The source row consisting of four copies of the binary natural module. -/
noncomputable abbrev fourBinaryThreeNatural :=
  ((specialLinearNatural (k := ZMod 2) 3).prod (specialLinearNatural 3)).prod
    ((specialLinearNatural 3).prod (specialLinearNatural 3))

include D c in
/-- The literal reduced four-natural section excludes every complementary carrier. -/
theorem not_complementary_of_four_binary_three [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (fourBinaryThreeNatural.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hr : ¬ ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) : False := by
  apply Other.not_complementary_of_large_moved D c ?_ hr
  have hc := d.card_le_central_image I c.strict.le
    ((source_full_moved_le_component D).trans c.strict.le) le_rfl
  simpa only [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod,
    show 2^3 * 2^3 * (2^3 * 2^3) = 2^12 by decide] using hc
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
