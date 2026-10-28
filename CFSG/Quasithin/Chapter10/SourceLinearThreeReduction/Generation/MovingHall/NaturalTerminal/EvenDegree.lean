module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CoreQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LargeTwoCoreQuotientRank
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverOrders
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Eliminating every even natural field degree

For even n the original natural block has a factor five in its order.
Its faithful image in the common component's two-core quotient retains
that factor and its elementary module of rank 2n. The known-simple
component catalogue and Bender non-enlargement force cubic rank at least
two in the common component. The original centralizing Hall axis has
order 2ⁿ−1, divisible by three. Its faithful Borel action separates it
from the component, giving a third cubic direction in the SQTK normalizer.

This applies to all even degrees, without identifying the field with four.
The source context still retains natural marking and original Hall placement;
qt-d-10-nona5-moving-hall-three owns their discharge and odd-degree recognition.
Source: Aschbacher–Smith 10.2.3(4), printed p.747, using A.3.6 and the
rank-one non-enlargement branch of A.3.12.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterC ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem five_dvd_binary_square_sub_one {n : ℕ} (hn : Even n) :
    5 ∣ (2^n)^2 - 1 := by
  have hm : (2^n)^2 % 5 = 1 := by
    obtain ⟨k,rfl⟩ := hn
    rw [←pow_mul,show (k+k)*2 = 4*k by omega,pow_mul,Nat.pow_mod]
    norm_num
  have hp : 1 ≤ (2^n)^2 := one_le_pow₀ (one_le_pow₀ (by decide))
  have hs := Nat.sub_add_cancel hp
  exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)

private theorem natural_five_dvd {X : Type*} [Group X] [Finite X] {n : ℕ}
    (h : IsL2EvenBlock X n) (hn : Even n) : 5 ∣ Nat.card X := by
  obtain ⟨F,_,_,hF,_,r,⟨m⟩,hm⟩ := h.2.2
  have hquot : Nat.card (X ⧸ pCore 2 X) = 2^n * ((2^n)^2-1) := by
    rw [Nat.card_congr m.quotientIso.toEquiv,Atlas.card_sl_two,hF]
  apply dvd_trans _ (card_quotient_dvd_card (pCore 2 X))
  rw [hquot]
  exact dvd_mul_of_dvd_right (five_dvd_binary_square_sub_one hn) _

/-- Every even field degree forces cubic rank at least two in the actual overcomponent. -/
theorem CommonOvercomponent.three_rank_of_even_degree
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (hn : Even n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) : 2 ≤ primeRank 3 c.overcomponent := by
  let C := c.overcomponent
  have hsq : IsSQTK KnownSimple.IsKnownSimple C := ⟨
    c.local_sqtk.stronglyQuasithin.of_injective (inclusion c.component.1)
      (inclusion_injective c.component.1),
    c.local_sqtk.isKGroup.of_injective (inclusion c.component.1)
      (inclusion_injective c.component.1)⟩
  have hC : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using c.component.2.subgroupOf_of_le le_rfl c.component.1
  obtain ⟨S,_,hlocal,_⟩ := c.local_family
  have h2 := (c.quotient_rank_and_quasisimple hi).1
  have hdegree := c.original_natural.1
  exact SourceEmbeddings.local_component_three_rank_of_large_twoCore_quotient hsq hC
    S (c.original.subgroupOf C) hlocal
    (fun he => c.original_lt.ne (le_antisymm c.original_lt.le (subgroupOf_eq_top.mp he)))
    (by omega) ((natural_five_dvd c.original_natural hn).trans (card_dvd_of_injective _ hi))

/-- The original axis supplies the third cubic direction, contradicting SQTK. -/
theorem CommonOvercomponent.false_of_even_degree
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (hn : Even n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) : False := by
  let S := ⁅baumann (T : Subgroup G),c.axis⁆
  let N := normalizer ((S ⊔ c.axis : Subgroup G) : Set G)
  have hCS : c.overcomponent ≤ centralizer (S : Set G) :=
    c.centralizes.trans (centralizer_le (fun _ hx => mem_sup_left hx))
  have hAC : c.axis ≤ centralizer (c.overcomponent : Set G) :=
    le_centralizer_iff.mp (c.centralizes.trans (centralizer_le (fun _ hx => mem_sup_right hx)))
  have h3 : 3 ∣ Nat.card c.axis := by
    rw [c.axis_card]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr hn
  have hlarge := three_le_primeRank_of_disjoint_commuting c.axis c.overcomponent
    (disjoint_of_centralizes_faithful_subgroup c.axis c.overcomponent S c.faithful hCS)
    hAC h3 (c.three_rank_of_even_degree hn hi)
  have hin : c.axis ⊔ c.overcomponent ≤ N :=
    sup_le (le_sup_right.trans (S ⊔ c.axis).le_normalizer) c.component.1
  have hle := Theory.GroupTheory.primeRank_le_of_injective 3
    (inclusion hin) (inclusion_injective hin)
  have hsmall := c.local_sqtk.stronglyQuasithin 3 (by decide) (by decide)
  change primeRank 3 N ≤ 2 at hsmall
  omega

/-- The original source context excludes every even natural field degree. -/
theorem Context.false_of_even_natural_degree
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (heven : Even n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) : False := by
  obtain ⟨c,hi,_,_⟩ := ctx.common_overcomponent_faithful D n hn hF e mark hBB
  exact c.false_of_even_degree heven hi

/-- Only odd degrees remain in the natural-row terminal recognition. -/
theorem Context.natural_degree_odd
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) : Odd n := by
  exact Nat.not_even_iff_odd.mp (fun he =>
    ctx.false_of_even_natural_degree D n hn he hF e mark hBB)

end CFSG.Quasithin.Chapter10.MovingHall
