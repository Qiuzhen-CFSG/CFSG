module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.FullBound
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.MovedBound

/-!
# Model-free size bounds for quiet small offenders

The component stabilizer of a noncommuting TI offender embeds in the
actual automorphism group of L/O₂(L). Its index in the offender is at most
two, and the offender has index at most four in the conjugate module.
Thus an automorphism two-rank bound r gives moved order at most 2^(r+3).
Point-centralizer control and the literal fixed-space geometry apply this
both to fully moved modules and to separated factors. No marking or
irreducibility of the component action is assumed.

The actual J₁ and large binary SL₂ applications are in Quiet.Families.
Source: Aschbacher--Smith 10.2.9--12, pp.750--755.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE ChapterI.Section06To08 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem full_ti_card_le_of_automorphism_rank
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hti : IsTISubgroup D.fullModule)
    (hz : D.fullModule ⊓ centralizer (L : Set G) = ⊥)
    {r : ℕ} (hrank : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ r) :
    Nat.card D.fullModule ≤ 2 ^ (r + 3) := by
  let V := D.fullModule
  let P := V.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let B := A ⊓ normalizer (L : Set G)
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := offender_elementary_of_le
    (show B ≤ P from inf_le_left.trans inf_le_left)
  obtain ⟨f,hf⟩ := full_ti_offender_component_stabilizer_injective D c hti hz
  obtain ⟨a⟩ := full_component_automizer_equiv D c.nonnormal
  let j := (MulAut.congr a).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.congr a).injective.comp hf
  have hr : primeRank 2 B ≤ r := (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
    hrank
  have hB : Nat.card B ≤ 2 ^ r := by
    have hh := (primeRank_le_iff_elementary_card_le B).mp hr ⊤
      (IsElementaryAbelian.of_injective (⊤ : Subgroup B).subtype Subtype.val_injective)
    rw [Nat.card_congr (topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv] at hh
    exact hh
  have hAI : A.relIndex P ≤ 4 := by
    have he : D.maximalLocal.relIndex P = 2 ^ subgroupCorank P (P ⊓ D.maximalLocal) := by
      rw [subgroupCorank_eq_quotient_finrank,relIndex_eq_two_pow_quotient_finrank P D.maximalLocal]
      congr 1
      rw [inf_subgroupOf_left]
    rw [inf_relIndex_left,he]
    exact Nat.pow_le_pow_right (by decide) c.small
  have hBI : B.relIndex A ≤ 2 := by
    rw [inf_relIndex_left]
    by_cases hAN : A ≤ normalizer (L : Set G)
    · rw [relIndex_eq_one.mpr hAN]
      decide
    obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
    obtain ⟨b,hb,hbn⟩ := SetLike.not_le_iff_exists.mp hAN
    exact (normalizer_relIndex_eq_two_of_pair A L
      (L.map (MulAut.conj t).toMonoidHom)
      (fun m hm => source_nonnormal_maximal_pair D c.nonnormal ht htn m hm.2)
      b hb (fun he => hbn (mem_normalizer_iff_map_conj_eq.mpr he))).le
  have ha := relIndex_mul_card_of_le (show A ≤ P from inf_le_left)
  have hb := relIndex_mul_card_of_le (show B ≤ A from inf_le_left)
  have hc : Nat.card P = Nat.card V := card_map_of_injective (MulAut.conj g).injective
  have hAb := Nat.mul_le_mul hBI hB
  rw [hb] at hAb
  have hPb := Nat.mul_le_mul hAI hAb
  rw [ha,hc] at hPb
  convert hPb using 1
  ring

theorem moved_ti_card_le_of_automorphism_rank
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hz : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥)
    {r : ℕ} (hrank : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ r)
    {x : G}
    (hd : Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom))
    (hnc : ⁅⁅D.fullModule,L⁆,(⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom⁆ ≠ ⊥)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) ≤ 2)
    (hAN : (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) ≤ 2 ^ (r + 3) := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj x).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let B := A ⊓ normalizer (L : Set G)
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := offender_elementary_of_le
    (show B ≤ P from inf_le_left.trans inf_le_left)
  obtain ⟨f,hf⟩ := moved_ti_offender_component_stabilizer_injective D hti hz hd hnc hsmall hAN
  obtain ⟨a⟩ := moved_component_automizer_equiv D hn
  let j := (MulAut.congr a).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.congr a).injective.comp hf
  have hr : primeRank 2 B ≤ r := (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
    hrank
  have hB : Nat.card B ≤ 2 ^ r := by
    have hh := (primeRank_le_iff_elementary_card_le B).mp hr ⊤
      (IsElementaryAbelian.of_injective (⊤ : Subgroup B).subtype Subtype.val_injective)
    rw [Nat.card_congr (topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv] at hh
    exact hh
  have hAI : A.relIndex P ≤ 4 := moved_intersection_index_le D hsmall
  have hBI : B.relIndex A ≤ 2 := by
    rw [inf_relIndex_left]
    by_cases hAL : A ≤ normalizer (L : Set G)
    · rw [relIndex_eq_one.mpr hAL]
      decide
    obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
    obtain ⟨b,hb,hbn⟩ := SetLike.not_le_iff_exists.mp hAL
    exact (normalizer_relIndex_eq_two_of_pair A L
      (L.map (MulAut.conj t).toMonoidHom)
      (fun m hm => source_nonnormal_maximal_pair D hn ht htn m hm.2)
      b hb (fun he => hbn (mem_normalizer_iff_map_conj_eq.mpr he))).le
  have ha := relIndex_mul_card_of_le (show A ≤ P from inf_le_left)
  have hb := relIndex_mul_card_of_le (show B ≤ A from inf_le_left)
  have hc : Nat.card P = Nat.card W := card_map_of_injective (MulAut.conj x).injective
  have hAb := Nat.mul_le_mul hBI hB
  rw [hb] at hAb
  have hPb := Nat.mul_le_mul hAI hAb
  rw [ha,hc] at hPb
  convert hPb using 1
  ring


/-- Every quiet small offender in a cubic-order family has bounded moved order,
using only the actual component automorphism two-rank. -/
theorem quiet_moved_card_le_of_automorphism_rank
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hthree : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {r : ℕ} (hrank : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ r) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) ≤ 2 ^ (r + 3) := by
  by_contra! hlarge
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  have hti := quiet_moved_ti_of_three D c hJ hNL hthree
  have hnfull : ⁅D.fullModule,L⁆ ≠ D.fullModule := by
    intro he
    rw [he] at hz hti hlarge
    exact (not_lt_of_ge (full_ti_card_le_of_automorphism_rank D c hti hz hrank)) hlarge
  have hcross : ∀ {t : G}, t ∈ (T : Subgroup G) → t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
    fun ht htn => (quiet_crossed_or_moved_eq_full D c.many c.minimal hJ ht htn).resolve_right hnfull
  have hsize : 8 < (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ := by
    rw [←inf_relIndex_left,hz,relIndex_bot_left]
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ r + 3)).trans_lt hlarge
  let ctx : FixedSpaces.Context D :=
    ⟨c.many,c.minimal,c.nonnormal,c.notA5,c.pointCentralizers,
      fun _ ht htn => hcross ht htn,hsize⟩
  have hgeometry := FixedSpaces.fixedSpaceGeometry_of_normalizer D ctx hNL
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  apply c.noncommuting
  apply source_a5_small_conjugates_commute_of_moved_factor D c.nonnormal ht
    (hcross ht htn) 2 ?_ g c.small
  intro x hx hs
  have hc : ⁅⁅D.fullModule,L⁆,(⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom⁆ = ⊥ := by
    by_contra hnc
    have hd : Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom) :=
      disjoint_iff.mpr (FixedSpaces.moved_inf_conjugate_eq_bot D c.nonnormal t ht
        (hcross ht htn) c.pointCentralizers hNL hx)
    exact (not_lt_of_ge (moved_ti_card_le_of_automorphism_rank D c.nonnormal hti hz
      hrank hd hnc hs (hgeometry x hx hs).1)) hlarge
  have hp := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  refine ⟨?_,hp⟩
  obtain ⟨w,hw,hw1⟩ := (⁅D.fullModule,L⁆ : Subgroup G).bot_or_exists_ne_one.resolve_left
    (source_full_moved_ne_bot D)
  exact (hp.trans (centralizer_le (Set.singleton_subset_iff.mpr hw))).trans
    (c.pointCentralizers w hw hw1)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
