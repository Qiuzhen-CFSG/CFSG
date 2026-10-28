module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.Source

/-!
# The fully moved quiet binary-three case is impossible

For a center-free full TI module, every nonidentity element of the attained
small offender has fixed corank at most two. Its component stabilizer embeds
in the automorphism group of the actual component action: a kernel element
would commute with a perfect fixed-point-free action on its displacement
space of dimension at most two. The two-rank bound for Aut(SL₃(2)), together
with the two index bounds, gives module order at most 64.

The remaining fully moved quiet binary-three case has order at least 512.
Excluding it proves crossed centralization without a natural marking.
`Quiet.BinaryThree` uses this in recognition of the actual moved quotient.
Source: Aschbacher--Smith 10.1.1--2 and 10.2.12, pp.741--742,754--755.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE ChapterI.Section06To08 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem full_component_automizer_equiv
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nonempty ((inducedAutomizer D.fullModule L) ≃* (L ⧸ pCore 2 L)) := by
  let V := D.fullModule
  let N := normalizer (V : Set G)
  have hLN : L ≤ N :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  let β := V.normalizerMonoidHom.rangeRestrict
  let A := L.subgroupOf N
  let a : L ≃* A := (subgroupOfEquivOfLe hLN).symm
  let f := (β.subgroupMap A).comp a.toMonoidHom
  have hf : Function.Surjective f := (β.subgroupMap_surjective A).comp a.surjective
  have hk : pCore 2 L ≤ f.ker := by
    intro l hl
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (l : G) * (v : G) * (l : G)⁻¹ = (v : G)
    have hc := source_component_core_centralizes_fullModule D
      (mem_map_of_mem L.subtype hl) v v.property
    change (v : G) * (l : G) = (l : G) * (v : G) at hc
    rw [←hc,mul_inv_cancel_right]
  let fbar := QuotientGroup.lift (pCore 2 L) f hk
  have hs : Function.Surjective fbar := QuotientGroup.lift_surjective_of_surjective _ _ hf hk
  have hne : inducedAutomizer V L ≠ ⊥ := by
    intro he
    have hc := (inducedAutomizer_eq_bot_iff hLN).mp he
    exact source_full_moved_ne_bot D
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  let : Nontrivial (A.map β) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  let : IsSimpleGroup (L ⧸ pCore 2 L) := ModuleChoice.component_quotient_simple D hn
  have hi : Function.Injective fbar := by
    apply fbar.ker_eq_bot_iff.mp
    rcases fbar.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    exfalso
    obtain ⟨y,hy⟩ := exists_ne (1 : A.map β)
    obtain ⟨x,rfl⟩ := hs y
    exact hy (show x ∈ fbar.ker from ht ▸ mem_top _)
  exact ⟨(MulEquiv.ofBijective fbar ⟨hi,hs⟩).symm⟩

theorem full_ti_offender_component_stabilizer_injective
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hti : IsTISubgroup D.fullModule)
    (hz : D.fullModule ⊓ centralizer (L : Set G) = ⊥) :
    ∃ f : ↥((D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ⊓
      normalizer (L : Set G)) →* MulAut (inducedAutomizer D.fullModule L),
      Function.Injective f := by
  let V := D.fullModule
  let N := normalizer (V : Set G)
  let S := inducedAutomizer V L
  let B := (V.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ⊓ normalizer (L : Set G)
  have hBN : B ≤ N := (inf_le_left.trans inf_le_right).trans D.maximalLocal_normalizes_fullModule
  let β := V.normalizerMonoidHom.rangeRestrict
  let f : B →* Automizer V := β.comp (inclusion hBN)
  have hf (b : B) : f b ∈ normalizer (S : Set (Automizer V)) := by
    have hb : (inclusion hBN b) ∈ normalizer (L.subgroupOf N : Set N) := by
      rw [mem_normalizer_iff]
      intro x
      exact mem_normalizer_iff.mp b.property.2 x
    exact (L.subgroupOf N).le_normalizer_map β ⟨inclusion hBN b,hb,rfl⟩
  let fN : B →* normalizer (S : Set (Automizer V)) := f.codRestrict _ hf
  let α : B →* MulAut S := S.normalizerMonoidHom.comp fN
  have hi : Function.Injective α := by
    apply (injective_iff_map_eq_one _).mpr
    intro b hb
    by_contra hb1
    have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hnc := full_ti_offender_not_centralizing D c hti b.property.1.1 hb1'
    have hr : subgroupCorank V (V ⊓ centralizer ({(b : G)} : Set G)) ≤ 2 := by
      rw [full_ti_offender_fixed_corank D c hti b.property.1.1 b.property.1.2 hb1']
      exact c.small
    apply small_actor_not_commuting_component_image D hz b.property.1.2 hnc hr
    have hcent : f b ∈ centralizer (S : Set (Automizer V)) := by
      have hh : fN b ∈ S.normalizerMonoidHom.ker := hb
      rw [Subgroup.normalizerMonoidHom_ker] at hh
      exact hh
    have hA : inducedAutomizer V (zpowers (b : G)) ≤ centralizer (S : Set (Automizer V)) := by
      rintro x ⟨n,hn,rfl⟩
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp hn
      have he : n = (inclusion hBN b) ^ k := Subtype.ext hk.symm
      rw [he,map_zpow]
      exact (centralizer (S : Set (Automizer V))).zpow_mem hcent k
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hA)
  exact ⟨α,hi⟩

theorem full_ti_binary_three_card_le_sixtyfour
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hti : IsTISubgroup D.fullModule)
    (hz : D.fullModule ⊓ centralizer (L : Set G) = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    Nat.card D.fullModule ≤ 64 := by
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
  let j := (MulAut.congr (a.trans e)).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.congr (a.trans e)).injective.comp hf
  have hr : primeRank 2 B ≤ 3 := (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
    BinaryLinearThree.NaturalDual.automorphism_two_rank_le_three
  have hB : Nat.card B ≤ 8 := by
    have hh := (primeRank_le_iff_elementary_card_le B).mp hr ⊤
      (IsElementaryAbelian.of_injective (⊤ : Subgroup B).subtype Subtype.val_injective)
    rw [Nat.card_congr (topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv] at hh
    norm_num at hh
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
  exact hPb

theorem quiet_binary_three_moved_ne_full
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    ⁅D.fullModule,L⁆ ≠ D.fullModule := by
  intro hfull
  have hh := quiet_binary_three_full_small_involution D c hJ hNL e hfull
  have hb := full_ti_binary_three_card_le_sixtyfour D c hh.2.2.1 hh.2.1 e
  omega

theorem quiet_binary_three_crossed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  (quiet_crossed_or_moved_eq_full D c.many c.minimal hJ ht htn).resolve_right
    (quiet_binary_three_moved_ne_full D c hJ hNL e)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
