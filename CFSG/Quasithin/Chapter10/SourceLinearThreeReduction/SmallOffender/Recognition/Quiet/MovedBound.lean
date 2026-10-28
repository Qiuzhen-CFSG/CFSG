module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.Source

/-!
# A small offender bounds the quiet binary-three moved factor

A noncommuting conjugate TI pair has equal mutual-normalizer orders. Thus
every nonidentity element of the moved offender has fixed corank at most two,
even though this offender need only lie in the full mutual normalizer.
The center-free component action excludes a kernel in its stabilizer's map
to Aut(SL₃(2)). The component stabilizer has order at most eight, its index
in the offender is at most two, and the offender index is at most four.
Hence the moved factor has order at most 64.

`Quiet.BinaryThree` applies this to the original fixed-space geometry and
point-centralizer hypotheses; no model marking is assumed here.
Source: Aschbacher--Smith 10.2.9--12, pp.750--755.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE ChapterI.Section06To08 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem ti_noncommuting_pair_not_centralizing
    (W P : Subgroup G) [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 P]
    (hw : IsTISubgroup W) (hp : IsTISubgroup P)
    (hd : Disjoint W P) (he : Nat.card W = Nat.card P)
    (hnc : ⁅W,P⁆ ≠ ⊥) {b : G} (hb : b ∈ P) (hb1 : b ≠ 1) :
    b ∉ centralizer (W : Set G) := by
  intro hc
  have hne : P ⊓ centralizer (W : Set G) ≠ ⊥ := by
    intro hz
    exact hb1 (hz.le ⟨hb,hc⟩)
  have hf := ti_pair_full_normalizer_of_centralizer_ne_bot W P hd hp hne
  exact hnc (commutator_eq_bot_iff_le_centralizer.mpr
    (ti_pair_commute_of_full_normalizer W P hd hw hp he hf))

private theorem ti_pair_small_fixed_corank
    (W P A : Subgroup G) [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 P]
    (hw : IsTISubgroup W) (hp : IsTISubgroup P)
    (hd : Disjoint W P) (he : Nat.card W = Nat.card P)
    (hAP : A ≤ P) (hAN : A ≤ normalizer (W : Set G)) (hi : A.relIndex P ≤ 4)
    {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    subgroupCorank W (W ⊓ centralizer ({b} : Set G)) ≤ 2 := by
  let B := P ⊓ normalizer (W : Set G)
  let C := W ⊓ normalizer (P : Set G)
  have hBC : Nat.card B = Nat.card C :=
    ti_pair_mutual_normalizers_card_eq P W hd.symm hp hw he.symm
  have hC : C = W ⊓ centralizer ({b} : Set G) :=
    ti_pair_opposite_normalizer_eq_centralizer P W hd.symm hp (hAP hb) (hAN hb) hb1
  have hidx : C.relIndex W = B.relIndex P := by
    have hB := relIndex_mul_card_of_le (show B ≤ P from inf_le_left)
    have hC' := relIndex_mul_card_of_le (show C ≤ W from inf_le_left)
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := B))
    rw [hBC,hC',hBC.symm,hB,he]
  have hbound : B.relIndex P ≤ 4 :=
    (relIndex_le_of_le_left (le_inf hAP hAN) (show A.relIndex P ≠ 0 from index_ne_zero_of_finite)).trans hi
  change Nat.log 2 ((W ⊓ centralizer ({b} : Set G)).relIndex W) ≤ 2
  rw [←hC,hidx]
  exact (Nat.log_mono_right hbound).trans (by decide : Nat.log 2 4 ≤ 2)

private theorem small_moved_actor_not_commuting_component_image
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hz : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥)
    {b : G} (hbN : b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hb : b ∉ centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hsmall : subgroupCorank ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)) ≤ 2) :
    ⁅inducedAutomizer ⁅D.fullModule,L⁆ L,inducedAutomizer ⁅D.fullModule,L⁆ (zpowers b)⁆ ≠ ⊥ := by
  let W := ⁅D.fullModule,L⁆
  let := source_full_moved_elementary D
  let ρ := automizerRepresentation W
  have hLN : L ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  have hBN : zpowers b ≤ normalizer (W : Set G) := zpowers_le.mpr hbN
  let S := inducedAutomizer W L
  let A := inducedAutomizer W (zpowers b)
  let : Group.IsPerfect L := by
    let := D.maximal.1.1.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : Group.IsPerfect (L.subgroupOf (normalizer (W : Set G))) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLN).symm.toMonoidHom)
      (subgroupOfEquivOfLe hLN).symm.surjective
  let : Group.IsPerfect S := Group.IsPerfect.map _
  have hfix : Representation.BinaryOffender.fixedSpace ρ S = ⊥ := by
    apply bot_unique
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hz.le ⟨v.toMul.property,(mem_fixedSpace_inducedAutomizer W L hLN v).mp hv⟩
  have hnot : ¬ A ≤ ρ.ker := by
    intro hk
    have hkbot : ρ.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff ρ).mpr (automizerRepresentation_injective W)
    have hAbot : A = ⊥ := bot_unique (hk.trans_eq hkbot)
    exact hb ((inducedAutomizer_eq_bot_iff hBN).mp hAbot (mem_zpowers b))
  have hbound : Representation.BinaryOffender.fixedCodim ρ A ≤ 2 := by
    rw [fixedCodim_inducedAutomizer W (zpowers b) hBN]
    simpa only [zpowers_eq_closure, centralizer_closure] using hsmall
  intro hc
  have hh := Representation.BinaryOffender.three_le_fixedCodim_of_perfect_fixedSpace_eq_bot
    ρ S A hfix hnot hc
  omega

theorem moved_component_automizer_equiv
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nonempty ((inducedAutomizer ⁅D.fullModule,L⁆ L) ≃* (L ⧸ pCore 2 L)) := by
  let W := ⁅D.fullModule,L⁆
  let N := normalizer (W : Set G)
  have hLN : L ≤ N := normalizer_commutator_ge_right _ _
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  let β := W.normalizerMonoidHom.rangeRestrict
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
      (mem_map_of_mem L.subtype hl) v (hWV v.property)
    change (v : G) * (l : G) = (l : G) * (v : G) at hc
    rw [←hc,mul_inv_cancel_right]
  let fbar := QuotientGroup.lift (pCore 2 L) f hk
  have hs : Function.Surjective fbar := QuotientGroup.lift_surjective_of_surjective _ _ hf hk
  have hne : inducedAutomizer W L ≠ ⊥ := by
    intro he
    have hc := (inducedAutomizer_eq_bot_iff hLN).mp he
    have hh := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
    rw [source_full_moved_eq_commutator D] at hh
    exact source_full_moved_ne_bot D hh
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

theorem moved_ti_offender_component_stabilizer_injective
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hz : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥)
    {x : G}
    (hd : Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom))
    (hnc : ⁅⁅D.fullModule,L⁆,(⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom⁆ ≠ ⊥)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) ≤ 2)
    (hAN : (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ∃ f : ↥(((⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) ⊓
      normalizer (L : Set G)) →* MulAut (inducedAutomizer ⁅D.fullModule,L⁆ L),
      Function.Injective f := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj x).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let N := normalizer (W : Set G)
  let S := inducedAutomizer W L
  let B := A ⊓ normalizer (L : Set G)
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have hp : IsTISubgroup P := hti.map_equiv (MulAut.conj x)
  have he : Nat.card W = Nat.card P := (card_map_of_injective (MulAut.conj x).injective).symm
  have hBN : B ≤ N := inf_le_left.trans hAN
  let β := W.normalizerMonoidHom.rangeRestrict
  let f : B →* Automizer W := β.comp (inclusion hBN)
  have hf (b : B) : f b ∈ normalizer (S : Set (Automizer W)) := by
    have hb : (inclusion hBN b) ∈ normalizer (L.subgroupOf N : Set N) := by
      rw [mem_normalizer_iff]
      intro y
      exact mem_normalizer_iff.mp b.property.2 y
    exact (L.subgroupOf N).le_normalizer_map β ⟨inclusion hBN b,hb,rfl⟩
  let fN : B →* normalizer (S : Set (Automizer W)) := f.codRestrict _ hf
  let α : B →* MulAut S := S.normalizerMonoidHom.comp fN
  have hi : Function.Injective α := by
    apply (injective_iff_map_eq_one _).mpr
    intro b hb
    by_contra hb1
    have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hnot := ti_noncommuting_pair_not_centralizing W P hti hp hd he hnc b.property.1.1 hb1'
    have hr := ti_pair_small_fixed_corank W P A hti hp hd he inf_le_left hAN
      (moved_intersection_index_le D hsmall) b.property.1 hb1'
    apply small_moved_actor_not_commuting_component_image D hz (hBN b.property) hnot hr
    have hcent : f b ∈ centralizer (S : Set (Automizer W)) := by
      have hh : fN b ∈ S.normalizerMonoidHom.ker := hb
      rw [Subgroup.normalizerMonoidHom_ker] at hh
      exact hh
    have hA : inducedAutomizer W (zpowers (b : G)) ≤ centralizer (S : Set (Automizer W)) := by
      rintro y ⟨n,hn,rfl⟩
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp hn
      have he : n = (inclusion hBN b) ^ k := Subtype.ext hk.symm
      rw [he,map_zpow]
      exact (centralizer (S : Set (Automizer W))).zpow_mem hcent k
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hA)
  exact ⟨α,hi⟩

theorem moved_ti_binary_three_card_le_sixtyfour
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hz : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    {x : G}
    (hd : Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom))
    (hnc : ⁅⁅D.fullModule,L⁆,(⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom⁆ ≠ ⊥)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) ≤ 2)
    (hAN : (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) ≤ 64 := by
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
  exact hPb

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
