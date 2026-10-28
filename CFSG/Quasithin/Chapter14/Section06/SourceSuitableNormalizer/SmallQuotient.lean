module

public import Theory.GroupTheory.ElementaryThompsonTwoLayers
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import CFSG.Quasithin.ChapterC.Section06.Original.ModelOrbit
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer.SingleBlock

/-!
# The small quotient of the suitable normalizer

This proves the intrinsic group-theoretic step in Aschbacher--Smith
14.6.3(4), printed pp.1021--1022. A normal two-subgroup U of index two in
a proper Sylow subgroup S is the two-core once characteristic normalizer
control is imposed. The proved C.1.29 ordered product selects actual blocks;
solvability makes them A₃ blocks, each normalized by S.

Two distinct selected blocks have disjoint elementary module layers. Every
element outside U moves both layers, so the elementary Thompson bound forces
J(S) into U, contradicting the selected blocks' movement. Thus a single
normal A₃ block generates with S and is the two-residual. Its index-three
Sylow action gives the S₃ quotient needed by the original C.6 application.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.SuitableSmallQuotient
variable {G : Type*} [Group G] [Finite G]

private theorem sup_eq_of_index_two (S U A : Subgroup G) (hUS : U ≤ S) (hAS : A ≤ S)
    (hi : U.relIndex S = 2) (hn : ¬ A ≤ U) : U ⊔ A = S := by
  have hsup : U ⊔ A ≤ S := sup_le hUS hAS
  have hh := relIndex_mul_relIndex U (U ⊔ A) S le_sup_left hsup
  rw [hi] at hh
  have hone : U.relIndex (U ⊔ A) ≠ 1 := fun he =>
    hn (le_sup_right.trans (relIndex_eq_one.mp he))
  have hp : 0 < (U ⊔ A).relIndex S := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hp' : 0 < U.relIndex (U ⊔ A) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hlarge : 2 ≤ U.relIndex (U ⊔ A) := by omega
  exact le_antisymm hsup (relIndex_eq_one.mp (by nlinarith))

private theorem core_eq_normal_half_sylow (S : Sylow 2 G) (U : Subgroup G) [U.Normal]
    (hU : IsPGroup 2 U) (hUS : U ≤ (S : Subgroup G)) (hi : U.relIndex (S : Subgroup G) = 2)
    (hproper : (S : Subgroup G) ≠ ⊤)
    (hcpu : (S : Subgroup G).characteristicNormalizerClosure ≤ (S : Subgroup G)) :
    pCore 2 G = U := by
  have hUQ : U ≤ pCore 2 G := (show U ≤ pCore 2 G from le_sSup ⟨inferInstance,hU⟩)
  have hQS : pCore 2 G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  by_contra hn
  have hjoin : U ⊔ pCore 2 G = (S : Subgroup G) :=
    sup_eq_of_index_two _ _ _ hUS hQS hi (fun hh => hn (le_antisymm hh hUQ))
  rw [sup_eq_right.mpr hUQ] at hjoin
  have hSnontriv : (S : Subgroup G) ≠ ⊥ := by
    intro hs
    have hu : U = ⊥ := bot_unique (hs ▸ hUS)
    rw [hs,hu,relIndex_self] at hi
    contradiction
  apply hproper
  apply top_unique
  have hh := (normalizer_le_characteristicNormalizerClosure_self (S : Subgroup G) hSnontriv).trans hcpu
  rw [←hjoin,normalizer_eq_top] at hh
  exact hjoin ▸ hh

private theorem moved_block_sylow_normalizes
    (S : Sylow 2 G) (U K : Subgroup G) [U.Normal]
    (hU : IsPGroup 2 U) (hUS : U ≤ (S : Subgroup G)) (hi : U.relIndex (S : Subgroup G) = 2)
    (hb : ChapterC.IsBlock K) (hout : ¬K ≤ (S : Subgroup G))
    (hm : K = ⁅K,elementaryAbelianMaxJ (S : Subgroup G)⁆) :
    (S : Subgroup G) ≤ normalizer (K : Set G) := by
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  have hJU : ¬J ≤ U := by
    intro hh
    apply hout
    rw [hm]
    exact ((commutator_mono le_rfl hh).trans (commutator_le_right K U)).trans hUS
  have hgen : U ⊔ J = (S : Subgroup G) :=
    sup_eq_of_index_two _ _ _ hUS (sSup_le fun _ hA => hA.1) hi hJU
  rw [←hgen]
  apply sup_le
  · exact le_normalizer_of_isSubnormal_isPPerfect K U hb.subnormal hb.short.twoPerfect hU
      le_normalizer_of_normal
  · rw [hm]
    exact normalizer_commutator_ge_right K J

omit [Finite G] in
private theorem moved_module_sylow_not_central
    (S : Sylow 2 G) (K : Subgroup G) (hb : ChapterC.IsBlock K)
    (ha : ChapterC.IsAlternatingBlock K 3)
    (hm : K = ⁅K,elementaryAbelianMaxJ (S : Subgroup G)⁆) :
    ¬ (S : Subgroup G) ≤ centralizer ((ChapterC.blockU K).map K.subtype : Set G) := by
  let W := (ChapterC.blockU K).map K.subtype
  have hKN : K ≤ normalizer (W : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
  intro hc
  have hKC : K ≤ centralizer (W : Set G) := by
    rw [hm]
    exact (commutator_mono le_rfl ((sSup_le fun _ hA => hA.1).trans hc)).trans
      (le_normalizer_iff_commutator_le_right.mp (hKN.trans (normalizer_le_normalizer_centralizer W)))
  have hzero : ChapterC.blockU K = ⊥ := by
    apply eq_bot_iff.mpr
    intro w hw
    have hc : w ∈ center K := mem_center_iff.mpr (fun k =>
      Subtype.ext ((hKC k.property w (mem_map_of_mem K.subtype hw)).symm))
    exact ha.center_eq_bot ▸ hc
  exact hb.short.blockU_ne_bot hzero

private theorem outside_half_moves_module
    (S : Sylow 2 G) (U K : Subgroup G) [U.Normal]
    (hU : IsPGroup 2 U) (hUS : U ≤ (S : Subgroup G)) (hi : U.relIndex (S : Subgroup G) = 2)
    (hb : ChapterC.IsBlock K) (ha : ChapterC.IsAlternatingBlock K 3)
    (hm : K = ⁅K,elementaryAbelianMaxJ (S : Subgroup G)⁆) :
    ∀ a ∈ (S : Subgroup G), a ∉ U →
      a ∉ centralizer ((ChapterC.blockU K).map K.subtype : Set G) := by
  intro a haS haU haC
  have he : U ⊔ zpowers a = (S : Subgroup G) :=
    sup_eq_of_index_two _ _ _ hUS (zpowers_le.mpr haS) hi
      (fun hh => haU (hh (mem_zpowers a)))
  apply moved_module_sylow_not_central S K hb ha hm
  rw [←he]
  exact sup_le (((show U ≤ pCore 2 G from le_sSup ⟨inferInstance,hU⟩)).trans hb.core_centralizes_blockU) (zpowers_le.mpr haC)

private theorem moved_blocks_equal
    (hf : generalizedFitting G = pCore 2 G)
    (S : Sylow 2 G) (U K L : Subgroup G) [U.Normal]
    (hU : IsPGroup 2 U) (hUS : U ≤ (S : Subgroup G)) (hi : U.relIndex (S : Subgroup G) = 2)
    (hcore : pCore 2 G = U)
    (hbK : ChapterC.IsBlock K) (haK : ChapterC.IsAlternatingBlock K 3)
    (hbL : ChapterC.IsBlock L) (haL : ChapterC.IsAlternatingBlock L 3)
    (houtK : ¬ K ≤ (S : Subgroup G)) (houtL : ¬ L ≤ (S : Subgroup G))
    (hmK : K = ⁅K,elementaryAbelianMaxJ (S : Subgroup G)⁆)
    (hmL : L = ⁅L,elementaryAbelianMaxJ (S : Subgroup G)⁆) : K = L := by
  by_contra hne
  let V := (ChapterC.blockU K).map K.subtype
  let W := (ChapterC.blockU L).map L.subtype
  let : IsElementaryAbelian 2 (ChapterC.blockU K) := hbK.short.elementary
  let : IsElementaryAbelian 2 (ChapterC.blockU L) := hbL.short.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hKL : K ≤ centralizer (L : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (ChapterC.blocks_commute (ChapterC.RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf)
      hbK hbL hne)
  have hdKL : Disjoint K L := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hz : (⟨x,hx.1⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun y => Subtype.ext ((hKL y.property x hx.2).symm))
    rw [haK.center_eq_bot,mem_bot] at hz
    exact congrArg Subtype.val hz
  have hJ : elementaryAbelianMaxJ (S : Subgroup G) ≤ U := by
    apply thompson_le_of_two_moved_layers (S : Subgroup G) U V W hUS hi.le
    · rw [←hcore]
      exact (map_mono ChapterC.blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hbK.subnormal)
    · rw [←hcore]
      exact (map_mono ChapterC.blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hbL.subnormal)
    · rw [←hcore]
      exact le_centralizer_iff.mp hbK.core_centralizes_blockU
    · rw [←hcore]
      exact le_centralizer_iff.mp hbL.core_centralizes_blockU
    · exact hdKL.mono (map_subtype_le _) (map_subtype_le _)
    · exact (moved_block_sylow_normalizes S U K hU hUS hi hbK houtK hmK).trans
        (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
    · exact (moved_block_sylow_normalizes S U L hU hUS hi hbL houtL hmL).trans
        (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
    · exact outside_half_moves_module S U K hU hUS hi hbK haK hmK
    · exact outside_half_moves_module S U L hU hUS hi hbL haL hmL
  apply houtK
  rw [hmK]
  exact ((commutator_mono le_rfl hJ).trans (commutator_le_right K U)).trans hUS

/-- The original local C theorem yields one actual normal A₃ block. -/
theorem exists_single_alternatingThree
    (hs : Group.IsSolvable G) (hqt : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G)
    (S : Sylow 2 G) (U : Subgroup G) [U.Normal]
    (hU : IsPGroup 2 U) (hUS : U ≤ (S : Subgroup G)) (hi : U.relIndex (S : Subgroup G) = 2)
    (hproper : (S : Subgroup G) ≠ ⊤)
    (hcpu : (S : Subgroup G).characteristicNormalizerClosure ≤ (S : Subgroup G)) :
    ∃ K : Subgroup G, K.Normal ∧ ChapterC.IsAlternatingBlock K 3 ∧
      K ⊔ (S : Subgroup G) = ⊤ ∧ pResidual 2 G = K := by
  classical
  let := hs
  obtain ⟨r,hr,L,hL,hout,hm,hprod⟩ :=
    ChapterC.RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple
      hqt hf S (S : Subgroup G) hcpu
  have ha (i) : ChapterC.IsAlternatingBlock (L i) 3 :=
    ChapterC.Section06.Original.chiZero_cubic_of_solvable (hL i).2
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    subst r
    apply hproper
    apply top_unique
    intro g _
    obtain ⟨s,b,hg⟩ := hprod g
    simp only [List.ofFn_zero,List.prod_nil,mul_one] at hg
    exact hg ▸ s.property
  let i : Fin r := ⟨0,hrpos⟩
  let K := L i
  have he (j) : L j = K := moved_blocks_equal hf S U (L j) K hU hUS hi
    (core_eq_normal_half_sylow S U hU hUS hi hproper hcpu)
    (hL j).1 (ha j) (hL i).1 (ha i) (hout j) (hout i) (hm j) (hm i)
  have hgen : K ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨s,b,hg⟩ := hprod g
    rw [hg]
    apply (K ⊔ (S : Subgroup G)).mul_mem (mem_sup_right s.property)
    apply mem_sup_left
    exact K.list_prod_mem (fun a ha => by
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
      exact he j ▸ (b j).property)
  have hn : K.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸
    sup_le K.le_normalizer (moved_block_sylow_normalizes S U K hU hUS hi
      (hL i).1 (hout i) (hm i))))
  let := hn
  exact ⟨K,hn,ha i,hgen,pResidual_eq_of_isPPerfect_sup K (S : Subgroup G)
    (hL i).1.short.twoPerfect S.isPGroup' hgen⟩


/-- The actual normal half-Sylow subgroup is the two-core, with the single
A₃ residual and S₃ quotient required by the original C.6 application. -/
theorem small_quotient_and_residual
    (hs : Group.IsSolvable G) (hqt : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G)
    (S : Sylow 2 G) (U : Subgroup G) [U.Normal]
    (hU : IsPGroup 2 U) (hUS : U ≤ (S : Subgroup G)) (hi : U.relIndex (S : Subgroup G) = 2)
    (hproper : (S : Subgroup G) ≠ ⊤)
    (hcpu : (S : Subgroup G).characteristicNormalizerClosure ≤ (S : Subgroup G)) :
    pCore 2 G = U ∧ ChapterC.IsAlternatingBlock (pResidual 2 G) 3 ∧
      Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  have hcore := core_eq_normal_half_sylow S U hU hUS hi hproper hcpu
  obtain ⟨K,hn,hK,hgen,hres⟩ := exists_single_alternatingThree hs hqt hf S U hU hUS hi hproper hcpu
  let := hn
  have hnoncore : ¬ (S : Subgroup G) ≤ pCore 2 G := by
    intro hh
    rw [hcore] at hh
    have hone := relIndex_eq_one.mpr hh
    omega
  exact ⟨hcore,hres.symm ▸ hK,
    SourceSuitableNormalizer.quotient_equiv_perm_three_of_normal_alternatingThree S K hK hgen hnoncore⟩

end CFSG.Quasithin.Chapter14.Section06.SuitableSmallQuotient
