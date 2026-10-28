module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeCrossCore
public import Theory.SpecificGroups.PSL3Two.SylowNormalizedTwoCore

/-!
# The opposite binary core has a full parabolic four-group image

The original opposite core has nontrivial image in LS/O₂(LS), normalized by
the full Sylow two-image and by an actual residual cubic. The binary model
therefore identifies this literal image as a self-centralizing elementary
four-group. Consequently every cubic in LS moves the opposite core.

This supplies a mixed-component action constraint for the original large
binary branch. It does not infer commutation between different conjugates
of a cubic or a rank-three elementary subgroup.

Source: Aschbacher–Smith 15.3.23, printed pp.1128–1129; the binary parabolic
calculation is I.5.4 and I.5.7, printed pp.420–421.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem cubic_image_order {J H : Type*} [Group J] [Group H]
    (f : J →* H) (hp : IsPGroup 2 f.ker) (x : J) (hx : orderOf x = 3) :
    orderOf (f x) = 3 := by
  apply orderOf_eq_prime
  · rw [←map_pow, ←hx, pow_orderOf_eq_one, map_one]
  · intro hh
    have hm : x ∈ f.ker := hh
    have hcop := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x,hm⟩ : f.ker)
    have ho : orderOf (⟨x,hm⟩ : f.ker) = 3 := (Subgroup.orderOf_coe _).symm.trans hx
    rw [ho] at hcop
    norm_num at hcop

/-- The original opposite core maps onto the self-centralizing four-radical
of a binary parabolic under the literal overgroup projection. -/
theorem binary_three_source_conjugate_core_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (a : G) (ha : a ∈ (d.T : Subgroup G)) (haS : a ∉ d.S) :
    let N := (((LinearThree.commutatorCore c.L).conjBy a).subgroupOf (c.L ⊔ d.S)).map
      b.coreProjection
    IsElementaryAbelian 2 N ∧ Nat.card N = 4 ∧
      centralizer (N : Set Matrix.PSL3Two.SL) ≤ N := by
  dsimp only
  let J := c.L ⊔ d.S
  let N := (((LinearThree.commutatorCore c.L).conjBy a).subgroupOf J).map b.coreProjection
  obtain ⟨hN0,hN2,hNorm,_⟩ := binary_three_source_conjugate_core_image
    hG d hempty hM hu hmany hI htwo hf c e b a ha haS
  obtain ⟨P,hP⟩ := binary_three_exists_marked_sylow hG d hempty hM hu hmany hI c
  let Pbar := P.mapSurjective b.coreProjection_surjective
  have hPN : (Pbar : Subgroup Matrix.PSL3Two.SL) ≤ normalizer (N : Set Matrix.PSL3Two.SL) := by
    change (P : Subgroup J).map b.coreProjection ≤ _
    rw [←hP]
    exact (map_mono (subgroupOf_mono J (show d.S ≤ d.Y ⊔ d.S from le_sup_right))).trans hNorm
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  have hd : 3 ∣ Nat.card (YL d c.L) := by
    apply Nat.dvd_of_factorization_pos
    intro hn
    have he := h.component_three_part
    rw [hn,pow_zero] at he
    omega
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := YL d c.L) 3 hd
  have hVL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  let vJ : J := ⟨v, (show c.L ≤ J from le_sup_left) (hVL v.property)⟩
  have hvJ : orderOf vJ = 3 :=
    (Subgroup.orderOf_coe vJ).symm.trans ((Subgroup.orderOf_coe v).trans hv)
  have hp : IsPGroup 2 b.coreProjection.ker := by
    rw [b.coreProjection_kernel]
    exact pCore_isPGroup
  have hvo := cubic_image_order b.coreProjection hp vJ hvJ
  have hvn : b.coreProjection vJ ∈ normalizer (N : Set Matrix.PSL3Two.SL) := by
    apply hNorm
    apply mem_map_of_mem b.coreProjection
    change (v : G) ∈ d.Y ⊔ d.S
    apply mem_sup_left
    rw [hg.generation]
    exact mem_sup_left v.property
  exact ⟨(Matrix.PSL3Two.SylowNormalizedTwoCore.recognize N Pbar hN2 hN0 hPN
    (b.coreProjection vJ) hvn hvo).1,
    (Matrix.PSL3Two.SylowNormalizedTwoCore.recognize N Pbar hN2 hN0 hPN
    (b.coreProjection vJ) hvn hvo).2,
    Matrix.PSL3Two.SylowNormalizedTwoCore.centralizer_le N Pbar hN2 hN0 hPN
    (b.coreProjection vJ) hvn hvo⟩

/-- Every cubic of the original overgroup moves the opposite commutator core.
The conclusion concerns actual elements, not just abstract chief factors. -/
theorem binary_three_source_cubic_moves_conjugate_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (a : G) (ha : a ∈ (d.T : Subgroup G)) (haS : a ∉ d.S)
    (x : (c.L ⊔ d.S : Subgroup G)) (hx : orderOf (x : G) = 3) :
    (x : G) ∉ centralizer ((LinearThree.commutatorCore c.L).conjBy a : Set G) := by
  let J := c.L ⊔ d.S
  let N := (((LinearThree.commutatorCore c.L).conjBy a).subgroupOf J).map b.coreProjection
  obtain ⟨hN2,_,hNC⟩ := binary_three_source_conjugate_core_four
    hG d hempty hM hu hmany hI htwo hf c e b a ha haS
  let := hN2
  have hp : IsPGroup 2 b.coreProjection.ker := by
    rw [b.coreProjection_kernel]
    exact pCore_isPGroup
  have hxo : orderOf (b.coreProjection x) = 3 := cubic_image_order b.coreProjection hp x
    ((Subgroup.orderOf_coe x).symm.trans hx)
  intro hxc
  have hfx : b.coreProjection x ∈ centralizer (N : Set Matrix.PSL3Two.SL) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨q,hq,rfl⟩
    have he : q * x = x * q := Subtype.ext ((mem_centralizer_iff.mp hxc) q hq)
    rw [←map_mul, ←map_mul, he]
  have hxm : b.coreProjection x ∈ N := hNC hfx
  have hcop := (IsElementaryAbelian.isPGroup 2 N).orderOf_coprime
    (by decide : Nat.Coprime 2 3) (⟨b.coreProjection x,hxm⟩ : N)
  have ho : orderOf (⟨b.coreProjection x,hxm⟩ : N) = 3 :=
    (Subgroup.orderOf_coe _).symm.trans hxo
  rw [ho] at hcop
  norm_num at hcop


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
