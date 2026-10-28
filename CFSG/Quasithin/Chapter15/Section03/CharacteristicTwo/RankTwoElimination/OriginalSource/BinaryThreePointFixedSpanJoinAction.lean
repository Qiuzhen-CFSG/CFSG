module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanComponentWitness
public import Theory.GroupTheory.JoinActionKernel

/-!
# Exact full action of the promoted Sylow join

The actual promoted component has two-core kernel. Its Sylow supplement
is a two-group, so the entire Sylow join still has a two-group kernel.
Surjectivity onto the full elementary automorphism group then identifies
that kernel with the intrinsic two-core of the join.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The same promoted Sylow join induces the full U action with exactly its
own two-core as kernel, retaining the original containing component. -/
theorem binary_three_source_fixed_span_join_action
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
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
    let A := normalizer (U : Set G)
    ∃ D : Subgroup A, D.IsCComponent ∧ D.Normal ∧ c.L.subgroupOf A ≤ D ∧
      let B := D.map A.subtype
      let J := B ⊔ d.S
      J ∈ d.Hplus ∧ Chapter1.IsSylowIn 2 d.S J ∧ HasCharacteristicTwo J ∧
      d.Yplus ≤ B ∧ ∃ hJA : J ≤ A,
        Function.Surjective (U.normalizerMonoidHom.comp (inclusion hJA)) ∧
        (U.normalizerMonoidHom.comp (inclusion hJA)).ker = pCore 2 J := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  obtain ⟨D,hD,hDn,hLD,hfull,hker,hJ,hSJ,hchar,_,hJA,c5,hc5,_,hY,_⟩ :=
    binary_three_source_fixed_span_component_witness
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  let B := D.map A.subtype
  let J := B ⊔ d.S
  let f : J →* MulAut U := U.normalizerMonoidHom.comp (inclusion hJA)
  let fD : D →* MulAut U := U.normalizerMonoidHom.comp D.subtype
  have hBJ : B ≤ J := le_sup_left
  have hBA : B ≤ A := map_subtype_le D
  have hBAeq : B.subgroupOf A = D := by
    exact comap_map_eq_self_of_injective A.subtype_injective D
  have hBnA : (B.subgroupOf A).Normal := hBAeq.symm ▸ hDn
  let : (B.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBJ).mpr
      (hJA.trans ((normal_subgroupOf_iff_le_normalizer hBA).mp hBnA))
  let aB : D ≃* B := D.equivMapOfInjective A.subtype A.subtype_injective
  let a : B.subgroupOf J ≃* D := (subgroupOfEquivOfLe hBJ).trans aB.symm
  have haval (x : B.subgroupOf J) : ((a x : A) : G) = ((x : J) : G) := by
    exact congrArg Subtype.val (aB.apply_symm_apply ((subgroupOfEquivOfLe hBJ) x))
  have hcomp : f.comp (B.subgroupOf J).subtype = fD.comp a.toMonoidHom := by
    ext x u
    change ((x : J) : G) * (u : G) * (((x : J) : G))⁻¹ =
      ((a x : A) : G) * (u : G) * (((a x : A) : G))⁻¹
    rw [haval]
  have hkerp : IsPGroup 2 (f.comp (B.subgroupOf J).subtype).ker := by
    rw [hcomp,←MonoidHom.comap_ker]
    have hp : IsPGroup 2 fD.ker := hker.symm ▸ pCore_isPGroup
    exact hp.comap_of_injective a.toMonoidHom a.injective
  have hSp : IsPGroup 2 (d.S.subgroupOf J) :=
    (d.T.isPGroup'.to_le inf_le_left).of_equiv
      (subgroupOfEquivOfLe (show d.S ≤ J from le_sup_right)).symm
  have hjoin : B.subgroupOf J ⊔ d.S.subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hBJ (show d.S ≤ J from le_sup_right),subgroupOf_self]
  have hkerle : f.ker ≤ pCore 2 J :=
    f.ker_le_pCore_of_normal_join (B.subgroupOf J) (d.S.subgroupOf J) hSp hjoin hkerp
  have hfsurj : Function.Surjective f := by
    intro g
    obtain ⟨x,hx⟩ := hfull g
    exact ⟨⟨x.val.val,hBJ ⟨x.val,x.property,rfl⟩⟩,hx⟩
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hmap : (pCore 2 J).map f ≤ pCore 2 (MulAut U) :=
    le_sSup ⟨Normal.map inferInstance f hfsurj,pCore_isPGroup.map f⟩
  rw [MulAut.twoCore_eq_bot_of_elementary_two U] at hmap
  have hleker : pCore 2 J ≤ f.ker := by
    intro x hx
    exact hmap (mem_map_of_mem f hx)
  refine ⟨D,hD,hDn,hLD,hJ,hSJ,hchar,?_,hJA,hfsurj,le_antisymm hkerle hleker⟩
  exact hc5 ▸ hY

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
