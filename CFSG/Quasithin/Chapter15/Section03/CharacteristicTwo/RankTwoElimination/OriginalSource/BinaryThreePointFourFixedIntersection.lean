module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourStandardModel
public import Theory.Representation.BinaryEndpointInduction.SurvivorFixedSpace

/-!
# The original binary-four span has trivial fixed intersection

The recognized whole component action has zero common fixed space for the
literal original endpoint parabolic. Pulling its four actors back through
the unchanged point quotient proves that the actual conjugate span has no
element centralized by L. In particular its intersection with the original
intrinsic four is trivial, strengthening the previous order-two bound.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open BinaryEndpointInduction
variable {G : Type*} [Group G] [Finite G]

/-- The whole original central span has no component-fixed point, and is
disjoint from the actual intrinsic four. -/
theorem binary_three_source_four_fixed_intersection
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
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ (centralizer ({z} : Set G))
    W ⊓ centralizer (c.L : Set G)=⊥ ∧ W ⊓ intrinsicFour c.L=⊥ := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  obtain ⟨hW,σ,hσ,_,_,eK,heK,dual,E,hE⟩ :=
    binary_three_source_four_standard_model
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  let := hW
  have hfix : W ⊓ centralizer (c.L : Set G)=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    let w : Additive W := Additive.ofMul ⟨x,hx.1⟩
    have hz : E w=0 := by
      apply survivor_parabolic_fixed_eq_zero dual (E w)
      intro k
      let u := eK.symm (parabolicGenerator k)
      have hu : (u : C ⧸ pCore 2 C) ∈ B := by
        have hp : parabolicGenerator k ∈ (B.subgroupOf K).map eK.toMonoidHom := by
          rw [heK]
          exact parabolicGenerator_mem_endpoint k
        obtain ⟨v,hv,he⟩ := hp
        have hvu : v=u := eK.injective (he.trans (eK.apply_symm_apply _).symm)
        exact hvu ▸ hv
      obtain ⟨l,hl,hlq⟩ := hu
      have hσw : σ u.val w=w := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [←hlq,hσ]
        change (l:G)*x*(l:G)⁻¹=x
        rw [hx.2 l hl,mul_inv_cancel_right]
      have hh := hE u w
      rw [hσw,eK.apply_symm_apply] at hh
      exact hh.symm
    have hw : w=0 := E.injective (hz.trans E.map_zero.symm)
    exact congrArg (fun v : Additive W => (v.toMul:G)) hw
  refine ⟨hfix,?_⟩
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hH := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2
  apply le_antisymm _ bot_le
  exact (inf_le_inf_left W (hH.trans inf_le_right)).trans hfix.le

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
