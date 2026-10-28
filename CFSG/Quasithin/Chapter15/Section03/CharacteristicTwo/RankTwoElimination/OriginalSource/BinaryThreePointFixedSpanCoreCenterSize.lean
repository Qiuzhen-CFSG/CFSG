module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCoreCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanComponentWitness
public import Theory.GroupAction.SymplecticSmallTwoSection
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Growth of the actual normalizer-core center

The promoted PSL5(2) quotient has a factor 31, so it fixes every two-section
of order at most 16. If the core center modulo U were that small, the
original L would move its center into U. Its exact moved subgroup is
Phi(Q), of order 256, whereas U has order 32. Thus the actual center has
order at least 1024.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The promoted action forces another factor of two beyond the original
fixed-span and moving-span product in the full core center. -/
theorem binary_three_source_fixed_span_core_center_size
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
    let F := (normalizer (U : Set G)).pCoreIn 2
    let ZF := (center F).map F.subtype
    32 ≤ U.relIndex ZF ∧ 1024 ≤ Nat.card ZF := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  let F := A.pCoreIn 2
  let ZF := (center F).map F.subtype
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  obtain ⟨D,hD,hDn,hLD,hfull,hker,hJ,hSJ,hchar,htwoJ,hJA,
    c5,hc5,⟨e5⟩,hY,hθJ,hθNU,hθM⟩ :=
    binary_three_source_fixed_span_component_witness
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  have hBA : c5.L ≤ A := by
    rw [hc5]
    exact map_subtype_le D
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hLA : c.L ≤ A := le_sup_left.trans hout.2.1
  have hLB : c.L ≤ c5.L := by
    rw [hc5]
    intro x hx
    exact ⟨⟨x,hLA hx⟩,hLD hx,rfl⟩
  have hAZ : A ≤ normalizer (ZF : Set G) := A.le_normalizer.trans
    ((normalizer_le_normalizer_characteristic_image A (pCore 2 A)).trans
      (normalizer_le_normalizer_characteristic_image F (center F)))
  have hBZ : c5.L ≤ normalizer (ZF : Set G) := hBA.trans hAZ
  have hBU : c5.L ≤ normalizer (U : Set G) := hBA
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUF : U ≤ F := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) U.le_normalizer le_rfl
  have hFU : F ≤ centralizer (U : Set G) := by
    have he : F = (centralizer ({z} : Set G)).pCoreIn 2 ⊓ centralizer (U : Set G) :=
      binary_three_source_fixed_span_normalizer_core
        hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
          K hK hKn hLK eB hrX hrB hm
    exact he.le.trans inf_le_right
  have hUZ : U ≤ ZF := by
    intro x hx
    exact ⟨⟨x,hUF hx⟩,mem_center_iff.mpr
      (fun y => Subtype.ext ((hFU y.property) x hx).symm),rfl⟩
  have hZU : ZF ≤ normalizer (U : Set G) :=
    ((map_subtype_le _).trans hFU).trans (Subgroup.centralizer_le_normalizer _)
  let : (U.subgroupOf ZF).Normal := (normal_subgroupOf_iff_le_normalizer hUZ).mpr hZU
  have hZp : IsPGroup 2 ZF := (A.isPGroup_pCoreIn 2).to_le (map_subtype_le _)
  let S5 := c5.L ⧸ pCore 2 c5.L
  let : IsSimpleGroup PSL(5,ZMod 2) := Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup S5 := e5.isSimpleGroup
  have h31 : 31 ∣ Nat.card S5 := by
    rw [Nat.card_congr e5.toEquiv,
      Nat.card_congr (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)).toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 5).toEquiv,
      Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hperfect : Group.IsPerfect c5.L := by
    have hh := c5.component.perfect
    let := hh
    let f := subgroupOfEquivOfLe c5.le_thompson
    exact Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  let := hperfect
  have hpB : IsPPerfect 2 c5.L := by
    intro H hH hquot
    let : H.Normal := hH
    by_contra hne
    let : Nontrivial (c5.L ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent (c5.L ⧸ H) := hquot.isNilpotent
    exact Group.IsPerfect.not_isSolvable (c5.L ⧸ H) inferInstance
  have horder : 4 < orderOf (2 : ZMod 31) := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have he : orderOf (2 : ZMod 31) = 5 :=
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    omega
  have hi : ¬ U.relIndex ZF ≤ 16 := by
    intro hsmall
    have hmove : ⁅ZF,c5.L⁆ ≤ U :=
      commutator_component_le_of_primitive_small_section c5.L ZF U
        hpB (QuotientGroup.mk' (pCore 2 c5.L))
        (QuotientGroup.mk'_surjective _) (by
          rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
        (show Nat.Prime 31 by decide) h31 hZp hsmall
        horder hBZ hBU
    have hPhiU : Phi ≤ U :=
      (binary_three_source_fixed_span_core_center
        hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
          K hK hKn hLK eB hrX hrB hm).2.2.symm.le.trans
        ((commutator_mono le_rfl hLB).trans hmove)
    have hPhiCard : Nat.card Phi = 256 := by
      change Nat.card ((frattini Q).map Q.subtype) = 256
      rw [card_map_of_injective Q.subtype_injective]
      exact (binary_three_large_distance_original_core_structure
        hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.1
    have hUc : Nat.card U = 32 := binary_three_source_four_fixed_span_order
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
    have hn := card_le_of_le hPhiU
    rw [hPhiCard,hUc] at hn
    omega
  obtain ⟨n,hn⟩ := (hZp.to_quotient (U.subgroupOf ZF)).exists_card_eq
  change U.relIndex ZF = 2 ^ n at hn
  have hindex : 32 ≤ U.relIndex ZF := by
    have hlarge : 5 ≤ n := by
      by_contra hh
      have hb : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
      exact hi (hn.trans_le hb)
    rw [hn]
    exact Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide) hlarge
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) U ZF bot_le hUZ
  rw [relIndex_bot_left,relIndex_bot_left] at hcard
  have hUc : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  rw [hUc] at hcard
  refine ⟨hindex,?_⟩
  calc
    1024 = 32 * 32 := rfl
    _ ≤ 32 * U.relIndex ZF := Nat.mul_le_mul_left 32 hindex
    _ = Nat.card ZF := hcard

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
