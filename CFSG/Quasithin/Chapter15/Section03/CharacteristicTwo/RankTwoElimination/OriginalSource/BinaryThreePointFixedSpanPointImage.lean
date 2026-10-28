module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanKernelIndex
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointBinaryFaithfulSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourEndpointEquality
public import Theory.GroupAction.ElementaryThirtyTwoPointEnlargement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The whole point stabilizer acts on the original fixed span

The original point kernel has image of order 16 on U. The containing
component acts faithfully modulo the original point line, with order 20160.
The full action on U therefore has order at least 16 times 20160, which is
exactly the order of the point stabilizer on the elementary group of order32.
This identifies the literal conjugation image and retains its full kernel.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private theorem image_card_lower_from_section
    {A B D : Type*} [Group A] [Group B] [Group D] [Finite A]
    (f : A →* B) (g : A →* D) (N K : Subgroup A) [N.Normal]
    (hfg : f.ker ≤ g.ker) (hNg : N ≤ g.ker) (hgK : g.ker ⊓ K ≤ N)
    {m : ℕ} (hfN : f.ker.relIndex N = m) :
    m * N.relIndex K ≤ Nat.card f.range := by
  let J := f.ker ⊔ N
  have hJg : J ≤ g.ker := sup_le hfg hNg
  have hsub : J.subgroupOf K = N.subgroupOf K := by
    ext k
    constructor
    · intro hk
      exact hgK ⟨hJg hk,k.property⟩
    · exact fun hk => mem_sup_right hk
  have hJK : J.relIndex K = N.relIndex K := congrArg Subgroup.index hsub
  have hbound : N.relIndex K ≤ J.index := by
    rw [←hJK]
    exact Nat.le_of_dvd (show 0 < J.index from Nat.card_pos)
      (relIndex_dvd_index_of_normal J K)
  have hmul := relIndex_mul_index (show f.ker ≤ J from le_sup_left)
  change f.ker.relIndex (f.ker ⊔ N) * J.index = f.ker.index at hmul
  rw [relIndex_sup_left,hfN,index_ker] at hmul
  exact (Nat.mul_le_mul_left m hbound).trans_eq hmul

variable {G : Type*} [Group G] [Finite G]

/-- The actual point centralizer induces every automorphism of U fixing
its original nonidentity point z. -/
theorem binary_three_source_fixed_span_point_image
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
    let C := centralizer ({z} : Set G)
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let α := U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy _ C))
    α.range = MulAction.stabilizer (MulAut U) (⟨z,le_conjugateSpanBy _ C hzH⟩ : U) := by
  let C := centralizer ({z} : Set G)
  let N := pCore 2 C
  let q := QuotientGroup.mk' N
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  let hCU : C ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ C
  let α : C →* MulAut U := U.normalizerMonoidHom.comp (inclusion hCU)
  let zU : U := ⟨z,le_conjugateSpanBy _ C hzH⟩
  change α.range = MulAction.stabilizer (MulAut U) zU
  obtain ⟨_,_,_,_,_,_,hZ,hel,ρ,hρ,hfaith,_,_⟩ :=
    binary_three_source_binary_faithful_span
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB (Or.inl rfl) hm
  let := hZ
  let β := ρ.comp q
  have hαker : α.ker = (centralizer (U : Set G)).subgroupOf C := by
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  have hαβ : α.ker ≤ β.ker := by
    intro x hx
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v
    have hfix : α x u = u := congrArg (fun a : MulAut U => a u) (MonoidHom.mem_ker.mp hx)
    change ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U) u) = _
    rw [hρ x u (α x u) rfl,hfix]
    rfl
  have hNβ : N ≤ β.ker := by
    intro x hx
    change ρ (q x) = 1
    have hq : q x = 1 := (QuotientGroup.eq_one_iff (N := N) x).mpr hx
    rw [hq,map_one]
  have hβK : β.ker ⊓ K ≤ N := by
    rintro x ⟨hx,hxK⟩
    let k : K.map q := ⟨q x,mem_map_of_mem q hxK⟩
    have hk : k = 1 := hfaith (show (ρ.comp (K.map q).subtype) k =
      (ρ.comp (K.map q).subtype) 1 from (MonoidHom.mem_ker.mp hx).trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val hk)
  have hNsub : (C.pCoreIn 2).subgroupOf C = N :=
    comap_map_eq_self_of_injective C.subtype_injective N
  have hαN : α.ker.relIndex N = 16 := by
    rw [hαker,←hNsub,relIndex_subgroupOf (C.pCoreIn_le 2)]
    exact (binary_three_source_fixed_span_kernel_index
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  obtain ⟨_,_,_,a,_,_,_⟩ := binary_three_point_four_endpoint_equality
    d c.L b z hLS P hP (K.map q) hBK hm
  have hKcard : Nat.card (K.map q) = 20160 := by
    rw [Nat.card_congr a.toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 4).toEquiv,Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  have hNK : N.relIndex K = 20160 := by
    rw [←QuotientGroup.ker_mk' N,relIndex_ker,hKcard]
  have hbound : 322560 ≤ Nat.card α.range := by
    have hh := image_card_lower_from_section α β N K hαβ hNβ hβK hαN
    rw [hNK] at hh
    exact hh
  have hpoint : α.range ≤ MulAction.stabilizer (MulAut U) zU := by
    rintro _ ⟨x,rfl⟩
    change α x zU = zU
    apply Subtype.ext
    change (x:G)*z*(x:G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp x.property,mul_inv_cancel_right]
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hzU : zU ≠ 1 := by
    intro hh
    have hz1 : z = 1 := congrArg Subtype.val hh
    rw [hz1,orderOf_one] at hz2
    norm_num at hz2
  exact eq_of_le_of_card_ge hpoint
    ((MulAut.card_stabilizer_of_elementary_thirtyTwo hUcard zU hzU).le.trans hbound)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
