module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.SourceLine
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MovingBlock
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.PCoreImage

/-!
# The literal covered-six quotient comparison

The map from the selected component to its plus image is the composite of
the genuine star image map and the restricted star-to-plus map.  Under the
earlier invariance and the source moving-block conclusion its kernel is the
literal two-core of `K`.  The quotient lift therefore embeds `K/O₂(K)` in
the actual plus quotient, with the representative formula used by the
marked-plane assembly.

Source: Aschbacher--Smith, combined manuscript, 13.6.14 and 13.6.22,
printed pp.929 and 932.
-/

@[expose] public section
open Subgroup CFSG.Quasithin.ChapterC
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MovingBlock

variable {G : Type*} [Group G] [Finite G]

section Comparison

variable (K L T : Subgroup G) (z v : G)
    (h : IsExceptionalAhat6Block K)
    [IsElementaryAbelian 2 (blockU K)]
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v)))

/-- The actual map from `K` to the actual plus image of `K`. -/
noncomputable def coveredSixToPlus :
    K →* plusImage K L T z v hL hz K :=
  (componentStarToPlus K L T z v hK.1.1 hL hz).comp
    (starImageMap z v K hK.1.1)

omit [Finite G] [IsElementaryAbelian 2 (blockU K)] in
theorem coveredSixToPlus_surjective :
    Function.Surjective (coveredSixToPlus K L T z v hK hL hz) :=
  (componentStarToPlus_surjective K L T z v hK.1.1 hL hz).comp
    (starImageMap_surjective z v K hK.1.1)

omit [Finite G] [IsElementaryAbelian 2 (blockU K)] in
theorem coveredSixToPlus_mk (k : K) :
    (coveredSixToPlus K L T z v hK hL hz k :
      Gplus K L T z v hL hz) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k) := by
  exact componentStarToPlus_mk K L T z v hK.1.1 hL hz k

omit [Finite G] [IsElementaryAbelian 2 (blockU K)] in
theorem coveredSixToPlus_ker :
    (coveredSixToPlus K L T z v hK hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  ext x
  change componentStarToPlus K L T z v hK.1.1 hL hz
      (starImageMap z v K hK.1.1 x) = 1 ↔ _
  rw [Subtype.ext_iff, componentStarToPlus_mk]
  change inclusion (K_le_plusActor K L T v) x ∈
      (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

omit [Finite G] [IsElementaryAbelian 2 (blockU K)] in
private theorem core_le_tv
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    (pCore 2 K).map K.subtype ≤ Tv T v := by
  have hcore : (pCore 2 K).map K.subtype ≤
      (K ⊔ Tv T v).pCoreIn 2 := by
    simpa only [pCoreIn] using
      (pCoreIn_mono_of_normalizes (p := 2) (Y := K) (L := K ⊔ Tv T v)
        le_sup_left (sup_le K.le_normalizer hn))
  let H := K ⊔ Tv T v
  obtain ⟨S, hS⟩ := hK.1.2.2.1
  have hHT : H.pCoreIn 2 ≤ Tv T v :=
    hS ▸ pCoreIn_le_sylow H S
  exact hcore.trans hHT

omit [Finite G] [IsElementaryAbelian 2 (blockU K)] in
private theorem core_centralizes_WK
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (_hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (pCore 2 K).map K.subtype ≤ centralizer (WK K L T z v : Set G) := by
  rw [WK, Kminus_eq_of_invariant K T v hn]
  apply le_centralizer_conjugateSpanBy_of_normalizes
    ((pCore 2 K).map K.subtype) (zpowers z) (K ⊔ Lv L v)
  · have hKcore : K ≤ normalizer ((pCore 2 K).map K.subtype : Set G) := by
      have hm := (pCore 2 K).le_normalizer_map K.subtype
      rw [normalizer_eq_top (pCore 2 K)] at hm
      intro x hx
      apply hm
      exact mem_map.mpr ⟨⟨x, hx⟩, (by trivial), rfl⟩
    have hLcore : Lv L v ≤ normalizer ((pCore 2 K).map K.subtype : Set G) :=
      hLK.trans hKcore
    exact sup_le hKcore hLcore
  · intro x hx
    rw [zpowers_eq_closure, centralizer_closure]
    exact hz (core_le_tv K L T z v hK hn hx)

omit [IsElementaryAbelian 2 (blockU K)] in
private theorem centralizer_le_core
    (h : IsExceptionalAhat6Block K) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v))) :
    (centralizer (WK K L T z v : Set G)).subgroupOf K ≤ pCore 2 K := by
  let C : Subgroup G := centralizer (WK K L T z v : Set G) ⊓ K
  have hKW : K ≤ normalizer (WK K L T z v : Set G) :=
    (K_le_plusActor K L T v).trans
      (plusActor_normalizes_WK K L T z v hL hz)
  have hKC : K ≤ normalizer (C : Set G) := by
    exact (le_inf (hKW.trans (normalizer_le_normalizer_centralizer _))
      K.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hCW : ⁅C, WK K L T z v⁆ = (⊥ : Subgroup G) :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (show C ≤ centralizer (WK K L T z v : Set G) from inf_le_left)
  have hrot₁ : ⁅⁅K, C⁆, WK K L T z v⁆ ≤ (⊥ : Subgroup G) := by
    exact (commutator_mono
      (le_normalizer_iff_commutator_le_right.mp hKC) le_rfl).trans_eq hCW
  have hrot₂ : ⁅⁅C, WK K L T z v⁆, K⁆ ≤ (⊥ : Subgroup G) := by
    exact (commutator_mono hCW.le le_rfl).trans_eq (commutator_bot_left K)
  have hthree : ⁅⁅WK K L T z v, K⁆, C⁆ ≤ (⊥ : Subgroup G) :=
    commutator_commutator_le_of_rotate hrot₁ hrot₂
  have hblock : C ≤ centralizer ((blockU K).map K.subtype : Set G) := by
    rw [source_moving_eq_blockU K L T z v hL hz hK hn hW hb] at hthree
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [commutator_comm]
    exact bot_unique hthree
  intro x hx
  have hxC : (x : G) ∈ C := ⟨hx, x.property⟩
  have hxK : x ∈ centralizer (blockU K : Set K) := by
    intro u hu
    apply Subtype.ext
    exact hblock hxC (u : G) (mem_map.mpr ⟨u, hu, rfl⟩)
  have hxcore : x ∈ pCore 2 K := by
    rw [← h.centralizer]
    exact hxK
  exact hxcore

include h hn hLK hW hb
omit [IsElementaryAbelian 2 (blockU K)] in
theorem restricted_kernel_eq_twoCore :
    (coveredSixToPlus K L T z v hK hL hz).ker = pCore 2 K := by
  rw [coveredSixToPlus_ker K L T z v hK hL hz]
  apply le_antisymm (centralizer_le_core K L T z v h hK hn hL hz hW hb)
  intro x hx
  exact core_centralizes_WK K L T z v hK hn hLK hL hz
    (mem_map.mpr ⟨x, hx, rfl⟩)

omit [IsElementaryAbelian 2 (blockU K)] in
include hK in
/-- The literal plus kernel is a 2-group.  Its intersection with `K` is the
two-core computed above, while the quotient of the plus actor by `K` is a
2-group supplied by the original Sylow witness in `Yz`. -/
theorem plus_kernel_isPGroup :
    IsPGroup 2 (plusMk K L T z v hL hz).ker := by
  rw [plusMk_ker]
  let H := plusActor K L T v
  let C : Subgroup H := (centralizer (WK K L T z v : Set G)).subgroupOf H
  change IsPGroup 2 C
  have hactor : plusActor K L T v = K ⊔ Tv T v := by
    unfold plusActor
    rw [Kminus_eq_of_invariant K T v hn, sup_of_le_left hLK]
  have hKH : K ≤ H := K_le_plusActor K L T v
  let KH := K.subgroupOf H
  let : KH.Normal := normal_subgroupOf_of_le_normalizer (by
    change plusActor K L T v ≤ normalizer (K : Set G)
    rw [hactor]
    exact sup_le K.le_normalizer hn)
  have hsup : KH ⊔ (Tv T v).subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hKH (show Tv T v ≤ H from le_sup_right), ← hactor]
    exact subgroupOf_self _
  have hTv : IsPGroup 2 ((Tv T v).subgroupOf H) :=
    (Chapter1.isSylowIn_iff.mp hK.1.2.2.1).1.comap_subtype
  have hq : IsPGroup 2 (H ⧸ KH) :=
    isPGroup_quotient_of_sup_eq_top KH _ hTv hsup
  let q : C →* H ⧸ KH := (QuotientGroup.mk' KH).comp C.subtype
  have hqker : IsPGroup 2 q.ker := by
    have hcore : (centralizer (WK K L T z v : Set G)).subgroupOf K ≤ pCore 2 K :=
      centralizer_le_core K L T z v h hK hn hL hz hW hb
    let j : q.ker →* pCore 2 K :=
      { toFun := fun x =>
          have hxq : q x.val = 1 := MonoidHom.mem_ker.mp x.property
          have hxq' : QuotientGroup.mk' KH (x.val : H) = 1 := by
            simpa [q] using hxq
          have hxKH : (x.val : H) ∈ KH :=
            (QuotientGroup.eq_one_iff (x.val : H)).mp hxq'
          let k : K := ⟨(x.val : G), hxKH⟩
          ⟨k, hcore x.val.property⟩
        map_one' := by rfl
        map_mul' := by intro x y; rfl }
    have hj : Function.Injective j := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      simpa [j] using congrArg (fun z : pCore 2 K => (z : G)) he
    exact pCore_isPGroup.of_injective j hj
  have hh := (hq.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at hh
  exact hh.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C)

/-! The quotient map is kept separate from the literal action map so that the
range remains the actual plus image of `K`. -/

noncomputable def coreToPlus :
    (K ⧸ pCore 2 K) →* plusImage K L T z v hL hz K :=
  QuotientGroup.lift _ (coveredSixToPlus K L T z v hK hL hz)
    (by rw [restricted_kernel_eq_twoCore K L T z v h hK hn hLK hL hz hW hb])

omit [IsElementaryAbelian 2 (blockU K)] in
theorem coreToPlus_surjective :
    Function.Surjective (coreToPlus K L T z v h hK hn hLK hL hz hW hb) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (coveredSixToPlus_surjective K L T z v hK hL hz) _

omit [IsElementaryAbelian 2 (blockU K)] in
theorem coreToPlus_mk (k : K) :
    coreToPlus K L T z v h hK hn hLK hL hz hW hb
      (QuotientGroup.mk' (pCore 2 K) k) =
      coveredSixToPlus K L T z v hK hL hz k := rfl

noncomputable def coreToGplus :
    (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz :=
  (plusImage K L T z v hL hz K).subtype.comp
    (coreToPlus K L T z v h hK hn hLK hL hz hW hb)

omit [IsElementaryAbelian 2 (blockU K)] in
theorem coreToGplus_mk (k : K) :
    coreToGplus K L T z v h hK hn hLK hL hz hW hb
      (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k) := by
  exact coveredSixToPlus_mk K L T z v hK hL hz k

omit [IsElementaryAbelian 2 (blockU K)] in
theorem coreToGplus_injective :
    Function.Injective (coreToGplus K L T z v h hK hn hLK hL hz hW hb) := by
  intro a b hab
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) b
  rw [coreToGplus_mk K L T z v h hK hn hLK hL hz hW hb k,
    coreToGplus_mk K L T z v h hK hn hLK hL hz hW hb l] at hab
  apply (QuotientGroup.eq_iff_div_mem).2
  rw [← restricted_kernel_eq_twoCore K L T z v h hK hn hLK hL hz hW hb]
  change coveredSixToPlus K L T z v hK hL hz (k / l) = 1
  rw [map_div]
  apply Subtype.ext
  change ((↑((coveredSixToPlus K L T z v hK hL hz) k) :
      Gplus K L T z v hL hz) /
      ↑((coveredSixToPlus K L T z v hK hL hz) l)) = 1
  rw [div_eq_mul_inv, coveredSixToPlus_mk K L T z v hK hL hz k,
    coveredSixToPlus_mk K L T z v hK hL hz l, hab, mul_inv_cancel]

end Comparison

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
