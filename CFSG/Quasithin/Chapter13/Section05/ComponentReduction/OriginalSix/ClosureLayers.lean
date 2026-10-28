module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosurePair
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperAction

/-!
# The literal second layer of the original A₆ pair

The actual A₅ quotient and its Sylow image generate the two-core from
its intersections with U_H and its conjugate. The layer
V(U_H∩U_Hᵍ) is normal and elementary: its commutator lies in V, and
the two distinct Frattini lines make the intersection elementary.
These conclusions use the original F.9 and pair maps directly.
Source: Aschbacher–Smith13.5.14(4),13.5.22 and13.5.25, pp.919,924–925.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosureLayers
open Section08.SourceCompletion NormalBranch
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks SourceFiveModule SourceUpperStructure
open ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

theorem closure_image_card (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    Nat.card ((D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)) = 4 := by
  let U := D.UH.subgroupOf (NormalBranch.K D g.val)
  let f := restrictedActor d hK a hi
  let q := (localMap d).comp (inclusion hK)
  have he : f.ker=q.ker := restrictedActor_ker d hK a hi
  rw [←relIndex_ker,he,relIndex_ker]
  have hmap : U.map (inclusion hK) = D.UH.subgroupOf D.L := by
    apply map_injective D.L.subtype_injective
    rw [map_map]
    change U.map (NormalBranch.K D g.val).subtype = _
    rw [map_subgroupOf_eq_of_le (show D.UH≤NormalBranch.K D g.val from le_sup_left),
      map_subgroupOf_eq_of_le (ClosurePair.closure_reduction_of_tilde d h htilde).2.2]
  change Nat.card (U.map q)=4
  rw [show U.map q = (D.UH.subgroupOf D.L).map (localMap d) by change U.map ((localMap d).comp (inclusion hK)) = _; rw [←map_map,hmap]]
  obtain ⟨b,hb,_⟩ := QuadraticSource.source_even_flag d
  rw [ClosurePair.closure_image_eq_point_core_of_tilde d h e htilde hU b hb,
    card_map_of_injective (MulAut.conj b.val).injective,pointCoreEven_card]

theorem core_generated (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hg : g.val ∈ NormalBranch.K D g.val) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    (NormalBranch.K D g.val).pCoreIn 2 =
      (D.UH ⊓ (NormalBranch.K D g.val).pCoreIn 2) ⊔
      ChapterG.Section02.Setup.conjugate (D.UH ⊓ (NormalBranch.K D g.val).pCoreIn 2) g.val := by
  let J := NormalBranch.K D g.val
  let U := D.UH.subgroupOf J
  let f := restrictedActor d hK a hi
  let k : J := ⟨g.val,hg⟩
  have hk : f.ker=pCore 2 J := restrictedActor_ker_eq_twoCore d hK a hi e
  have hUp : IsPGroup 2 U := (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup).comap_subtype
  have hcard : Nat.card (U.map f)=4 := closure_image_card d h e htilde hU g hK a hi
  have hidx : (U.map f).index=15 := by
    have hh := (U.map f).card_mul_index
    rw [hcard,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  let P : Sylow 2 (alternatingGroup (Fin 5)) :=
    (hUp.map f).toSylow (by rw [hidx];decide)
  have hnorm : f.ker ≤ normalizer (U : Set J) := by
    intro x hx
    have hxL : inclusion hK x ∈ (localMap d).ker := (restrictedActor_ker d hK a hi).le hx
    rw [SourceBarred.local_kernel_eq_core d e] at hxL
    have hxH : x.val ∈ D.H := h.T_le_H
      (h.sylow_centralizer.symm.le (SourcePairResidual.local_core_le_LT_core h
        (mem_map_of_mem D.L.subtype hxL))).1
    apply mem_normalizer_iff.mpr
    intro u
    exact mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H hxH) u.val
  have hconj : (U.map (MulAut.conj k⁻¹).toMonoidHom).map J.subtype =
      ChapterG.Section02.Setup.conjugate D.UH g.val := by
    rw [map_map]
    change U.map (((MulAut.conj g.val⁻¹).toMonoidHom).comp J.subtype) = _
    rw [←map_map,map_subgroupOf_eq_of_le (show D.UH≤J from le_sup_left)]
    rfl
  have hgen : U ⊔ U.map (MulAut.conj k⁻¹).toMonoidHom = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,hconj,map_subgroupOf_eq_of_le (show D.UH≤J from le_sup_left),
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hh := kernel_eq_intersection_pair_of_twoPerfect hp f (hk ▸ pCore_isPGroup)
    U hUp k⁻¹ hgen hnorm P rfl
  simp only [hk] at hh
  have hm := congrArg (Subgroup.map J.subtype) hh
  rw [Subgroup.map_sup,map_inf _ _ _ J.subtype_injective,
    map_subgroupOf_eq_of_le (show D.UH≤J from le_sup_left)] at hm
  have hmap : ((U⊓pCore 2 J).map (MulAut.conj k⁻¹).toMonoidHom).map J.subtype =
      ChapterG.Section02.Setup.conjugate (D.UH⊓J.pCoreIn 2) g.val := by
    rw [map_map]
    change (U⊓pCore 2 J).map (((MulAut.conj g.val⁻¹).toMonoidHom).comp J.subtype) = _
    rw [←map_map,map_inf _ _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le (show D.UH≤J from le_sup_left)]
    rfl
  exact hm.trans (congrArg (fun B : Subgroup G => (D.UH ⊓ J.pCoreIn 2) ⊔ B) hmap)

/-- The unchanged denominator from the printed13.5.22 and13.5.25. -/
@[expose] def second (D : ChapterF.Section09.Setup G) (g : G) : Subgroup G :=
  D.V ⊔ (D.UH ⊓ conjugate D.UH g)

omit d [Finite G] in
theorem second_def (g : G) : second D g = D.V ⊔ (D.UH ⊓ conjugate D.UH g) := rfl

theorem second_commutator (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) :
    ⁅second D g.val,NormalBranch.K D g.val⁆ ≤ D.V := by
  have hn : NormalBranch.K D g.val ≤ normalizer (D.V:Set G) :=
    hK.trans (le_sup_left.trans d.normalizes_V)
  have hV : D.V ≤ commutatorPreimage (normalizer (D.V:Set G)) (NormalBranch.K D g.val) D.V :=
    le_commutatorPreimage D.V.le_normalizer (le_normalizer_iff_commutator_le_left.mp hn)
  have hE : D.UH⊓conjugate D.UH g.val ≤ commutatorPreimage (normalizer (D.V:Set G)) (NormalBranch.K D g.val) D.V :=
    le_commutatorPreimage ((inf_le_left.trans le_sup_left).trans hn)
      (SourceSecondLayer.intersection_commutator_le_module d h g hK)
  exact (commutator_mono (sup_le hV hE) le_rfl).trans
    (commutator_commutatorPreimage_le (normalizer (D.V:Set G)) (NormalBranch.K D g.val) D.V le_rfl)

theorem second_normalized (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) :
    NormalBranch.K D g.val ≤ normalizer (second D g.val:Set G) :=
  le_normalizer_iff_commutator_le_left.mpr ((second_commutator d h g hK).trans le_sup_left)

omit d in
theorem intersection_elementary (h : D.Hypothesis) (g : D.L) (hgn : g.val∉D.Gz) :
    IsElementaryAbelian 2 (D.UH⊓conjugate D.UH g.val : Subgroup G) := by
  have hd : Disjoint D.V₁ (conjugate D.V₁ g.val) := by
    apply disjoint_iff.mpr
    apply inf_eq_bot_of_card_two_of_ne _ _ h.point_card
    · exact (card_map_of_injective (MulAut.conj g.val⁻¹).injective).trans h.point_card
    · intro he
      apply hgn
      rw [←h.normalizer_point_eq] at *
      have hi : g.val⁻¹∈normalizer (D.V₁:Set G) := mem_normalizer_iff_map_conj_eq.mpr he.symm
      simpa only [inv_inv] using (normalizer (D.V₁:Set G)).inv_mem hi
  exact conjugate_intersection_elementary h.g2_hypothesis.U_isPGroup
    h.frattini_UH_le_point g.val⁻¹ hd

theorem second_le_core (h : D.Hypothesis) (g : D.L) (hgn : g.val∉D.Gz)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    second D g.val ≤ (NormalBranch.K D g.val).pCoreIn 2 := by
  have hVK := (module_le_core d h (seed_identity d h) g hK hL a hi).trans (pCoreIn_le 2 _)
  have hEK : D.UH⊓conjugate D.UH g.val≤NormalBranch.K D g.val := inf_le_left.trans le_sup_left
  let := h.elementary
  let := intersection_elementary h g hgn
  have hp : IsPGroup 2 (second D g.val) :=
    IsPGroup.to_sup_of_normal_left' (IsElementaryAbelian.isPGroup 2 D.V)
      (IsElementaryAbelian.isPGroup 2 (D.UH⊓conjugate D.UH g.val : Subgroup G))
      (hEK.trans (hK.trans (le_sup_left.trans d.normalizes_V)))
  exact le_pCoreIn_of_normalizes hp (sup_le hVK hEK) (second_normalized d h g hK)

theorem second_elementary (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hgn : g.val∉D.Gz)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    IsElementaryAbelian 2 (second D g.val) := by
  let := h.elementary
  let := intersection_elementary h g hgn
  have hES : D.UH⊓conjugate D.UH g.val≤(NormalBranch.K D g.val).pCoreIn 2 :=
    le_sup_right.trans (second_le_core d h g hgn hK hL a hi)
  exact IsElementaryAbelian.sup_of_le_centralizer
    (hES.trans (core_centralizes_module d h e g hK a hi))

theorem second_normal_in_core (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) :
    ((second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 (NormalBranch.K D g.val)).trans (second_normalized d h g hK))

/-- The exact layer obstruction needed for the G₂ terminal fixed-point argument. -/
theorem order_four_not_mem_second (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hgn : g.val∉D.Gz)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (j : G) (hj : orderOf j=4) : j∉second D g.val := by
  let := second_elementary d h e g hgn hK hL a hi
  intro hm
  have hd := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p:=2) j hm)
  rw [hj] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosureLayers
