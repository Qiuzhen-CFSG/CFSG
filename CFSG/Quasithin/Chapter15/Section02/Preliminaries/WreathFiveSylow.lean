module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveLocals
public import Theory.Quasithin.EvenCharacteristic
/-!
# Sylow promotion in the original marked-five wreath configuration

The marked normal order-five image preserves the residual's module seed under
conjugation inside M.  Consequently the source uniqueness argument for YT also
applies to YQ for every ambient Sylow subgroup Q contained in M.  This avoids
assuming global normality of the literal relative residual Y.

For the actual mixed generated group with nontrivial two-core, an overgroup of
S in a Sylow subgroup has index at most two.  Thompson control puts it in M;
if it were larger than S, the preceding uniqueness would force the entire
local generated group into M, contradicting the chosen wreath component.

Source: Aschbacher--Smith, original 15.2.4, printed p.1106, using 15.2.3(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conjugate_image {D : Type*} [Group D]
    {M X : Subgroup G} (hXM : X ≤ M) (f : M →* D) (m : M) :
    ((X.map (MulAut.conj (m:G)).toMonoidHom).subgroupOf M).map f =
      ((X.subgroupOf M).map f).map (MulAut.conj (f m)).toMonoidHom := by
  ext d
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hx
    let y' : M := ⟨y,hXM hy⟩
    have hxy : x = m*y'*m⁻¹ := Subtype.ext he.symm
    rw [hxy]
    exact ⟨f y',mem_map_of_mem f hy,by simp [MulAut.conj_apply]⟩
  · rintro ⟨d,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨m*x*m⁻¹,?_,by simp [MulAut.conj_apply]⟩
    exact mem_map.mpr ⟨x,hx,rfl⟩

omit [Finite G] in
private theorem orbit_span_le_of_action_image {M V X W Z : Subgroup G}
    (hn : M ≤ normalizer (V : Set G)) (hXM : X ≤ M) (hZV : Z ≤ V)
    (hi : (X.subgroupOf M).map (actionHom M V hn).rangeRestrict ≤
      (W.subgroupOf M).map (actionHom M V hn).rangeRestrict) :
    conjugateSpanBy Z X ≤ conjugateSpanBy Z W := by
  apply (closure_le _).mpr
  rintro _ ⟨x,hx,z,hz,rfl⟩
  obtain ⟨w,hw,he⟩ := hi (mem_map_of_mem (actionHom M V hn).rangeRestrict
    (show (⟨x,hXM hx⟩ : M) ∈ X.subgroupOf M from hx))
  have ha := congrArg (fun a : MulAut V => a ⟨z,hZV hz⟩) (congrArg Subtype.val he)
  have hv : (w:G)*z*(w:G)⁻¹ = x*z*x⁻¹ := congrArg Subtype.val ha
  exact hv ▸ subset_closure ⟨w,hw,z,hz,rfl⟩

/-- The source seed uniqueness works for every ambient Sylow subgroup of M. -/
theorem source_dihedral_five_any_sylow_unique
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2) (Q : Sylow 2 G) (hQM : (Q : Subgroup G) ≤ M) :
    maximalTwoLocalOvergroups
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (Q : Subgroup G)) = {M} := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let f := (actionHom M V hV.normalized).rangeRestrict
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hIm := source_dihedral_caseIIResidual_image hG T hempty hM hJ hu hmany hV l hp hd
  let : (Jhat (imageRepresentation M V hV.normalized)).Normal := Jhat_normal _
  have hnormal := (hd.ambient_marks (Jhat (imageRepresentation M V hV.normalized)) hp).2.2.2.1
  have hspan := source_dihedral_five_residual_seed_span hG T hempty hM hJ hu hmany hV l hp hd
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq M (Q.subtype hQM) (T.subtype hM.1.2)
  rw [Sylow.smul_subtype] at hm
  have hQT := congrArg Sylow.toSubgroup (Sylow.subtype_injective hm)
  change (Q : Subgroup G).map (MulAut.conj (m:G)).toMonoidHom = (T : Subgroup G) at hQT
  let Y' := Y.map (MulAut.conj (m:G)).toMonoidHom
  have hMM : M.map (MulAut.conj (m:G)).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer m.property)
  have hY'M : Y' ≤ M := (map_mono hYM).trans_eq hMM
  have hI : (Y'.subgroupOf M).map f = (Y.subgroupOf M).map f := by
    rw [conjugate_image hYM f m,hIm]
    exact normal_iff_map_conj_eq.mp hnormal (f m)
  have hspan' : V = conjugateSpanBy (centralInvolutions T ⊓ V) Y' :=
    le_antisymm (hspan.le.trans (orbit_span_le_of_action_image hV.normalized hYM
      inf_le_right hI.symm.le)) (conjugateSpanBy_le inf_le_right (hY'M.trans hV.normalized))
  have hu' : maximalTwoLocalOvergroups (Y' ⊔ (T : Subgroup G)) = {M} := by
    apply source_unique_overgroup_of_seed_span hG T hempty hM hJ le_sup_right
      (sup_le hY'M hM.1.2) hV.nontrivial hV.normalized
    exact le_antisymm (hspan'.le.trans (conjugateSpanBy_mono le_rfl le_sup_left))
      (conjugateSpanBy_le inf_le_right ((sup_le hY'M hM.1.2).trans hV.normalized))
  ext N
  constructor
  · intro hN
    have hNc : N.map (MulAut.conj (m:G)).toMonoidHom ∈
        maximalTwoLocalOvergroups (Y' ⊔ (T : Subgroup G)) := by
      refine ⟨Theory.Quasithin.isMaximalTwoLocal_map (MulAut.conj (m:G)) hN.1,?_⟩
      have hh := map_mono (f := (MulAut.conj (m:G)).toMonoidHom) hN.2
      rwa [Subgroup.map_sup,hQT] at hh
    have he : N.map (MulAut.conj (m:G)).toMonoidHom = M := Set.mem_singleton_iff.mp (hu' ▸ hNc)
    exact Set.mem_singleton_iff.mpr (map_injective (MulAut.conj (m:G)).injective (he.trans hMM.symm))
  · rintro rfl
    exact ⟨hM.1.1,sup_le hYM hQM⟩

private theorem sylow_of_index_two_control (T : Sylow 2 G) {S Y M W : Subgroup G}
    (hST : S ≤ (T : Subgroup G)) (hi : S.relIndex (T : Subgroup G) = 2)
    (hSW : S ≤ W) (hYW : Y ≤ W) (hNS : normalizer (S : Set G) ≤ M)
    (hout : ¬ W ≤ M) (hcore : pCore 2 W ≠ ⊥)
    (huniq : ∀ Q : Sylow 2 G, (Q : Subgroup G) ≤ M →
      maximalTwoLocalOvergroups (Y ⊔ (Q : Subgroup G)) = {M}) :
    Chapter1.IsSylowIn 2 S W := by
  refine Chapter1.isSylowIn_iff.mpr ⟨T.isPGroup'.to_le hST,hSW,?_⟩
  intro U hU hSU hUW
  obtain ⟨Q,hUQ⟩ := hU.exists_le_sylow
  have hSQ : S ≤ (Q : Subgroup G) := hSU.trans hUQ
  have hcQ : Nat.card S * S.relIndex (Q : Subgroup G) = Nat.card (Q : Subgroup G) := by
    simpa only [relIndex_bot_left] using relIndex_mul_relIndex (⊥ : Subgroup G) S Q bot_le hSQ
  have hcT : Nat.card S * 2 = Nat.card (T : Subgroup G) := by
    simpa only [relIndex_bot_left,hi] using relIndex_mul_relIndex (⊥ : Subgroup G) S T bot_le hST
  have hidx : S.relIndex (Q : Subgroup G) = 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S))
    exact hcQ.trans ((Q.card_eq_multiplicity.trans T.card_eq_multiplicity.symm).trans hcT.symm)
  have hprod : S.relIndex U * U.relIndex (Q : Subgroup G) = 2 :=
    (relIndex_mul_relIndex S U Q hSU hUQ).trans hidx
  rcases Nat.prime_mul_iff.mp (hprod ▸ Nat.prime_two) with ⟨_,hUQi⟩ | ⟨_,hSUi⟩
  · have hUeq : U = (Q : Subgroup G) := le_antisymm hUQ (relIndex_eq_one.mp hUQi)
    have hSUi : S.relIndex U = 2 := by rwa [hUQi,mul_one] at hprod
    have hUN : U ≤ normalizer (S : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hSU).mp (normal_of_index_eq_two hSUi)
    have hQM : (Q : Subgroup G) ≤ M := hUeq ▸ hUN.trans hNS
    obtain ⟨N,hN,hWN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot W hcore
    have hNmem : N ∈ maximalTwoLocalOvergroups (Y ⊔ (Q : Subgroup G)) :=
      ⟨hN,sup_le (hYW.trans hWN) ((hUeq ▸ hUW).trans hWN)⟩
    have hNM : N = M := Set.mem_singleton_iff.mp (huniq Q hQM ▸ hNmem)
    exact (hout (hWN.trans_eq hNM)).elim
  · exact le_antisymm (relIndex_eq_one.mp hSUi) hSU

theorem source_dihedral_five_nontrivial_core_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V K : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2) (hout : ¬ K ≤ M)
    (hi : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2)
    (hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (K : Set G))
    (hcore : pCore 2 (ChapterF.Source.generated
      ![caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (M ⊓ Mc).pCoreIn 2,K] ((T : Subgroup G) ⊓ normalizer (K : Set G))) ≠ ⊥) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (K : Set G))
      (ChapterF.Source.generated
        ![caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
          (M ⊓ Mc).pCoreIn 2,K] ((T : Subgroup G) ⊓ normalizer (K : Set G))) := by
  have hNS : normalizer ((T : Subgroup G) ⊓ normalizer (K : Set G) : Set G) ≤ M := by
    have hn := normalizer_le_normalizer_elementaryAbelianMaxJ
      ((T : Subgroup G) ⊓ normalizer (K : Set G))
    rw [elementaryAbelianMaxJ_eq_of_intermediate_finite _ _ hJS inf_le_left] at hn
    exact hn.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  apply sylow_of_index_two_control T inf_le_left hi le_sup_right
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) hNS ?_ hcore
  · intro Q hQM
    exact source_dihedral_five_any_sylow_unique hG T hempty hM hJ hu hmany hV l hd Q hQM
  · intro hWM
    exact hout ((le_sup_right.trans le_sup_left).trans hWM)

end CFSG.Quasithin.Chapter15.Section02
