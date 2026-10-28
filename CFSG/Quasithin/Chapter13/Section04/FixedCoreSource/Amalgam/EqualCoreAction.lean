module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ActionKernel
public import Theory.GroupAction.InvolutionDisplacementCard
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.SolvableOuterQuotient
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SmallSolvableAction

/-!
# Equal parabolic cores in the solvable omega action

Equal embedded vertex two-cores are the ambient two-core. Thus the
common Sylow action on a reduced normal module containing its omega
center has order two. Its fixed subgroup is exactly that center;
when this has order four, the whole module has order at most sixteen.

Pass to the full conjugation image, preserving both local action kernels.
If the two vertex images coincide, their cubic residuals commute. Otherwise
they form a genuine Goldschmidt triple and SmallSolvableAction applies.
Lifting proves that the original residual commutator centralizes the whole
module. No assertion that the full action kernel is a two-group is used.
EqualCoreSource applies this to the original admitted pairs of 13.4.7.

Source: Aschbacher--Smith 13.4.7, printed p.901, the equal-core reduction
in the solvable-action case; F.6.3 and F.6.8, printed pp.304--305.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem equal_cores_ambient {A B : Subgroup G}
    (hg : ChapterF.IsGoldschmidtTriple A B) (he : A.pCoreIn 2 = B.pCoreIn 2) :
    A.pCoreIn 2 = pCore 2 G := by
  apply le_antisymm
  · apply hg.twoCore_isGreatest.2
    refine ⟨hg.local_twoCore_le_intersection,?_,?_⟩
    · exact (normal_subgroupOf_iff_le_normalizer (A.pCoreIn_le 2)).mpr
        hg.left_core_normalized
    · rw [he]
      exact (normal_subgroupOf_iff_le_normalizer (B.pCoreIn_le 2)).mpr
        hg.symm.left_core_normalized
  · exact le_pCoreIn_of_normalizes pCore_isPGroup
      (hg.twoCore_isGreatest.1.1.trans inf_le_left) le_normalizer_of_normal

private theorem card_le_fixed_sq {E : Type u} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (S : Subgroup (MulAut E)) (hS : Nat.card S = 2) :
    Nat.card E ≤ Nat.card (FixedPoints.subgroup S E)^2 := by
  let : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨s,hs⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic S)
  have hs' : zpowers (s : MulAut E) = S := by
    apply le_antisymm (zpowers_le.mpr s.property)
    intro a ha
    obtain ⟨n,hn⟩ := (show (⟨a,ha⟩ : S) ∈ zpowers s from hs ▸ mem_top _)
    exact ⟨n,congrArg Subtype.val hn⟩
  have hs2 : (s : MulAut E)^2 = 1 := by
    have hh := pow_card_eq_one' (x := s)
    rw [hS] at hh
    exact congrArg Subtype.val hh
  obtain ⟨hc,hd⟩ := MulAut.involution_fixed_displacement_card_data (s : MulAut E) hs2
  rw [←hs',pow_two,hc]
  exact Nat.mul_le_mul_left _ (card_le_of_le hd)

/-- Equality of the actual vertex cores bounds the full omega span by sixteen. -/
theorem equal_core_seed_card {A B W : Subgroup G}
    (hg : ChapterF.IsGoldschmidtTriple A B) (hW : IsPReduced 2 W)
    (hseed : omegaOneCenterAmbient (A ⊓ B) ≤ W)
    (hZ : Nat.card (omegaOneCenterAmbient (A ⊓ B)) = 4)
    (hker : (A ⊓ B) ⊓ centralizer (W : Set G) = pCore 2 G)
    (he : A.pCoreIn 2 = B.pCoreIn 2) : Nat.card W ≤ 16 := by
  let := hW.normal
  let := hW.elementary
  let f : G →* MulAut W := MulAut.conjNormal
  let S := A ⊓ B
  let I := S.map f
  have hfixed : (FixedPoints.subgroup I W).map W.subtype = omegaOneCenterAmbient S := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      apply (mem_omegaOneCenterAmbient_iff _ _).mpr
      refine ⟨hg.twoCore_isGreatest.1.1 (hW.le_pCore w.property),?_,?_⟩
      · exact elemPow_eq_one_of_isElementaryAbelian w.val w.property
      · intro t ht
        have hh := hw ⟨f t,mem_map_of_mem f ht⟩
        have hv : t*w.val*t⁻¹=w.val := congrArg Subtype.val hh
        exact mul_inv_eq_iff_eq_mul.mp hv
    · intro x hx
      refine ⟨⟨x,hseed hx⟩,?_,rfl⟩
      rintro ⟨a,ha⟩
      obtain ⟨t,ht,rfl⟩ := ha
      apply Subtype.ext
      change t*x*t⁻¹=x
      exact mul_inv_eq_iff_eq_mul.mpr
        (((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2 t ht)
  have hfixedCard : Nat.card (FixedPoints.subgroup I W) = 4 := by
    rw [←card_map_of_injective W.subtype_injective,hfixed]
    exact hZ
  have hI : Nat.card I = 2 := by
    let a := f.comp S.subtype
    have hr : a.range = I := by rw [MonoidHom.range_comp,range_subtype]
    have hk : a.ker = (pCore 2 G).subgroupOf S := by
      ext s
      change f s.val = 1 ↔ s.val ∈ pCore 2 G
      rw [←MonoidHom.mem_ker,MulAut.conjNormal_ker_eq_centralizer]
      exact ⟨fun hs => hker.le ⟨s.property,hs⟩,fun hs => (hker.symm.le hs).2⟩
    rw [←hr,←index_ker,hk,←equal_cores_ambient hg he]
    exact hg.left_core_index
  have hb := card_le_fixed_sq I hI
  rw [hfixedCard] at hb
  exact hb

/-- The equal-core branch in the original action, retaining its full kernel. -/
theorem equal_core_solvable_seed_commutes {K : GroupClass.{u}}
    (hG : IsSQTK K G) {A B W : Subgroup G}
    (hg : ChapterF.IsGoldschmidtTriple A B) (hW : IsPReduced 2 W)
    (hseed : omegaOneCenterAmbient (A ⊓ B) ≤ W)
    (hZ : Nat.card (omegaOneCenterAmbient (A ⊓ B)) = 4)
    (hkerA : A ⊓ centralizer (W : Set G) = pCore 2 G)
    (hkerB : B ⊓ centralizer (W : Set G) = pCore 2 G)
    (hkerT : (A ⊓ B) ⊓ centralizer (W : Set G) = pCore 2 G)
    (he : A.pCoreIn 2 = B.pCoreIn 2) (hs : Group.IsSolvable G) :
    ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (W : Set G) := by
  let := hW.normal
  let := hW.elementary
  let f : G →* MulAut W := MulAut.conjNormal
  let Q := f.range
  let q : G →* Q := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hk : q.ker = centralizer (W : Set G) := by
    rw [MonoidHom.ker_rangeRestrict,MulAut.conjNormal_ker_eq_centralizer]
  let e : (G ⧸ centralizer (W : Set G)) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq (MulAut.conjNormal_ker_eq_centralizer W).symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hcore : pCore 2 Q = ⊥ := by
    rw [←pCore_map_iso 2 e,hW.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hlocal (C : Subgroup G) (hC : C.pCoreIn 2 = pCore 2 G)
      (hkerC : C ⊓ centralizer (W : Set G) = pCore 2 G)
      (eC : (C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) :
      Nonempty (C.map q ≃* Equiv.Perm (Fin 3)) := by
    have hkc : (q.subgroupMap C).ker = pCore 2 C := by
      apply map_injective C.subtype_injective
      rw [ker_subgroupMap,subgroupOf_map_subtype,hk,inf_comm,hkerC,←hC]
      rfl
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap C)
      (q.subgroupMap_surjective C)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkc).trans eC)⟩
  let eA := (hlocal A (equal_cores_ambient hg he) hkerA hg.quotient_left.some).some
  let eB := (hlocal B (he.symm.trans (equal_cores_ambient hg he)) hkerB
    hg.quotient_right.some).some
  have hc : ⁅(pResidual 2 (A.map q)).map (A.map q).subtype,
      (pResidual 2 (B.map q)).map (B.map q).subtype⁆ = ⊥ := by
    by_cases hab : A.map q = B.map q
    · rw [←hab]
      have hcard : Nat.card ((pResidual 2 (A.map q)).map (A.map q).subtype) = 3 := by
        rw [card_map_of_injective (A.map q).subtype_injective]
        exact (ChapterF.residual_of_symmetricThree eA).2
      let : IsCyclic ((pResidual 2 (A.map q)).map (A.map q).subtype) :=
        isCyclic_of_prime_card hcard
      exact commutator_self_eq_bot_iff.mpr inferInstance
    · obtain ⟨T,hT⟩ := hg.intersection_sylow
      let S := T.mapSurjective hq
      have hSA : (S : Subgroup Q) ≤ A.map q := map_mono (hT.symm.le.trans inf_le_left)
      have hSB : (S : Subgroup Q) ≤ B.map q := map_mono (hT.symm.le.trans inf_le_right)
      have model {C : Subgroup Q} (eC : C ≃* Equiv.Perm (Fin 3)) :
          Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) := by
        have hC : pCore 2 C = ⊥ := by
          have hh := ker_eq_twoCore_of_surjective_perm_three eC.toMonoidHom eC.surjective
            (by rw [(MonoidHom.ker_eq_bot_iff _).mpr eC.injective]
                exact IsPGroup.of_subsingleton 2 _)
          rw [(MonoidHom.ker_eq_bot_iff _).mpr eC.injective] at hh
          exact hh.symm
        exact ⟨((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot).trans eC⟩
      have hgi : ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) :=
        ⟨by rw [←Subgroup.map_sup,hg.generated,map_top_of_surjective q hq],model eA,model eB,
          S,intersection_eq_sylow hSA hSB (model eA).some (model eB).some hab⟩
      let : Group.IsSolvable G := hs
      exact small_solvable_action_residuals_commute hG q hq hgi eA
        (Group.isSolvable_of_surjective hq) hcore Q.subtype Q.subtype_injective
        (equal_core_seed_card hg hW hseed hZ hkerT he)
  rw [←map_embedded_pResidual,←map_embedded_pResidual,←map_commutator] at hc
  exact hk ▸ (Subgroup.map_eq_bot_iff _).mp hc

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
