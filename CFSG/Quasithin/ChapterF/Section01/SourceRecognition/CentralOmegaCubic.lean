module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.CubicLocalSize
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Complete
public import Theory.GroupTheory.CharacteristicTwoOmegaDetection

/-!
# Cubic recognition with a centralized Sylow omega-center

A characteristic-two vertex that centralizes the omega-center of the common
Sylow subgroup cannot have an A₄ residual: every nontrivial normal subgroup
meets that omega-center, whereas A₄ has trivial center. The opposite A₄
residual would give a small involution centralizer at this vertex, forcing
the same excluded residual. Characteristic two also excludes cubic residuals.
The proved universal-tree recognition therefore applies without an overlap
order bound, retaining all three maps of the original amalgam.

Source: Goldschmidt (1980), (4.2) and Sections5--6; Aschbacher--Smith
14.2.21, printed p.988, the cubic part of the F.1.12 application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterF.Source
open SourceAssembly SourceAssembly.Goldschmidt GreenBook RankTwoAmalgam
variable {G : Type*} [Group G] [Finite G]

private theorem no_alternating_residual (T : Sylow 2 G) (A : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A)
    (hc : centralizer (pCore 2 A : Set A) ≤ pCore 2 A)
    (hAZ : A ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ¬ Nonempty ((pResidual 2 A) ≃* alternatingGroup (Fin 4)) := by
  rintro ⟨e⟩
  let N := (pResidual 2 A).map A.subtype
  have hNA : N ≤ A := map_subtype_le _
  have hn : (N.subgroupOf A).Normal := by
    change ((pResidual 2 A).map A.subtype).comap A.subtype |>.Normal
    rw [comap_map_eq_self_of_injective A.subtype_injective]
    infer_instance
  have hc' : A ⊓ centralizer (A.pCoreIn 2 : Set G) ≤ A.pCoreIn 2 := by
    rintro x ⟨hx,hxc⟩
    refine ⟨⟨x,hx⟩,hc ?_,rfl⟩
    intro a ha
    exact Subtype.ext (hxc a (mem_map_of_mem A.subtype ha))
  let eN : N ≃* alternatingGroup (Fin 4) :=
    (equivMapOfInjective (pResidual 2 A) A.subtype A.subtype_injective).symm.trans e
  have hz : center N = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro n hn
    have hm : eN n ∈ center (alternatingGroup (Fin 4)) :=
      (Subgroup.centerCongr eN ⟨n,hn⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hm
    exact eN.injective (hm.trans eN.map_one.symm)
  have hne : N ≠ ⊥ := by
    intro hb
    have hcard := Nat.card_congr eN.toEquiv
    rw [hb, card_bot, nat_card_alternatingGroup] at hcard
    norm_num [Nat.factorial] at hcard
  obtain ⟨z,hzN,hzT,hz1⟩ := exists_omegaCenter_mem_normal A N T hTA hNA hn hc' hne
  have hzC : (⟨z,hzN⟩ : N) ∈ center N := by
    apply mem_center_iff.mpr
    intro n
    exact Subtype.ext ((hAZ (hNA n.property)) z hzT).symm
  rw [hz,mem_bot] at hzC
  exact hz1 (congrArg Subtype.val hzC)

private def resEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    pResidual 2 H ≃* pResidual 2 K :=
  (e.subgroupMap (pResidual 2 H)).trans (MulEquiv.subgroupCongr (map_pResidual 2 e))

omit [Finite G] in
private theorem exceptional_transport {H : Type*} [Group H]
    {A B : Subgroup G} {C D : Subgroup H}
    (e : Iso (inclusionAmalgam A B) (inclusionAmalgam C D))
    (h : ExceptionalMarkedAmalgam C D) : ExceptionalMarkedAmalgam A B := by
  rcases h with ⟨E⟩ | ⟨E⟩ | ⟨E⟩ | ⟨E⟩
  · exact Or.inl ⟨e.trans E.some⟩
  · exact Or.inr (Or.inl ⟨e.trans E.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans E.some⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.trans E.some⟩))

private theorem exceptional_cubic_of_no_alternating
    (A B : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hAB : A ⊓ B = (T : Subgroup G))
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hcore : pCore 2 (A ⊔ B : Subgroup G) = ⊥)
    (hAlt : ¬ Nonempty ((pResidual 2 A) ≃* alternatingGroup (Fin 4))) :
    ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A := by
  let α := inclusionAmalgam A B
  have hSA : Chapter1.IsSylowIn 2 (A ⊓ B) A := by
    rw [hAB]
    exact ⟨T.subtype hTA, by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTA]⟩
  have hSB : Chapter1.IsSylowIn 2 (A ⊓ B) B := by
    rw [hAB]
    exact ⟨T.subtype hTB, by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTB]⟩
  have hp : PrimitiveCubic α := ChapterF.Source.primitiveCubic_of_local_sylows
    A (A ⊓ B) B hSA hSB eA eB hcore
  let F := Universal.cosetFamily α
  have ht : CubicTreeAction F := universalCubicTreeAction α hp
  let : Finite (F false) := ht.finite false
  let : Finite (F true) := ht.finite true
  let e := Universal.markedIso α hp.sylow.left_injective hp.sylow.right_injective
  have qA : ((F false) ⧸ pCore 2 (F false)) ≃* Equiv.Perm (Fin 3) :=
    (LocalCoreTransport.quotientEquiv 2 e.left.symm).trans eA
  have qB : ((F true) ⧸ pCore 2 (F true)) ≃* Equiv.Perm (Fin 3) :=
    (LocalCoreTransport.quotientEquiv 2 e.right.symm).trans eB
  have hC (i : Bool) : ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)) := by
    cases i
    · rintro ⟨c⟩
      exact residual_not_cubic_of_characteristicTwo hA ⟨(resEquiv e.left).trans c⟩
    · rintro ⟨c⟩
      exact residual_not_cubic_of_characteristicTwo hB ⟨(resEquiv e.right).trans c⟩
  have hAltA : ¬ Nonempty ((pResidual 2 (F false)) ≃* alternatingGroup (Fin 4)) := by
    rintro ⟨c⟩
    exact hAlt ⟨(resEquiv e.left).trans c⟩
  have hAlts (i : Bool) : ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)) := by
    cases i
    · exact hAltA
    · rintro ⟨c⟩
      obtain ⟨v,hv,hn,hi⟩ := ht.swap.exists_small_centralizer_involution_of_alternating c qB
      have := residual_cubic_or_alternatingFour_of_involution_index_le_two qA hv hn hi
      exact this.elim (hC false) hAltA
  have hr := ht.twoPerfectResidual
  have hrC (i : Bool) : ¬ Nonempty ((pResidual 2 (residualFamily F i)) ≃* Multiplicative (ZMod 3)) := by
    rintro ⟨c⟩
    exact hC i ⟨(ht.residualLocalEquiv i).symm.trans c⟩
  have hrAlt (i : Bool) : ¬ Nonempty ((pResidual 2 (residualFamily F i)) ≃* alternatingGroup (Fin 4)) := by
    rintro ⟨c⟩
    exact hAlts i ⟨(ht.residualLocalEquiv i).symm.trans c⟩
  obtain ⟨s,hs,ho,hreg,hsing⟩ :=
    hr.toCubicTreeAction.exists_large_odd_singularityIndex_of_large_residual hrC hrAlt
  have hsource : LargeTreeSource (residualFamily F) s := ⟨hr,hrC,hrAlt,hs,ho,hreg,hsing⟩
  have hm := marked_base_of_source_cuts canonicalLabelsInput canonicalRadius radiusTwoMarkedInput
    MathieuRadiusThree.radiusThreeMarkedInput hsource
  rcases exceptional_of_marked_residual ht hm with hAB' | hBA'
  · exact Or.inl (exceptional_transport e hAB')
  · apply Or.inr
    apply exceptional_transport (C := F true) (D := F false) _ hBA'
    exact {
      left := e.right
      right := e.left
      middle := (MulEquiv.subgroupCongr (inf_comm B A)).trans
        (e.middle.trans (MulEquiv.subgroupCongr (inf_comm (F false) (F true))))
      left_commutes := fun x => e.right_commutes ⟨x.val,x.property.2,x.property.1⟩
      right_commutes := fun x => e.left_commutes ⟨x.val,x.property.2,x.property.1⟩ }

/-- The original cubic pair is recognized using the actual central Sylow
involutions at the first vertex, without a size or classification premise. -/
theorem exceptional_cubic_of_centralized_omegaCenter
    (A B : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hAB : A ⊓ B = (T : Subgroup G))
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hc : centralizer (pCore 2 A : Set A) ≤ pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hcore : pCore 2 (A ⊔ B : Subgroup G) = ⊥)
    (hAZ : A ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A :=
  exceptional_cubic_of_no_alternating A B T hTA hTB hAB eA eB
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hc) hB hcore
    (no_alternating_residual T A hTA hc hAZ)

end CFSG.Quasithin.ChapterF.Source
