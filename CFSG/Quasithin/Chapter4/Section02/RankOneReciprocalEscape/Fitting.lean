module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Source
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.MovedFittingProduct
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.FittingPreimage
public import Theory.GroupTheory.Fitting.OutsideComponent
public import Theory.GroupTheory.PerfectNormalizerCoreQuotient

/-!
# The reversed Fitting preimage and an outside component

The C.2.6 decomposition writes O₂,F(M) using outside A₄ blocks. The perfect
reciprocal span fixes each block, by the cubic rank bound, and centralizes
its cyclic core quotient. The perfect-actor theorem for short groups then
makes the block centralize the span, contradicting its exact normalizer H.
Thus O₂,F(M) lies in H. The reverse generalized-Fitting escape selects an
actual outside C-component of M, with quasisimple two-core quotient.

The same witnesses retain every earlier reciprocal clause. The component
acts nontrivially on the span modulo O₂(M), since quotient normalization
reflects through a normal two-group that already normalizes a perfect group.
The containment and model contradiction of 4.2.10 remain to be proved.

Source: Aschbacher--Smith, 4.2.9 and the paragraph before 4.2.10,
printed pp.609--610; C.2.6, p.145.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open ChapterC Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
private theorem cyclic_short_centralized (K B : Subgroup G) [K.Normal] [Group.IsPerfect B]
    (hK : IsShort K) [IsCyclic (K ⧸ pCore 2 K)] : ⁅K,B⁆ = ⊥ := by
  let f : B →* MulAut (K ⧸ pCore 2 K) :=
    (normalQuotientAction K (pCore 2 K)).comp B.subtype
  let _ := (IsCyclic.mulAutMulEquiv (K ⧸ pCore 2 K)).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv (K ⧸ pCore 2 K)).injective
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hf (b : B) : f b = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨f b,b,rfl⟩ : f.range) 1)
  apply SourceShortAction.perfect_centralizes_short_of_normalizes K B hK le_normalizer_of_normal
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb k hk
  let v : K := ⟨k,hk⟩
  have he := DFunLike.congr_fun (hf ⟨b,hb⟩) (QuotientGroup.mk' (pCore 2 K) v)
  simp only [f,MonoidHom.comp_apply,normalQuotientAction_apply_mk,
    MulAut.one_apply] at he
  have hh := QuotientGroup.eq_iff_div_mem.mp he
  refine ⟨(MulAut.conjNormal b v) / v,hh,?_⟩
  simp [v,div_eq_mul_inv,commutatorElement_def]

private theorem a3_centralized (K B : Subgroup G) [Group.IsPerfect B]
    (hK : IsAlternatingBlock K 3) (hBK : B ≤ normalizer (K : Set G)) : ⁅K,B⁆ = ⊥ := by
  let N := normalizer (K : Set G)
  let K' := K.subgroupOf N
  let B' := B.subgroupOf N
  let : K'.Normal := (normal_subgroupOf_iff_le_normalizer K.le_normalizer).mpr le_rfl
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBK).symm.surjective
  have hk := RankOne.Solvable.isAlternatingBlock_of_equiv
    (subgroupOfEquivOfLe K.le_normalizer).symm hK
  have hc : Nat.card (K' ⧸ pCore 2 K') = 3 := by
    obtain ⟨e⟩ := hk.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  let : IsCyclic (K' ⧸ pCore 2 K') := isCyclic_of_prime_card hc
  have he := congrArg (map N.subtype) (cyclic_short_centralized K' B' hk.2.1)
  have hkmap : K'.map N.subtype = K := map_subgroupOf_eq_of_le K.le_normalizer
  have hbmap : B'.map N.subtype = B := map_subgroupOf_eq_of_le hBK
  rwa [map_commutator,hkmap,hbmap,Subgroup.map_bot] at he

/-- C.2.6 absorbs the Fitting preimage when a perfect subgroup controls its normalizer. -/
theorem fitting_preimage_le_of_perfect_normalizer
    {κ : GroupClass} (hG : IsSQTK κ G)
    (hcG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (R M X : Subgroup G) [Group.IsPerfect X]
    (hr : IsPRadical 2 R) (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hNX : normalizer (X : Set G) ≤ M) : twoFittingCore G ≤ M := by
  let F := twoFittingCore G
  have hF : generalizedFitting F = pCore 2 F :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (subnormal_core_selfCentralizing hcG F (inferInstance : F.Normal).isSubnormal)
  obtain ⟨n,_,B,hB,hprod⟩ := ChapterC.Section02Source.fitting_ordered_moved_product
    hG R M hr hcontrol hcG
  have hall (i : Fin n) : B i ≤ M := by
    have hi := hB i
    have ha := RankOne.Solvable.isAlternatingBlock_of_equiv
      (subgroupOfEquivOfLe hi.1).symm hi.2.2.2.1
    have hb : IsChiBlockIn ((B i).subgroupOf F) :=
      ⟨⟨inferInstance,ha.2.1,hi.2.2.1.subnormal.subgroupOf⟩,.inr ⟨3,by decide,ha⟩⟩
    have hrF : primeRank 3 F ≤ 2 :=
      (Theory.GroupTheory.primeRank_le_of_injective 3 F.subtype F.subtype_injective).trans
        (hG.stronglyQuasithin 3 Nat.prime_three (by decide))
    have hn := SourceShortAction.perfect_normalizes_chi F X hF hrF _ hb
    rw [map_subgroupOf_eq_of_le hi.1] at hn
    exact ((commutator_eq_bot_iff_le_centralizer.mp
      (a3_centralized (B i) X hi.2.2.2.1 hn)).trans (Subgroup.centralizer_le_normalizer _)).trans hNX
  have hz : n = 0 := by
    by_contra hn
    exact (hB ⟨0,Nat.pos_of_ne_zero hn⟩).2.1 (hall _)
  subst n
  intro x hx
  obtain ⟨m,hm,l,_,rfl⟩ := (hprod x).mp hx
  simpa using hm.1

/-- Source 4.2.9 in the reversed local group, retaining the actual span normalizer. -/
theorem reciprocal_fitting_preimage_le
    {κ : GroupClass} {M H R X : Subgroup G}
    (h : Chapter1.RadicalExclusions.PushingUpSetup κ M R (H ⊓ M))
    (hcM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    [Group.IsPerfect X] (hXM : X ≤ M) (hNX : normalizer (X : Set G) = H) :
    twoFittingCore M ≤ H.subgroupOf M := by
  let A := X.subgroupOf M
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXM).symm.surjective
  apply fitting_preimage_le_of_perfect_normalizer h.sqtk hcM (R.subgroupOf M)
    (H.subgroupOf M) A h.radical
  · exact h.characteristic_control.trans (comap_mono inf_le_left)
  · rw [←subgroupOf_normalizer_eq hXM,hNX]

/-- An outside subgroup cannot centralize the reciprocal perfect span modulo
the core of M: that core already lies in the exact normalizer H of the span. -/
theorem outside_moves_span {M H X : Subgroup G} [Group.IsPerfect X]
    (hXM : X ≤ M) (hNX : normalizer (X : Set G) = H)
    (hcore : M.pCoreIn 2 ≤ H)
    (K : Subgroup M) (hout : ¬ K ≤ H.subgroupOf M) :
    ¬ ⁅X.subgroupOf M,K⁆ ≤ pCore 2 M := by
  let Y := X.subgroupOf M
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXM).symm.surjective
  have hQY : pCore 2 M ≤ normalizer (Y : Set M) := by
    rw [← subgroupOf_normalizer_eq hXM,hNX]
    intro q hq
    exact hcore (mem_map_of_mem M.subtype hq)
  intro hc
  have hn := normalizes_perfect_of_commutator_le Y (pCore 2 M) K
    pCore_isPGroup hQY hc
  rw [← subgroupOf_normalizer_eq hXM,hNX] at hn
  exact hout hn


/-- The proved reciprocal data through 4.2.8, kept on the same H. -/
@[expose] def ReciprocalData (L H : Subgroup G) : Prop :=
      let M := normalizer (L : Set G)
      (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype = L ∧
      (L.subgroupOf H).IsCComponent ∧
      normalizer (L.subgroupOf H : Set H) = M.subgroupOf H ∧
      (M.subgroupOf H).index = 2 ∧
      conjugateSpanBy L H ≤ H ⊓ M ∧
      normalizer (conjugateSpanBy L H : Set G) = H ∧
      H.pCoreIn 2 = (H ⊓ M).pCoreIn 2 ∧
      PushingUpSetup KnownSimple.IsKnownSimple M (H.pCoreIn 2) (H ⊓ M) ∧
      M.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      ¬ (generalizedFitting (M ⧸ pCore 2 M)).comap
        (QuotientGroup.mk' (pCore 2 M)) ≤ H.subgroupOf M

/-- The reversed source extracts a genuine component after 4.2.9, on the
same maximal pushing-up witnesses. Its containment/normality analysis in
4.2.10 is a separate remaining step. -/
@[expose] def ReciprocalComponentCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ((generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H →
      ReciprocalData L H ∧
      twoFittingCore (normalizer (L : Set G)) ≤ H.subgroupOf (normalizer (L : Set G)) ∧
      ∃ K : Subgroup (normalizer (L : Set G)),
        K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        generalizedFitting K = pCore 2 K ∧ ¬ K ≤ H.subgroupOf (normalizer (L : Set G)) ∧
        ¬ ⁅(conjugateSpanBy L H).subgroupOf (normalizer (L : Set G)),K⁆ ≤
          pCore 2 (normalizer (L : Set G)))

/-- Literal application of 4.2.9 to the perfect H-conjugate span constructed
by ambient reciprocity, followed by extraction of an outside C-component. -/
theorem reciprocal_component_case_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (Section04.oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalComponentCase L V A := by
  obtain ⟨J,H,W,hw,hr⟩ := reciprocal_case_of_not_unique h D hM A hAN hcomm ho hAV hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  have hd : ReciprocalData L H := hr hf
  obtain ⟨_,_,_,_,hXM,hNX,_,hsetup,hcore,hescape⟩ := hr hf
  have hcM := h.simpleQTKE.evenCharacteristic T _ hM.1 (le_sup_right.trans hM.2.1)
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let : Group.IsPerfect (conjugateSpanBy L H) := conjugateSpanBy_isPerfect L H
  have hfit := reciprocal_fitting_preimage_le hsetup hcM (hXM.trans inf_le_right) hNX
  obtain ⟨K,hK,hq,hfK,hout⟩ :=
    exists_characteristicTwo_cComponent_outside _ hcM hfit hescape
  refine ⟨hd,hfit,K,hK,hq,hfK,hout,?_⟩
  exact outside_moves_span (hXM.trans inf_le_right) hNX
    (hcore.trans (pCoreIn_le 2 H)) K hout

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
