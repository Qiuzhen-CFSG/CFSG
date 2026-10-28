module

public import CFSG.Quasithin.Chapter13.Section07.pairNaturalChief
public import CFSG.Quasithin.Chapter13.Section07.PairInternalSquare
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.NoncentralChiefRefinement.fourGroup
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralPQuotient

/-!
# Complete chief count for the original two-conjugate pair

The point plane V₁V₁ᵍ is a normal four-group with trivial intersection with
Z(I): V_H fixes V₁ but moves the other point, and the original internal
conjugator exchanges the points. Thus this plane contributes one noncentral
chief factor. The intervening E/plane is central, the original natural
O₂(I)/E layer contributes m(A*), and I/O₂(I) has order six, so its binary
chief factors are central. Concatenation and Jordan--Hölder give exactly
m(A*)+1 for every complete chief series of the literal I.

This proves the I-count used by 13.7.10(8). Its separate comparison with a
conjugate of the original L₁, which adds one factor, remains to be proved.
Source: Aschbacher--Smith, 13.7.10(8), printed p.942.
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem pair_point_plane_data
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hspan : V≤V₃⊔conjugate V₁ (g:G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let I := Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G)
    let Z := V₁⊔conjugate V₁ (g:G)
    Z≤I ∧ I≤normalizer (Z:Set G) ∧ Nat.card Z=4 ∧
      (Z.subgroupOf I)⊓center I=⊥ := by
  dsimp only
  let A := Section08.Source.VH H V
  let B := conjugate A (g:G)
  let I := A⊔B
  let P := V₁
  let R := conjugate P (g:G)
  let Z := P⊔R
  have hPV : P≤V := h.point_lt.le.trans h.plus_le
  have hgg : conjugate V (g:G)=V := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
  have hRV : R≤V := (map_mono hPV).trans hgg.le
  have hZV : Z≤V := sup_le hPV hRV
  have hVI : V≤I := (le_conjugateSpanBy V H).trans le_sup_left
  have hZA : Z≤A := hZV.trans (le_conjugateSpanBy V H)
  have hAZ : A≤normalizer (Z:Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono hZV le_rfl).trans (commutator_V_VH_le_point d h hU)).trans le_sup_left
  have hZg : conjugate Z (g:G)=Z := by
    change (P⊔R).map (MulAut.conj (g:G)⁻¹).toMonoidHom=P⊔R
    rw [Subgroup.map_sup]
    change R⊔conjugate R (g:G)=P⊔R
    have htt : conjugate R (g:G)=P := h.conjugate_twice_eq_of_square
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
      (h.square_mem_local_of_core_quotient_square g hs)
    rw [htt,sup_comm]
  have hBZ : B≤normalizer (Z:Set G) := by
    have hm := map_mono (f := (MulAut.conj (g:G)⁻¹).toMonoidHom) hAZ
    rw [map_normalizer_eq_of_bijective Z (MulAut.conj (g:G)⁻¹).bijective] at hm
    exact hZg ▸ hm
  have hIZ : I≤normalizer (Z:Set G) := sup_le hAZ hBZ
  have hCP : P≤centralizer (A:Set G) := le_centralizer_iff.mp (h.VH_le_H.trans h.H_centralizes)
  have hRnorm : R≤normalizer (P:Set G) := by
    let : IsElementaryAbelian 2 V := h.elementary
    have hc : V≤centralizer (V:Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact (hRV.trans (hc.trans (centralizer_le hPV))).trans (Subgroup.centralizer_le_normalizer _)
  have hZcard : Nat.card Z=4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint P R hRnorm (chosen_points_disjoint h (g:G) hout)]
    have hr : Nat.card R=2 := (card_map_of_injective (MulAut.conj (g:G)⁻¹).injective).trans h.point_card
    rw [show Nat.card P=2 from h.point_card,hr]
  let C := Z⊓centralizer (A:Set G)
  have hPC : P≤C := le_inf le_sup_left hCP
  have hCZ : C≠Z := by
    intro he
    have hRc : R≤centralizer (A:Set G) := le_sup_right.trans (he.symm.le.trans inf_le_right)
    have hVc : V≤centralizer (A:Set G) := hspan.trans (sup_le
      (le_centralizer_iff.mp ((VH_centralizes_UH d h hU).trans
        (inf_le_right.trans (centralizer_le (le_conjugateSpanBy V₃ H))))) hRc)
    exact hV ((conjugateSpanBy_commutative_iff V H).mpr hVc)
  have hCcard : Nat.card C=2 := by
    have hc : Nat.card C∣2^2 := by simpa [hZcard] using card_dvd_of_le (show C≤Z from inf_le_left)
    obtain ⟨k,hk,hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hc
    interval_cases k
    · have he := eq_bot_of_card_eq C (by simpa using hkc)
      have hp : P=⊥ := le_antisymm (hPC.trans he.le) bot_le
      have hh := h.point_card
      change Nat.card P=2 at hh
      rw [hp,card_bot] at hh
      contradiction
    · simpa using hkc
    · exact (hCZ (eq_of_le_of_card_ge inf_le_left (by simpa [hZcard] using hkc.ge))).elim
  have hC : C=P := (eq_of_le_of_card_ge hPC (by rw [hCcard];exact h.point_card.ge)).symm
  obtain ⟨x,_,hx⟩ := pair_internal_marked_conjugator d h hU hV g hout
  have hxP : R=P.conjBy (x:G) := hx P (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨hZV.trans hVI,hIZ,hZcard,?_⟩
  apply le_antisymm _ bot_le
  intro z hz
  have hzC : (z:G)∈C := ⟨hz.1,by
    intro a ha
    exact congrArg Subtype.val ((mem_center_iff.mp hz.2) (⟨a,(show A≤I from le_sup_left) ha⟩:I))⟩
  have hzP : (z:G)∈P := hC ▸ hzC
  have hzR : (z:G)∈R := by
    rw [hxP]
    have hm : (x:G)*(z:G)*(x:G)⁻¹∈P.conjBy (x:G) := mem_map_of_mem _ hzP
    have he : (x:G)*(z:G)*(x:G)⁻¹=(z:G) := by
      have hc : (x:G)*(z:G)=(z:G)*(x:G) := congrArg (fun a:I=>(a:G)) ((mem_center_iff.mp hz.2) x)
      rw [hc,mul_inv_cancel_right]
    rwa [he] at hm
  have he : P⊓R=⊥ := (chosen_points_disjoint h (g:G) hout).eq_bot
  have hz1 : (z:G)∈(⊥:Subgroup G) := he ▸ (show (z:G)∈P⊓R from ⟨hzP,hzR⟩)
  exact Subtype.ext hz1

/-- The complete original pair I has m(A*)+1 noncentral binary chief factors. -/
theorem pair_full_chief_refinement
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hspan : V≤V₃⊔conjugate V₁ (g:G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let A := Section08.Source.VH H V
    let B := conjugate A (g:G)
    let I := A⊔B
    let Q := (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let Astar := (((B⊓Q).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
    ∃s:ChiefSeries I,s.head=⊥ ∧ s.last=⊤ ∧ s.noncentralTwoCount=Nat.log 2 (Nat.card Astar)+1 := by
  dsimp only
  let A := Section08.Source.VH H V
  let B := conjugate A (g:G)
  let I := A⊔B
  let E := A⊓B
  let Z := V₁⊔conjugate V₁ (g:G)
  obtain ⟨hZI,hIZ,hZcard,hZcenter⟩ := pair_point_plane_data d h hU hV g hs hspan hout
  obtain ⟨hVE,_,hIE,_,_⟩ := pair_intersection_layer d h hU g hout
  have hEI : E≤I := inf_le_left.trans le_sup_left
  let zn : NormalNode I := ⟨Z.subgroupOf I,normal_subgroupOf_of_le_normalizer hIZ⟩
  let en : NormalNode I := ⟨E.subgroupOf I,normal_subgroupOf_of_le_normalizer hIE⟩
  let sn : NormalNode I := ⟨pCore 2 I,show (pCore 2 I).Normal from inferInstance⟩
  have hzcard : Nat.card zn.val=4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZI).toEquiv).trans hZcard
  obtain ⟨a,ha0,ha1,_,hac⟩ := exists_four_chief_refinement zn hzcard hZcenter
  have hgg : conjugate V (g:G)=V := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
  have hPV : V₁≤V := h.point_lt.le.trans h.plus_le
  have hZV : Z≤V := sup_le hPV ((map_mono hPV).trans hgg.le)
  have hze : zn≤en := comap_mono (hZV.trans hVE)
  obtain ⟨b,hb0,hb1⟩ := exists_chiefSeries zn en hze
  have hcentral : IsCentral zn en := by
    rw [isCentral_iff_commutator_le]
    apply commutator_le.mpr
    intro x _ y hy
    have hh : ⁅I,E⁆≤Z := by
      rw [commutator_comm]
      exact chosen_intersection_central_layer d h hU g hs
    exact hh (commutator_mem_commutator x.property hy)
  have hbc0 : b.noncentralTwoCount=0 := b.noncentralTwoCount_eq_zero_of_central (by rwa [hb0,hb1])
  obtain ⟨c,hc0,hc1,_,hcc⟩ := pair_natural_chief_count d h hU hV g hs hout
  obtain ⟨t,ht0,ht1⟩ := exists_chiefSeries sn (⊤ : NormalNode I) le_top
  obtain ⟨_,⟨e⟩⟩ := pair_twoCore_quotient d h hU hV g hout
  have h6 : Nat.card (I⧸pCore 2 I)=6 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  have hterminal : HasCentralPChiefFactors 2 (I⧸pCore 2 I) :=
    centralTwoChiefFactors_of_not_four_dvd (by rw [h6];norm_num)
  have htc : t.noncentralTwoCount=0 := t.noncentralTwoCount_eq_zero_of_centralTwo_quotient sn ht0.ge hterminal
  have hab : a.last=b.head := ha1.trans hb0.symm
  have hbc : (a.smash b hab).last=c.head := (RelSeries.last_smash hab).trans
    (hb1.trans (Subtype.ext hc0).symm)
  have hct : ((a.smash b hab).smash c hbc).last=t.head := (RelSeries.last_smash hbc).trans
    ((Subtype.ext hc1).trans ht0.symm)
  refine ⟨((a.smash b hab).smash c hbc).smash t hct,?_,?_,?_⟩
  · simpa only [RelSeries.head_smash] using ha0
  · exact (RelSeries.last_smash hct).trans ht1
  · rw [ChiefSeries.noncentralTwoCount_smash,ChiefSeries.noncentralTwoCount_smash,
      ChiefSeries.noncentralTwoCount_smash,hac,hbc0,hcc,htc]
    omega

/-- Every complete chief series of the original pair has the source count. -/
theorem pair_full_chief_count
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hspan : V≤V₃⊔conjugate V₁ (g:G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃)
    (s : ChiefSeries (Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G):Subgroup G))
    (h0 : s.head=⊥) (h1 : s.last=⊤) :
    s.noncentralTwoCount=Nat.log 2 (Nat.card
      (((conjugate (Section08.Source.VH H V) (g:G)⊓(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H))))+1 := by
  obtain ⟨t,ht0,ht1,hc⟩ := pair_full_chief_refinement d h hU hV g hs hspan hout
  exact (s.noncentralTwoCount_eq t (h0.trans ht0.symm) (h1.trans ht1.symm)).trans hc

/-- The source-constructed conjugator supplies the full pair count. -/
theorem exists_source_pair_chief_count
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let A := Section08.Source.VH H V
      let B := conjugate A (g:G)
      let I := A⊔B
      let Q := (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      let Astar := (((B⊓Q).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
      ∃s:ChiefSeries I,s.head=⊥ ∧ s.last=⊤ ∧ s.noncentralTwoCount=Nat.log 2 (Nat.card Astar)+1 := by
  obtain ⟨g,hs,hspan⟩ := exists_chosen_conjugator d
  have hout := ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,hout,pair_full_chief_refinement d h hU hV (inclusion le_sup_left g) hs hspan hout⟩

end CFSG.Quasithin.Chapter13.Section07
