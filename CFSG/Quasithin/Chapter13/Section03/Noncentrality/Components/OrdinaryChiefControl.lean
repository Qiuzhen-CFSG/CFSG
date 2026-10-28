module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryParabolic
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.Definitions
public import Theory.GroupTheory.NoncentralChiefRefinement.ExhaustedTwoLayers
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.CentralCore
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PGroup.Subnormal
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The exhausted chief-factor budget in the ordinary diagonal branch

The original actor A=L₊ is the two-residual of AT. Refine through the
literal layers W_K ≤ O₂(KAT) ≤ O₂(AT), and compare their chief count with
that of A. The selected component's nontrivial star-core action supplies
the upper moved layer. The relation [K,A]=K and residual commutator
idempotence supply movement on W_K. A budget of two therefore gives the
source bound [O₂(KAT),A] ≤ W_K, before recognizing K as a block.

The final theorem retains only the two earlier inputs needed by this step:
nontriviality of the genuine moved module and the original A chief budget.
The A₅-module recognition supplies the first. The second is the block
consequence of Baumann-normalizer escape and original 13.3.10; it is not
asserted by this module. The bound is the exact commutator input of the
ordinary block-recognition and diagonal contradiction consumers.

Source: Aschbacher--Smith, Lemma 13.3.14, last paragraph on printed p.893.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem moved_normalized (K A T : Subgroup G)
    (hn : A ≤ normalizer (K : Set G)) (ht : T ≤ normalizer (K : Set G)) :
    Diagonal.localGroup K A T ≤ normalizer (Diagonal.movedModule K A T : Set G) := by
  let J := Diagonal.localGroup K A T
  let W := reducedTwoSubgroup J
  have hWN : J ≤ normalizer (W.map J.subtype : Set G) := by
    have hw := W.le_normalizer_map J.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hw
    exact hw
  have hKN : J ≤ normalizer (K : Set G) := sup_le (sup_le K.le_normalizer hn) ht
  have hw : J ≤ normalizer (Diagonal.reducedModule K A T : Set G) := hWN
  intro a ha
  rw [Diagonal.movedModule, mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hKN ha),
    mem_normalizer_iff_map_conj_eq.mp (hw ha)]

omit [Finite G] in
private theorem moved_le_core (K A T : Subgroup G) :
    Diagonal.movedModule K A T ≤ (Diagonal.localGroup K A T).pCoreIn 2 := by
  let J := Diagonal.localGroup K A T
  have hWN : J ≤ normalizer (Diagonal.reducedModule K A T : Set G) := by
    have hw := (reducedTwoSubgroup J).le_normalizer_map J.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hw
    exact hw
  have hKW : K ≤ normalizer (Diagonal.reducedModule K A T : Set G) :=
    (le_sup_left.trans le_sup_left).trans hWN
  exact (le_normalizer_iff_commutator_le_left.mp hKW).trans
    (map_mono (reducedPSubgroup_le_pCore 2 J))

/-- The source chief-count argument on J=KAT, before any block recognition
of K. The two nontrivial commutators record the separated source layers. -/
theorem ordinary_core_commutator_le_of_chief_count
    (K A : Subgroup G) (T : Sylow 2 G)
    (hA : IsPPerfect 2 A) (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hn : A ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hW : ⁅Diagonal.movedModule K A T,A⁆ ≠ ⊥)
    (hupper : ¬ ⁅(A ⊔ (T : Subgroup G)).pCoreIn 2,A⁆ ≤
      (Diagonal.localGroup K A T).pCoreIn 2)
    (hcount : ∀ s : ChiefSeries A,
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2) :
    ⁅(Diagonal.localGroup K A T).pCoreIn 2,A⁆ ≤ Diagonal.movedModule K A T := by
  let J := Diagonal.localGroup K A T
  let S := A ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let W := Diagonal.movedModule K A T
  have hSJ : S ≤ J := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using hh
  have hQS : Q ≤ S := hQT.trans le_sup_right
  have hWQ : W ≤ Q := moved_le_core K A T
  have hWS : W ≤ S := hWQ.trans hQS
  have hQN : S ≤ normalizer (Q : Set G) := by
    have hh := (pCore 2 J).le_normalizer_map J.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hSJ.trans hh
  let : (Q.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hQN
  let : (W.subgroupOf S).Normal :=
    normal_subgroupOf_of_le_normalizer (hSJ.trans (moved_normalized K A T hn hTK))
  let w : NormalNode S := ⟨W.subgroupOf S,inferInstanceAs (W.subgroupOf S).Normal⟩
  let q : NormalNode S := ⟨Q.subgroupOf S,inferInstanceAs (Q.subgroupOf S).Normal⟩
  let r : NormalNode S := ⟨pCore 2 S,inferInstanceAs (pCore 2 S).Normal⟩
  have hqr : q ≤ r := by
    change Q.subgroupOf S ≤ pCore 2 S
    exact le_sSup ⟨inferInstance,(isPGroup_pCoreIn 2 J).comap_subtype⟩
  have hres : (pResidual 2 S).map S.subtype = A :=
    embedded_pResidual_join_pGroup A T hA T.isPGroup' hTA
  let e : pResidual 2 S ≃* A :=
    ((pResidual 2 S).equivMapOfInjective S.subtype S.subtype_injective).trans
      (MulEquiv.subgroupCongr hres)
  have hw : ⁅w.val,pResidual 2 S⁆ ≠ ⊥ := by
    intro hh
    have hm := congrArg (map S.subtype) hh
    rw [map_commutator,map_subgroupOf_eq_of_le hWS,hres,Subgroup.map_bot] at hm
    exact hW hm
  have hu : ¬ ⁅r.val,pResidual 2 S⁆ ≤ q.val := by
    intro hh
    have hm := map_mono (f := S.subtype) hh
    rw [map_commutator,hres,map_subgroupOf_eq_of_le hQS] at hm
    exact hupper hm
  have hc : ∀ s : ChiefSeries (pResidual 2 S),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2 := by
    intro s hs0 hs1
    have he := s.mapActor_complete e hs0 hs1
    have hh := hcount (s.mapActor e) he.1 he.2
    rwa [s.mapActor_noncentralTwoCount] at hh
  have hbound := residual_commutator_le_of_two_used_layers w q r
    (comap_mono hWQ) hqr pCore_isPGroup hw hu hc
  have hm := map_mono (f := S.subtype) hbound
  rw [map_commutator,hres,map_subgroupOf_eq_of_le hWS,
    map_subgroupOf_eq_of_le hQS] at hm
  exact hm


private theorem core_commutator_eq_of_twoPerfect
    (hG : IsPPerfect 2 G) (ho : Odd (Nat.card (G ⧸ pCore 2 G))) :
    ⁅pCore 2 G,(⊤ : Subgroup G)⁆ = pCore 2 G := by
  let U := ⁅(⊤ : Subgroup G),pCore 2 G⁆
  have hr : pResidual 2 G = ⊤ := (pResidual_eq_top_iff 2 G).mpr hG
  have hh := pResidual_inf_pCore_le_of_central_mod U
    (commutator_le_right _ _) (by rw [hr]) (by
      rw [hr,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ pCore 2 G)) ≃*
        (G ⧸ pCore 2 G)).toEquiv] using ho)
  rw [hr,top_inf_eq] at hh
  rw [commutator_comm]
  exact le_antisymm (commutator_le_right _ _) hh

private theorem actor_moves_moved
    (K A T : Subgroup G) (hp : IsPPerfect 2 K)
    (hgen : ⁅K,A⁆ = K)
    (hW : Diagonal.movedModule K A T ≠ ⊥) :
    ⁅Diagonal.movedModule K A T,A⁆ ≠ ⊥ := by
  let J := Diagonal.localGroup K A T
  let R := Diagonal.reducedModule K A T
  let W := Diagonal.movedModule K A T
  have hRN : J ≤ normalizer (R : Set G) := by
    have hh := (reducedTwoSubgroup J).le_normalizer_map J.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hKR : K ≤ normalizer (R : Set G) :=
    (show K ≤ J from le_sup_left.trans le_sup_left).trans hRN
  have hpR : IsPGroup 2 R :=
    (pCore_isPGroup.to_le (reducedPSubgroup_le_pCore 2 J)).map J.subtype
  have hid : ⁅W,K⁆ = W := commutator_isPPerfect_idempotent K R hp hpR hKR
  intro hc
  have h1 : ⁅⁅A,W⁆,K⁆ = ⊥ := by rw [commutator_comm A W,hc,commutator_bot_left]
  have h2 : ⁅⁅W,K⁆,A⁆ = ⊥ := by rw [hid]; exact hc
  have hh : ⁅⁅K,A⁆,W⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hgen,commutator_comm K W,hid] at hh
  exact hW hh


/-- The selected component's original star-core movement prevents the actor
core from lying in O₂(J). Both images use the actual H/O₂(H) map. -/
theorem actor_core_not_le_of_star_movement
    (H J A : Subgroup G) (K : Subgroup H) (hK : K.IsCComponent)
    (hKJ : K.map H.subtype ≤ J) (hAH : A ≤ H) (hAJ : A ≤ J)
    (hn : J ≤ normalizer (K.map H.subtype : Set G))
    (hm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),(star H A hAH).pCoreIn 2⁆ ≠ ⊥) :
    ¬ A.pCoreIn 2 ≤ J.pCoreIn 2 := by
  intro hAQ
  let B := K.map H.subtype
  let C := ⁅B,A.pCoreIn 2⁆
  have hQn : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hCQ : C ≤ J.pCoreIn 2 :=
    (commutator_mono le_rfl hAQ).trans (le_normalizer_iff_commutator_le_right.mp (hKJ.trans hQn))
  have hCB : C ≤ B :=
    le_normalizer_iff_commutator_le_left.mp (((A.pCoreIn_le 2).trans hAJ).trans hn)
  have hCBQ : C ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 J).to_le hCQ) hCB
      (normalizer_commutator_ge_left B (A.pCoreIn 2))
  have hBQ : B.pCoreIn 2 ≤ H.pCoreIn 2 := by
    have hh := map_mono (f := H.subtype) (pCoreIn_le_of_subnormal 2 hK.subnormal)
    rw [map_pCoreIn_of_injective 2 K H.subtype H.subtype_injective] at hh
    exact hh
  have hcH : C ≤ H.pCoreIn 2 := hCBQ.trans hBQ
  have hci : ⁅K,(A.subgroupOf H).pCoreIn 2⁆ ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,pCoreIn_subgroupOf 2 A H hAH,
      map_subgroupOf_eq_of_le ((A.pCoreIn_le 2).trans hAH)]
    exact hcH
  let π := QuotientGroup.mk' (pCore 2 H)
  have hs : (A.subgroupOf H).map π = star H A hAH := by
    change (A.subgroupOf H).map π = (π.comp (inclusion hAH)).range
    rw [MonoidHom.range_comp,inclusion_range]
  have hk : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcq : ⁅K,(A.subgroupOf H).pCoreIn 2⁆.map π = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [π,QuotientGroup.ker_mk'] using hci
  rw [map_commutator,map_pCoreIn_of_ker_isPGroup π hk,hs] at hcq
  exact hm hcq

open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section07.ModelExclusions
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

/-- The literal selected-component application of the two-chief calculation.
The selected star movement discharges the upper moved layer, and commutator
generation discharges the lower moved layer. The original actor's chief
budget and nontriviality of the recognized moved module remain explicit. -/
theorem ordinary_selected_core_commutator_of_count
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
      (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hTK : (T : Subgroup G) ≤ normalizer (K.map H.subtype : Set G))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K)
    (hW : Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T ≠ ⊥)
    (hcount : ∀ s : ChiefSeries (sourceOne L T P),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2) :
    ⁅(Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T).pCoreIn 2,
      sourceOne L T P⁆ ≤ Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T := by
  let A := sourceOne L T P
  let B := K.map H.subtype
  let J := Diagonal.localGroup B A T
  have hAH : A ≤ H := ordinary_point_residual_le_point d
  have hnG : A ≤ normalizer (B : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le hAH] at hh
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    T_normalizes_one L T P d.line_stable
  have hpA : IsPPerfect 2 A := ordinary_point_residual_twoPerfect
  have hpK : IsPPerfect 2 K := by
    let := hK.perfect
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hpB : IsPPerfect 2 B :=
    hpK.of_surjective (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
      (K.equivMapOfInjective H.subtype H.subtype_injective).surjective
  have hgenG : ⁅B,A⁆ = B := by
    have hh := congrArg (map H.subtype) hgen
    rwa [map_commutator,map_subgroupOf_eq_of_le hAH] at hh
  have hcore : ¬ A.pCoreIn 2 ≤ J.pCoreIn 2 :=
    actor_core_not_le_of_star_movement H J A K hK
      (le_sup_left.trans le_sup_left) hAH (le_sup_right.trans le_sup_left)
      (sup_le (sup_le B.le_normalizer hnG) hTK) hm
  have hodd : Odd (Nat.card (A ⧸ pCore 2 A)) := by
    rw [ordinary_point_residual_quotient_card d e]
    decide
  have hcoregen : ⁅A.pCoreIn 2,A⁆ = A.pCoreIn 2 := by
    have hh := congrArg (map A.subtype) (core_commutator_eq_of_twoPerfect hpA hodd)
    rwa [map_commutator, ← MonoidHom.range_eq_map,range_subtype] at hh
  have hupper : ¬ ⁅(A ⊔ (T : Subgroup G)).pCoreIn 2,A⁆ ≤ J.pCoreIn 2 := by
    intro hh
    apply hcore
    rw [← hcoregen]
    exact (commutator_mono
      (pCoreIn_mono_of_normalizes le_sup_left (sup_le A.le_normalizer hTA)) le_rfl).trans hh
  exact ordinary_core_commutator_le_of_chief_count B A T hpA hTA hnG hTK
    (actor_moves_moved B A T hpB hgenG hW) hupper hcount

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
