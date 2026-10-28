module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisThreeCentralization
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.RudvalisCubicIntersection
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.RudvalisThreeSpace

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.RudvalisThreeCentralization`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- An escaping quaternion centralizes the image of the actual original three-space. -/
theorem unitary_original_pushingUp_rudvalis_quaternion_three
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    let Zc := Z.map (MulAut.conj (c : G)).toMonoidHom
    let Uc := U.map (MulAut.conj (c : G)).toMonoidHom
    let Zbar := ((Zc.subgroupOf H).subgroupOf K).map f
    let Ubar := ((Uc.subgroupOf H).subgroupOf K).map f
    ∀ z ∈ Zbar, z ≠ 1 →
      let D := centralizer ({z} : Set Rudvalis.Model)
      ∃ X : Sylow 3 D,
        (X : Subgroup D).map D.subtype ≤ C ∧
        ∃ Q : Subgroup Rudvalis.Model, Nonempty (Q ≃* QuaternionGroup 2) ∧
          Q ≤ D.pCoreIn 2 ∧
          Q ≤ centralizer ((X : Subgroup D).map D.subtype : Set Rudvalis.Model) ∧
          Q ≤ centralizer (Ubar : Set Rudvalis.Model) ∧
          Nat.card (Q ⊓ C : Subgroup Rudvalis.Model) ≤ 4 ∧ ¬ Q ≤ C := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let E := ((W.subgroupOf H).subgroupOf K).map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  let g := (MulAut.conj (c : G)).toMonoidHom
  let Zbar := (((Z.map g).subgroupOf H).subgroupOf K).map f
  let Ubar := (((U.map g).subgroupOf H).subgroupOf K).map f
  have hZE : Zbar ≤ E := map_mono (subgroupOf_mono K
    (subgroupOf_mono H ((map_mono hZV).trans hVW)))
  dsimp only
  intro z hz hzne
  let zE : E := ⟨z,hZE hz⟩
  have hzE : zE ≠ 1 := fun h => hzne (congrArg Subtype.val h)
  obtain ⟨X,hXC,hbound⟩ :=
    unitary_original_pushingUp_rudvalis_cubic_sylow s hcover hJH hc K hK e c hVW zE hzE
  have hclass : IsConj z (Rudvalis.b^2) :=
    ((unitary_original_pushingUp_rudvalis_module_and_points s hcover hJH hc K hK e c hVW).2.2 zE hzE).2.1
  obtain ⟨Q,⟨q⟩,hQcore,hQX,hQderived⟩ :=
    Rudvalis.PointQuaternion.exists_quaternion_sylow_derived z hclass X
  have hUderived := unitary_original_pushingUp_rudvalis_original_three
    s Z B U hZV hBV hUV hTZ hTB hTU hZ hB hU hcover hJH hc K hK e c hVW z hz hzne
  have hQcard : Nat.card Q = 8 := (Nat.card_congr q.toEquiv).trans
    (by rw [Nat.card_eq_fintype_card,QuaternionGroup.card])
  have hQC : Nat.card (Q ⊓ C : Subgroup Rudvalis.Model) ≤ 4 :=
    (card_le_of_le (inf_le_inf (le_inf hQcore hQX) le_rfl)).trans hbound
  refine ⟨X,hXC,Q,⟨q⟩,hQcore,hQX,hQderived.trans (centralizer_le hUderived),hQC,?_⟩
  intro hQ
  rw [inf_eq_left.mpr hQ,hQcard] at hQC
  omega

/-- The original odd-actor application with its unchanged relative Sylow and flag. -/
theorem unitary_original_oddActorResidual_quaternion_three (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
      (c : sectionCentralizerIn (normalizer (L : Set G)) L),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          ∃ e : K ⧸ center K ≃* Rudvalis.Model,
            W = V.map (MulAut.conj (c : G)).toMonoidHom ∧
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
            let Zc := Z.map (MulAut.conj (c : G)).toMonoidHom
            let Uc := U.map (MulAut.conj (c : G)).toMonoidHom
            let Zbar := ((Zc.subgroupOf H).subgroupOf K).map f
            let Ubar := ((Uc.subgroupOf H).subgroupOf K).map f
            ∀ z ∈ Zbar, z ≠ 1 →
              let D := centralizer ({z} : Set Rudvalis.Model)
              ∃ X : Sylow 3 D,
                (X : Subgroup D).map D.subtype ≤ C ∧
                ∃ Q : Subgroup Rudvalis.Model, Nonempty (Q ≃* QuaternionGroup 2) ∧
                  Q ≤ D.pCoreIn 2 ∧
                  Q ≤ centralizer ((X : Subgroup D).map D.subtype : Set Rudvalis.Model) ∧
                  Q ≤ centralizer (Ubar : Set Rudvalis.Model) ∧
                  Nat.card (Q ⊓ C : Subgroup Rudvalis.Model) ≤ 4 ∧ ¬ Q ≤ C) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,_,_,⟨K,hK,hout,n,hn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hcS,hcV,K,hK,hout,?_⟩
  rcases hn with rfl | rfl
  · exact Or.inl ⟨e⟩
  · apply Or.inr
    have hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    exact ⟨e,unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_quaternion_three s Z B U hZV hBV hUV hTZ hTB hTU
        hZ hB hU hcover hJH hc K hK e c hcV⟩


end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
