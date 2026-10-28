module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisAmbientOrder
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.RudvalisModuleIntersection
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.RudvalisPointParabolic

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.RudvalisAmbientOrder`.
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

/-- The ambient two-core intersection is the kernel of the actual D₁₂ quotient,
and contains all commutators with the literal point stabilizer's two-core. -/
theorem unitary_original_pushingUp_rudvalis_ambient_point_order (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
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
    let E := ((W.subgroupOf H).subgroupOf K).map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      let P := D.subgroupOf C
      ∃ q : D →* Equiv.Perm (Fin 5),
        Function.Surjective q ∧ q.ker = pCore 2 D ∧
        let i : P →* D := {
          toFun := fun x => ⟨x.val.val,x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
        let r := q.comp i
        r.ker = ((D.pCoreIn 2).subgroupOf C).subgroupOf P ∧
        r.ker.map (C.subtype.comp P.subtype) = C ⊓ D.pCoreIn 2 ∧
        Nat.card r.ker = 1024 ∧ Nat.card r.range = 12 ∧
        ∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧
          ((E.subgroupOf C).subgroupOf P).map r = zpowers t ∧
          r.range = centralizer ({t} : Set (Equiv.Perm (Fin 5))) ∧
          Nonempty ((P ⧸ r.ker) ≃* DihedralGroup 6) ∧ ⁅pCore 2 P,⊤⁆ ≤ r.ker := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let E := ((W.subgroupOf H).subgroupOf K).map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  have hcent : C ⊓ centralizer (E : Set Rudvalis.Model) = E :=
    (unitary_original_pushingUp_rudvalis_normalizer s hcover hJH hc K hK e c hVW).2.2
  have hEC : E ≤ C := hcent.ge.trans inf_le_left
  have hEcentral : E ≤ centralizer (E : Set Rudvalis.Model) := hcent.ge.trans inf_le_right
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  have hED : E ≤ D := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact (mem_centralizer_iff.mp (hEcentral hu) z z.property).symm
  have hclass : IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) :=
    ((unitary_original_pushingUp_rudvalis_module_and_points
      s hcover hJH hc K hK e c hVW).2.2 z hz).2.1
  have hPcard : Nat.card P = 12288 :=
    (unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hVW).2.2 z hz
  have hintersect : Nat.card (E ⊓ D.pCoreIn 2 : Subgroup Rudvalis.Model) = 32 :=
    unitary_original_pushingUp_rudvalis_module_core_intersection s hcover hJH hc K hK e c hVW z hz
  have hex := unitary_original_pushingUp_rudvalis_point_parabolic
    s hcover hJH hc K hK e c hVW z hz
  let b : P →* Atlas.G2.BinaryCore.secondParabolic := Classical.choose hex
  have hbdata := Classical.choose_spec hex
  have hcore : Nat.card (pCore 2 Atlas.G2.BinaryCore.secondParabolic) = 32 := by
    rw [←Atlas.G2.LieParabolicSetup.local₂_binary]
    exact Atlas.G2.LieParabolicSetup.card_local₂_pCore_binary
  exact Rudvalis.point_core_intersection_exact C E hEC z hED hclass hPcard hintersect
    b hbdata.1 hbdata.2.1 Atlas.G2.BinaryCore.secondParabolic_card hcore

/-- The ambient involution-centralizer quotient in the actual escaping
odd-actor component, retaining the original relative Sylow and module marking. -/
theorem unitary_original_oddActorResidual_ambient_point_order (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
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
            let E := ((W.subgroupOf H).subgroupOf K).map f
            let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
            ∀ z : E, z ≠ 1 →
              let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
              let P := D.subgroupOf C
              ∃ q : D →* Equiv.Perm (Fin 5),
                Function.Surjective q ∧ q.ker = pCore 2 D ∧
                let i : P →* D := {
                  toFun := fun x => ⟨x.val.val,x.property⟩
                  map_one' := rfl
                  map_mul' := fun _ _ => rfl }
                let r := q.comp i
                r.ker = ((D.pCoreIn 2).subgroupOf C).subgroupOf P ∧
                r.ker.map (C.subtype.comp P.subtype) = C ⊓ D.pCoreIn 2 ∧
                Nat.card r.ker = 1024 ∧ Nat.card r.range = 12 ∧
                ∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧
                  ((E.subgroupOf C).subgroupOf P).map r = zpowers t ∧
                  r.range = centralizer ({t} : Set (Equiv.Perm (Fin 5))) ∧
                  Nonempty ((P ⧸ r.ker) ≃* DihedralGroup 6) ∧ ⁅pCore 2 P,⊤⁆ ≤ r.ker) := by
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
      unitary_original_pushingUp_rudvalis_ambient_point_order s hcover hJH hc K hK e c hcV⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
