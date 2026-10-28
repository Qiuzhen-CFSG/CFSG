module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisRadicalLift
public import Theory.SpecificGroups.Rudvalis.PointCoreIntersection

/-!
# The original Rudvalis point stabilizer in its ambient S₅ quotient

The original module and normalizer calculations put every nonidentity
module point in the central involution class and give its stabilizer order
12288. Restricting the native S₅ quotient identifies the kernel with the
literal intersection of the original normalizer image and the ambient
two-core. Kernel-image counting leaves image orders 6, 12 and 24.

The final theorem applies this to the escaping odd-actor component with
its original relative Sylow placement, full module and quotient marking.
It does not identify the ambient kernel with the earlier natural-action
parabolic kernel, which kills all of E₆₄. Selecting the ambient D₁₂ image,
constructing the flag/quaternion intersection, excluding J₄ and discharging
odd-normalizer control remain with qt-d-13316-source. Structural1222 retains
its final discharge with qt-theorem-d.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal ambient point-centralizer quotient and its intersection
kernel, with all possible kernel/image orders. -/
theorem unitary_original_pushingUp_rudvalis_ambient_point_quotient (s : Context T L V)
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
        ((Nat.card r.ker = 2048 ∧ Nat.card r.range = 6) ∨
          (Nat.card r.ker = 1024 ∧ Nat.card r.range = 12) ∨
          (Nat.card r.ker = 512 ∧ Nat.card r.range = 24)) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let E := ((W.subgroupOf H).subgroupOf K).map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  dsimp only
  intro z hz
  have hclass : IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) :=
    ((unitary_original_pushingUp_rudvalis_module_and_points
      s hcover hJH hc K hK e c hVW).2.2 z hz).2.1
  have hP : Nat.card
      ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) = 12288 :=
    (unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hVW).2.2 z hz
  exact Rudvalis.point_core_intersection_quotient C z hclass hP

/-- The ambient involution-centralizer quotient in the actual escaping
odd-actor component, retaining the original relative Sylow and module marking. -/
theorem unitary_original_oddActorResidual_ambient_point_quotient (s : Context T L V)
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
                ((Nat.card r.ker = 2048 ∧ Nat.card r.range = 6) ∨
                  (Nat.card r.ker = 1024 ∧ Nat.card r.range = 12) ∨
                  (Nat.card r.ker = 512 ∧ Nat.card r.range = 24))) := by
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
      unitary_original_pushingUp_rudvalis_ambient_point_quotient s hcover hJH hc K hK e c hcV⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
