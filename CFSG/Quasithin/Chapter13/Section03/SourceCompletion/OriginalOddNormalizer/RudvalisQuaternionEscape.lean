module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisCubicIntersection
public import Theory.SpecificGroups.Rudvalis.PointQuaternion

/-!
# An escaping quaternion in the original Rudvalis odd-actor component

The cubic selected inside the original normalizer image is Sylow in the
full ambient point centralizer. Its two-core centralizer contains an actual
quaternion subgroup of order eight. The previously proved intersection
bound of four therefore makes this quaternion escape the original image.

The final theorem applies the construction to the original odd-actor
residual, retaining the relative Sylow, whole module, section-centralizer
conjugation and central quotient marking. It assumes neither a full ambient
Sylow placement nor an identification of point centralizer and normalizer.

Placement of the original three-space in a subgroup centralized by this
quaternion, the J₄ exclusion and final odd-normalizer control remain with
qt-d-13316-source. In particular, the native core-involution diagnostic in
PointQuaternion.Core prevents replacing the required E₃₂ centralization by
centralization of every core involution. Earlier Structural1222 retains its
final discharge with qt-theorem-d.
Source: Aschbacher--Smith 4.2.13, pp.611--612, and 4.4.3, p.623,
in the original 13.3.16 application, pp.893--896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- An actual quaternion escapes the original normalizer image while
centralizing the chosen cubic inside the ambient point two-core. -/
theorem unitary_original_pushingUp_rudvalis_quaternion_escape (s : Context T L V)
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
      ∃ X : Sylow 3 D,
        (X : Subgroup D).map D.subtype ≤ C ∧
        ∃ Q : Subgroup Rudvalis.Model, Nonempty (Q ≃* QuaternionGroup 2) ∧
          Q ≤ D.pCoreIn 2 ∧
          Q ≤ centralizer ((X : Subgroup D).map D.subtype : Set Rudvalis.Model) ∧
          Nat.card (Q ⊓ C : Subgroup Rudvalis.Model) ≤ 4 ∧ ¬ Q ≤ C := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let E := ((W.subgroupOf H).subgroupOf K).map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  obtain ⟨X,hXC,hbound⟩ :=
    unitary_original_pushingUp_rudvalis_cubic_sylow s hcover hJH hc K hK e c hVW z hz
  have hclass : IsConj (z : Rudvalis.Model) (Rudvalis.b^2) :=
    ((unitary_original_pushingUp_rudvalis_module_and_points s hcover hJH hc K hK e c hVW).2.2 z hz).2.1
  obtain ⟨Q,⟨q⟩,hQcore,hQcent⟩ := Rudvalis.PointQuaternion.exists_quaternion_sylow z hclass X
  have hQcard : Nat.card Q = 8 := (Nat.card_congr q.toEquiv).trans
    (by rw [Nat.card_eq_fintype_card,QuaternionGroup.card])
  have hQC : Nat.card (Q ⊓ C : Subgroup Rudvalis.Model) ≤ 4 :=
    (card_le_of_le (inf_le_inf (le_inf hQcore hQcent) le_rfl)).trans hbound
  refine ⟨X,hXC,Q,⟨q⟩,hQcore,hQcent,hQC,?_⟩
  intro hQ
  rw [inf_eq_left.mpr hQ,hQcard] at hQC
  omega

/-- Apply the quaternion escape to the literal original odd-actor pair. -/
theorem unitary_original_oddActorResidual_quaternion_escape (s : Context T L V)
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
              ∃ X : Sylow 3 D,
                (X : Subgroup D).map D.subtype ≤ C ∧
                ∃ Q : Subgroup Rudvalis.Model, Nonempty (Q ≃* QuaternionGroup 2) ∧
                  Q ≤ D.pCoreIn 2 ∧
                  Q ≤ centralizer ((X : Subgroup D).map D.subtype : Set Rudvalis.Model) ∧
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
      unitary_original_pushingUp_rudvalis_quaternion_escape s hcover hJH hc K hK e c hcV⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
