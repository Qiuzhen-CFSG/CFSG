module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.PairedActor

/-!
# The F.9.18 group models for the original abelian component

On the literal action of H/O₂(H) on U_H/V₁, the same edge-core actor
is quadratic and faithful on the Sylow component orbit. If K is normal
in H, A.3.6 bounds the center of K-star by one or three; the small quadratic
classification then gives the complete group list in F.9.18(4). Otherwise
A.3.8 gives its index-two normalizer, and the paired quadratic calculation
gives binary PSL₂, Suzuki or PSL₃(2), as in F.9.18(5).

The intrinsic quotient equivalence K/O₂(K) ≃ K-star transports both lists.
The final application constructs the escaping component and uses its actual
reduced actor K₀L₁T. Earlier geometry remains explicit. This proves the group
model clauses, not the module alternatives or the finer 12.6.31 conclusion.
Source: Aschbacher--Smith F.9.18(4--5), pp.325--326, and12.6.30--31,
pp.835--836, combined manuscript of1 March2004.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The normal-component group list, including its central quotient and
exclusion of the triple cover of A₇, on the actual original actor. -/
theorem SourceHypothesis.original_abelian_normal_component_models
    (hn : (K.subgroupOf H).Normal) : Models.F918Models (actorImage H K) := by
  obtain ⟨hcomp,hU,a,B,_,_,hE,hquad,hcodim,hfaith,_⟩ :=
    S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
  let _ := hU
  let : IsQuasisimple (actorImage H K) := hcomp.2
  let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
  have hsq := S.original_star_sqtk D hZ z hz hH
  have hcenter : Nat.card (center (actorImage H K)) = 1 ∨
      Nat.card (center (actorImage H K)) = 3 := by
    rcases ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
      hsq (pCore_quotient_pCore_eq_bot 2) (hcomp.isCComponent) with
      ⟨hs,_⟩ | ⟨⟨e⟩,_⟩
    · let := hs
      exact Or.inl (Subgroup.card_eq_one.mpr CoverModels.center_eq_bot_of_simple)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod 3))
  rw [conjugateSpan_eq_of_normal H K T hKH (fun x hx => hH.1.2 (Or.inr hx)) hn] at hfaith
  exact f918Models_of_quadratic_actor a.representation (actorImage H K)
    (B.map (QuotientGroup.mk' (pCore 2 H))) a.faithful hcenter hsq hE hquad hcodim hfaith

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The genuine exchanged-component list with its relative normalizer index.
Both the small quadratic actor and the A.3.8 list are proved source inputs. -/
theorem SourceHypothesis.original_abelian_nonnormal_component_models
    (hn : ¬ (K.subgroupOf H).Normal) :
    (normalizer (actorImage H K : Set (H ⧸ pCore 2 H))).index = 2 ∧
      NonnormalF918Models (actorImage H K) := by
  obtain ⟨hcomp,hU,a,B,_,hBT,hE,hquad,hcodim,hfaith,_⟩ :=
    S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
  let _ := hU
  have hsq := S.original_star_sqtk D hZ z hz hH
  have hindexmodels : (normalizer (actorImage H K : Set (H ⧸ pCore 2 H))).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (actorImage H K) := by
    rcases ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple
      hsq (pCore_quotient_pCore_eq_bot 2) (actorImage H K) (hcomp.isCComponent)
      with hnormal | hm
    · let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
      exact (hn (cComponent_normal_of_quotient_normal hK (pCore 2 H) hnormal)).elim
    · exact hm
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let P := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hmove : ¬ actorImage H T ≤ normalizer (actorImage H K : Set (H ⧸ pCore 2 H)) := by
    intro ht
    have hd := index_dvd_of_le ht
    rw [hindexmodels.1] at hd
    exact P.not_dvd_index hd
  have ho : actorImage H (conjugateSpanBy K (T : Subgroup G)) =
      conjugateSpanBy (actorImage H K) (actorImage H T) :=
    star_conjugateSpan H K T hKH hTH
  rw [ho,conjugateSpanBy_eq_iSup_conj] at hfaith
  exact ⟨hindexmodels.1,nonnormal_models_of_quadratic_actor a.representation
    (actorImage H K) (actorImage H T) (B.map (QuotientGroup.mk' (pCore 2 H)))
    hcomp hsq hindexmodels.2 hindexmodels.1 hmove a.faithful hBT hE hquad hcodim hfaith⟩

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Exhaustive group-model alternatives, retaining relative normality and
transport through the literal intrinsic two-core quotient. -/
theorem SourceHypothesis.original_abelian_component_model_alternatives :
    ((K.subgroupOf H).Normal ∧ Models.F918Models (actorImage H K) ∧
      Models.F918Models (K ⧸ pCore 2 K)) ∨
    (¬ (K.subgroupOf H).Normal ∧ (normalizer (K.subgroupOf H : Set H)).index = 2 ∧
      NonnormalF918Models (actorImage H K) ∧ NonnormalF918Models (K ⧸ pCore 2 K)) := by
  classical
  by_cases hn : (K.subgroupOf H).Normal
  · have hm := S.original_abelian_normal_component_models D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn
    exact Or.inl ⟨hn,hm,f918Models_transport (componentStarEquiv H K hKH hK) hm⟩
  · obtain ⟨hi,hm⟩ := S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    exact Or.inr ⟨hn,(cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans hi,
      hm,hm.transport (componentStarEquiv H K hKH hK)⟩

include hz hTV hTz hbound hTI hns hH in
/-- Construct the escaping component and apply the exhaustive group-model
sieve in its reduced actor, preserving the original H and intrinsic quotient. -/
theorem SourceHypothesis.original_abelian_reduced_component_models :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (((K.subgroupOf J).Normal ∧ Models.F918Models (actorImage J K) ∧
          Models.F918Models (K ⧸ pCore 2 K)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          NonnormalF918Models (actorImage J K) ∧ NonnormalF918Models (K ⧸ pCore 2 K))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  exact S.original_abelian_component_model_alternatives D hZ z hz hTV hTz hbound hTI hns hJ
    ((le_conjugateSpanBy K T).trans (le_sup_left.trans le_sup_left)) hKJ rfl

end CFSG.Quasithin.Chapter12.Section06
