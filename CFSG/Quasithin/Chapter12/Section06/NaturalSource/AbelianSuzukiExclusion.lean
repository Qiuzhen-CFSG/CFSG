module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalMovement
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSuzukiCentralizer
public import Theory.SpecificGroups.Suzuki.ElementaryCentralizer

/-!
# The normal Suzuki exclusion on the original reduced actor

The normal subgroup C = L₁-star intersect C_H-star(K₀-star) fixes the
entire Suzuki moved space by the previously recognized natural section.
Full movement by a nontrivial normal local actor would then make K₀-star
act trivially on the original faithful section U_H/V₁. Thus C is trivial,
in both the normal and exchanged Suzuki cases.

If K is normal, K₀ = K. The actual Sylow E₉ of L₁ survives the two-core
quotient and has a nontrivial centralizer on K-star, since the full Suzuki
automorphism group has three-rank at most one. This contradicts C = 1.
The normal Suzuki row is therefore excluded. The final application uses
the source's actual replacement J = K₀L₁T and preserves every quotient.

The exchanged Suzuki field-action argument, the remaining group/module
sieve and universal NaturalReduction are not concluded here.
Source: Aschbacher--Smith 12.6.30--31, printed pp.835--836.
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
/-- Normality, Suzuki-section fixation and the original F.9 seed force
the centralizer intersection to vanish on the actual reduced actor. -/
theorem SourceHypothesis.original_abelian_suzuki_residual_centralizer_eq_bot
    {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    actorImage H (D.fullSetup hZ T z).L₁ ⊓
      centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
        Set (H ⧸ pCore 2 H)) = ⊥ := by
  let K₀ := actorImage H (conjugateSpanBy K (T : Subgroup G))
  let C := actorImage H (D.fullSetup hZ T z).L₁ ⊓
    centralizer (K₀ : Set (H ⧸ pCore 2 H))
  change C = ⊥
  by_contra hC
  let : C.Normal := S.original_abelian_residual_centralizer_normal D hZ z hz hTV hH hKH hK hgen
  obtain ⟨hU,a,_⟩ := S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  have hK₀ : K₀ ≠ ⊥ := by
    let : IsQuasisimple (actorImage H K) :=
      (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
        (componentStarEquiv H K hKH hK)
    let : IsSimpleGroup ((actorImage H K) ⧸ center (actorImage H K)) := IsQuasisimple.simple
    let : Nontrivial (actorImage H K) := (QuotientGroup.mk'_surjective (center (actorImage H K))).nontrivial
    have hh : actorImage H K ≤ K₀ := map_mono (comap_mono (le_conjugateSpanBy K T))
    intro hz
    exact (nontrivial_iff_ne_bot _).mp inferInstance (bot_unique (hh.trans_eq hz))
  exact S.original_normal_local_actor_not_fix_moved D hZ z hz hTV hTz hbound hH a C K₀ hC hK₀
    (inf_le_left.trans (map_mono (comap_mono le_sup_left))) inf_le_right
    (S.original_abelian_suzuki_centralizer_fixes_moved D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen a hm eK)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original normal-component Suzuki row contradicts the surviving
Sylow E₉; no source subgroup or action kernel is replaced. -/
theorem SourceHypothesis.original_abelian_normal_suzuki_impossible
    (hn : (K.subgroupOf H).Normal) {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let E := D.fullSetup hZ T z
  let A : Sylow 3 E.L₁ := Classical.choice inferInstance
  let P := (A : Subgroup E.L₁).map E.L₁.subtype
  obtain ⟨hP,hcard,_⟩ := S.original_point_sylow_star D hZ z hz hTz hH A
  change IsElementaryAbelian 3 (actorImage H P) at hP
  change Nat.card (actorImage H P) = 9 at hcard
  let _ := hP
  let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  let e := (componentStarEquiv H K hKH hK).symm.trans eK
  have hne := BenderSuzuki.MatrixGroups.elementary_nine_centralizer_normal_suzuki_ne_bot
    (actorImage H K) (actorImage H P) hcard hm e
  have hzC := S.original_abelian_suzuki_residual_centralizer_eq_bot D hZ z hz hTV hTz
    hbound hTI hns hH hKH hK hgen hm eK
  rw [conjugateSpan_eq_of_normal H K T hKH (fun x hx => hH.1.2 (Or.inr hx)) hn] at hzC
  apply hne
  exact bot_unique ((inf_le_inf_right _
    (map_mono (comap_mono (show P ≤ E.L₁ from map_subtype_le _)))).trans_eq hzC)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Any Suzuki marking left in the source sieve must be exchanged,
with the literal relative normalizer index two. -/
theorem SourceHypothesis.original_abelian_suzuki_forces_exchange
    {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ¬ (K.subgroupOf H).Normal ∧ (normalizer (K.subgroupOf H : Set H)).index = 2 := by
  have hn : ¬ (K.subgroupOf H).Normal := fun hn =>
    S.original_abelian_normal_suzuki_impossible D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hm eK
  obtain ⟨hi,_⟩ := S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz
    hbound hTI hns hH hKH hK hgen hn
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  exact ⟨hn,(cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans hi⟩

include hz hTV hTz hbound hTI hns hH in
/-- On the source's actual reduced actor, any remaining Suzuki marking
must be exchanged, and its centralizer inside L₁-star is trivial. -/
theorem SourceHypothesis.original_abelian_reduced_suzuki_restrictions :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      ∀ m : ℕ, 0 < m →
        Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
        actorImage J (D.fullSetup hZ T z).L₁ ⊓
          centralizer (actorImage J K₀ : Set (J ⧸ pCore 2 J)) = ⊥ ∧
        ¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  rintro m hm ⟨e⟩
  exact ⟨S.original_abelian_suzuki_residual_centralizer_eq_bot D hZ z hz hTV hTz
    hbound hTI hns hJ hKle hKJ rfl hm e,
    S.original_abelian_suzuki_forces_exchange D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ rfl hm e⟩

end CFSG.Quasithin.Chapter12.Section06
