module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.AlternatingCoreGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional

/-!
# The A₇ exclusion in the original abelian component catalogue

An escaping component normalized by T cannot have intrinsic two-core
quotient A₇. The actual quotient action makes KT E₁-generated; its even
order makes its generation parameter exactly one. Original12.6.29 then
puts KT, and hence K, inside M, a contradiction.

For a normal component the preceding F.9.18 group list and A.3.6 cover
classification give concrete carriers, retaining Suzuki. The application
below combines these identifications with the A₇ exclusion on the same
K/O₂(K), without assuming the full12.6.31 alternatives or any module row.
Source: Aschbacher--Smith12.6.31, p.836, using E.1.14(3), p.214.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
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

include hz hTV hTz hbound hTI hns in
/-- Generation one excludes A₇ on the literal two-core quotient of an
escaping T-invariant subgroup. No component-selection premise is required. -/
theorem SourceHypothesis.original_escaping_alternatingSeven_impossible
    {K : Subgroup G} (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ M L) (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) : False := by
  let J := K ⊔ (T : Subgroup G)
  have hcard : Nat.card (K ⧸ pCore 2 K) = 2520 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hd : 2 ∣ Nat.card J :=
    (show 2 ∣ Nat.card (K ⧸ pCore 2 K) by rw [hcard]; norm_num).trans
      ((card_quotient_dvd_card (pCore 2 K)).trans
        (card_dvd_of_le (show K ≤ J from le_sup_left)))
  have hn : ChapterE.generationParameter J = 1 :=
    ChapterE.ExceptionalValues.generationParameter_eq_one_of_upper (fun ho => ho.not_two_dvd_nat hd)
      (ChapterE.isEGenerated_one_of_alternatingSeven_quotient K T hTK e)
  exact hout (le_sup_left.trans (S.original_generation_one_overgroup_le D hZ z hz hTV hTz
    hbound hTI hns (show (T : Subgroup G) ≤ J from le_sup_right) hn))

include hz hTV hTz hbound hTI hns in
/-- The normal branch has concrete component carriers (including Suzuki),
with A₇ excluded on the same intrinsic quotient. -/
theorem SourceHypothesis.original_abelian_normal_component_catalogue
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) (hout : ¬ K ≤ M L)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H) (hn : (K.subgroupOf H).Normal) :
    Models.ComponentModelOrSuzuki (actorImage H K) ∧
      Models.ComponentModelOrSuzuki (K ⧸ pCore 2 K) ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) := by
  have hq := S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK
  let e : (K ⧸ pCore 2 K) ≃* actorImage H K := componentStarEquiv H K hKH hK
  let : IsQuasisimple (actorImage H K) := hq.of_mulEquiv e
  have hcomp : (actorImage H K).IsCComponent := starImage_isCComponent H K hK
  have hA := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    (S.original_star_sqtk D hZ z hz hH) (pCore_quotient_pCore_eq_bot 2) hcomp
  have hm : Models.ComponentModelOrSuzuki (actorImage H K) :=
    CoverModels.SourceApplication.classified_of_source
      (S.original_abelian_normal_component_models D hZ z hz hTV hTz hbound hTI hns
        hH hKH hK hgen hn) (hA.elim (fun hs => Or.inl hs.1) Or.inr)
  have hmi : Models.ComponentModelOrSuzuki (K ⧸ pCore 2 K) := by
    rcases hm with hm | ⟨m,hm,he⟩
    · exact Or.inl (hm.of_mulEquiv e)
    · exact Or.inr ⟨m,hm,he.map (e.trans ·)⟩
  refine ⟨hm,hmi,?_⟩
  rintro ⟨e₇⟩
  exact S.original_escaping_alternatingSeven_impossible D hZ z hz hTV hTz hbound hTI hns
    ((show (T : Subgroup G) ≤ H from fun x hx => hH.1.2 (Or.inr hx)).trans
      ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)) hout e₇

include hz hTV hTz hbound hTI hns in
/-- Apply the concrete catalogue and A₇ exclusion after constructing the
source's escaping component and changing to its actual reduced actor. -/
theorem SourceHypothesis.original_abelian_reduced_component_catalogue
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (((K.subgroupOf J).Normal ∧ Models.F918Models (actorImage J K) ∧
          Models.ComponentModelOrSuzuki (actorImage J K) ∧
          Models.ComponentModelOrSuzuki (K ⧸ pCore 2 K) ∧
          ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          NonnormalF918Models (actorImage J K) ∧ NonnormalF918Models (K ⧸ pCore 2 K))) := by
  classical
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
  have hKle : K ≤ J := (le_conjugateSpanBy K T).trans (le_sup_left.trans le_sup_left)
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  rcases S.original_abelian_component_model_alternatives D hZ z hz hTV hTz hbound hTI hns
    hJ hKle hKJ rfl with ⟨hn,hm,_⟩ | hn
  · exact Or.inl ⟨hn,hm,S.original_abelian_normal_component_catalogue D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ hout rfl hn⟩
  · exact Or.inr hn

end CFSG.Quasithin.Chapter12.Section06
