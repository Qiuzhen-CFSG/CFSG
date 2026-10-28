module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianQuasisimple
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Sections

/-!
# The original quadratic actor on the abelian component spans

The actual Sylow orbit K₀ is normal and supplements the edge in H=K₀L₁T.
Since H/O₂(H) has trivial two-core, the edge two-core acts faithfully on
K₀-star. The same actor supplied by F.9.16 remains faithful and quadratic
on every intermediate span of a noncentral Irr⁺ seed, retaining both ratio
bounds and the literal representation on U_H/V₁. Quasisimplicity is supplied
by the preceding source argument, and the final constructor supplies K and
its reduced actor from the original H in Hz.

No equality K₀=O²(H) is used. The model classification in F.9.18(4--5) and
the exhaustive12.6.31 alternatives remain open. Source: Aschbacher--Smith,
F.9.18(2--3), printed p.325, and12.6.30--31, printed pp.835--836.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
open Chapter13.Section08.SolvableExclusion.Three
open Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
open Chapter13.Section08.SourceCompletion.F918
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- F.9.18(2--3) for the reduced abelian actor K₀L₁T. The same edge-core
quadratic actor is faithful on K₀-star and on every actual Irr⁺ orbit span.
The proof uses the supplement K₀(L₁T), without identifying K₀ with O²(H). -/
theorem SourceHypothesis.original_abelian_component_span_actors
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H) :
    IsComponent (H ⧸ pCore 2 H) (actorImage H K) ∧
    ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H),
      let _ := hU
      ∃ (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)
        (B : Subgroup H),
        B ≤ (((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
        B.map (QuotientGroup.mk' (pCore 2 H)) ≤ actorImage H T ∧
        IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
        IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
        fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
          2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
        B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
          centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) : Set (H ⧸ pCore 2 H)) = ⊥ ∧
        ∀ I : Submodule (ZMod 2) (Additive (((D.fullSetup hZ T z).UH H) ⧸
            (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H))),
          IsIrrPlus a.representation (actorImage H (conjugateSpanBy K (T : Subgroup G))) I →
          ∀ X : Subgroup (H ⧸ pCore 2 H), actorImage H K ≤ X → actorImage H T ≤ X →
            SpanActorResult a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) X I := by
  let E := D.fullSetup hZ T z
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  let K₀ := conjugateSpanBy K (T : Subgroup G)
  have hK₀H : K₀ ≤ H := conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have ho : K₀.subgroupOf H = conjugateSpanBy (K.subgroupOf H) (T.subgroupOf H) :=
    subgroupOf_conjugateSpan H K T hKH hTH
  have hN : (K₀.subgroupOf H).Normal := by
    rw [ho]
    exact conjugateSpanBy_sylow_normal (K.subgroupOf H) (T.subtype hTH)
      (Chapter1.Section02.proposition_1_2_1_three_orbit_source
        (S.original_star_sqtk D hZ z hz hH) hK)
  let : (actorImage H K₀).Normal := hN.map _ (QuotientGroup.mk'_surjective _)
  let J := (L ⊔ (T : Subgroup G)) ⊓ H
  have hLJ : E.L₁ ≤ J := le_inf
    ((show E.L₁ ≤ L from (map_subtype_le _).trans inf_le_left).trans le_sup_left) hLH
  have hTJ : (T : Subgroup G) ≤ J := le_inf le_sup_right hTH
  have hJ : K₀ ⊔ J = H := by
    apply le_antisymm (sup_le hK₀H inf_le_right)
    calc
      H = K₀ ⊔ E.L₁ ⊔ (T : Subgroup G) := hgen.symm
      _ ≤ K₀ ⊔ J := sup_le (sup_le le_sup_left (hLJ.trans le_sup_right))
        (hTJ.trans le_sup_right)
  have hstar : actorImage H K₀ ⊔ actorImage H J = ⊤ := by
    unfold actorImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hK₀H (show J ≤ H from inf_le_right),hJ,
      subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hfaith : actorImage H (J.pCoreIn 2) ⊓
      centralizer (actorImage H K₀ : Set (H ⧸ pCore 2 H)) = ⊥ :=
    centralizer_inf_eq_bot_of_supplement _ _ _ hstar
      (starImage_isPGroup H _ (isPGroup_pCoreIn 2 J))
      (starImage_normalizes H (le_normalizer_pCoreIn 2 J)) (hstar_twoCore H)
  have hq := S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK
  let eK : K ≃* K.subgroupOf H := (subgroupOfEquivOfLe hKH).symm
  have hqi : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    hq.of_mulEquiv (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK))
  have hcomp : IsComponent (H ⧸ pCore 2 H) (actorImage H K) := by
    have hc := actorImage_component_of_intrinsic H (K.subgroupOf H) hK hqi
    rwa [map_subgroupOf_eq_of_le hKH] at hc
  obtain ⟨hU,a,_,B,hB,hE,hquad,hcodim,_⟩ :=
    S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  have hBT := source_internal_actor_le_sylow T hTH B hB
  have hf : B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
      centralizer (actorImage H K₀ : Set (H ⧸ pCore 2 H)) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (map_mono hB)).trans_eq hfaith)
  refine ⟨hcomp,hU,a,B,hB,hBT,hE,hquad,hcodim,hf,?_⟩
  have hspan : actorImage H K₀ = conjugateSpanBy (actorImage H K) (actorImage H T) :=
    star_conjugateSpan H K T hKH hTH
  intro I hI X hKX hTX
  rw [hspan] at hf hI
  exact spanActorResult a.representation (actorImage H K) (actorImage H T)
    (B.map (QuotientGroup.mk' (pCore 2 H))) X hcomp hKX hTX (hBT.trans hTX)
    hE hquad hcodim hf I hI

/-- The original escaping component supplies every premise of the
section-actor theorem on its actual reduced group. -/
theorem SourceHypothesis.original_abelian_reduced_span_actors
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
          IsComponent (J ⧸ pCore 2 J) (actorImage J K) ∧
          ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH J),
            let _ := hU
            ∃ (a : LocalQuotientAction J ((D.fullSetup hZ T z).UH J) (D.fullSetup hZ T z).V₁)
              (B : Subgroup J),
              B ≤ (((L ⊔ (T : Subgroup G)) ⊓ J).pCoreIn 2).subgroupOf J ∧
              B.map (QuotientGroup.mk' (pCore 2 J)) ≤ actorImage J T ∧
              IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
              IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
              fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 J))) ≤
                2 * rank (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
              B.map (QuotientGroup.mk' (pCore 2 J)) ⊓
                centralizer (actorImage J (conjugateSpanBy K (T : Subgroup G)) : Set (J ⧸ pCore 2 J)) = ⊥ ∧
              ∀ I : Submodule (ZMod 2) (Additive (((D.fullSetup hZ T z).UH J) ⧸
                  (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH J))),
                IsIrrPlus a.representation (actorImage J (conjugateSpanBy K (T : Subgroup G))) I →
                ∀ X : Subgroup (J ⧸ pCore 2 J), actorImage J K ≤ X → actorImage J T ≤ X →
                  SpanActorResult a.representation (B.map (QuotientGroup.mk' (pCore 2 J))) X I := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  exact S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hJ
    ((le_conjugateSpanBy K T).trans (le_sup_left.trans le_sup_left)) hKJ rfl

end CFSG.Quasithin.Chapter12.Section06
