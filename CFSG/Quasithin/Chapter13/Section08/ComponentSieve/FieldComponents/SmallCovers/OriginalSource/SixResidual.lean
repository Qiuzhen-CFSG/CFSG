module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixSelection

public import Theory.GroupTheory.NormalCentralQuotientAction.Maps

/-!
# Forcing the proper residual in the original six-cover branch

The canonical component and third-isomorphism maps identify the star action
on K*/Z(K*) with the actual H-action on K/O₂,Z(K). Hence the natural actor
obtained from a recognized hexacode section controls the literal action used
by the solvable-overgroup comparison.

If Y=L₁, the earlier universal solvable-overgroup theorem puts its whole span
in the proper overlap H∩M. The native six-group comparison then forces a
non-natural Sylow actor, contradicting the recognized action. The remaining
source residual alternative is Y=L₁,+, and it moves the full numerator U_H.

In the reducible source-module case all recognition inputs are discharged.
The general selection retains the complete homogeneous F.9.18(4) alternatives.
Their proof and the terminal V_H/U_H geometry remain with qt-d-138-fields-source;
qt-d-1381-source supplies the preceding SourceContext assumptions.
Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), using
13.8.13 and the literal central-quotient action.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.GroupAction.PCoreCentralModelAction
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open Reduction Reduction.ModuleRecognition SourceCompletion
open LocalGeometry LocalGeometry.DynkinExclusion LocalGeometry.CoverParabolics
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
attribute [local instance] Selection.starImage_normal

/-- The two central-quotient action conventions agree on the literal source maps. -/
theorem sourceAction_eq_centralModelAction
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) [(K.subgroupOf H).Normal]
    (eZ : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* AlternatingSix.ShadowLocal.A6)
    (h : H) :
    sourceAction H K hKH hK eZ (QuotientGroup.mk' (pCore 2 H) h) =
      centralModelAction H K (le_normalizer_of_normal_subgroupOf hKH)
        ((centralPreimageQuotientEquiv (pCore 2 K)).trans eZ) h := by
  let c := Components.componentStarEquiv H K hKH hK
  let d := (centralPreimageQuotientEquiv (pCore 2 K)).trans eZ
  have hm (k : K) :
      sourceCentralEquiv H K hKH hK eZ (QuotientGroup.mk' _ (c (QuotientGroup.mk' _ k))) =
        d (QuotientGroup.mk' _ k) := by
    rw [sourceCentralEquiv_mk,show (Components.componentStarEquiv H K hKH hK).symm
      (c (QuotientGroup.mk' (pCore 2 K) k)) = QuotientGroup.mk' (pCore 2 K) k from c.symm_apply_apply _]
    change eZ _ = eZ (centralPreimageQuotientEquiv (pCore 2 K) (QuotientGroup.mk' _ k))
    rw [centralPreimageQuotientEquiv_mk]
  apply MulEquiv.ext
  intro x
  obtain ⟨q,rfl⟩ := d.surjective x
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.centralPreimage (pCore 2 K)) q
  rw [centralModelAction_apply,←hm k,sourceAction_mk]
  have hc : MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) h)
      (c (QuotientGroup.mk' (pCore 2 K) k)) =
      c (QuotientGroup.mk' (pCore 2 K)
        (K.normalizerMonoidHom (inclusion (le_normalizer_of_normal_subgroupOf hKH) h) k)) := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply,Components.componentStarEquiv_mk,Components.componentStarEquiv_mk]
    rw [←map_mul,←map_inv,←map_mul]
    rfl
  rw [hc,hm]

private theorem component_le (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) : K ≤ H :=
  (le_sup_left.trans le_sup_left).trans_eq c.component.generated

/-- A natural central action rules out Y=L₁ by the genuine solvable-overgroup theorem. -/
theorem source_six_cover_residual_ne_one_of_natural
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eZ : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* AlternatingSix.ShadowLocal.A6)
    [(K.subgroupOf H).Normal]
    (hn : ∀ h : Source.Hstar H,
      sourceAction H K ((le_sup_left.trans le_sup_left).trans_eq c.component.generated)
        c.component.component eZ h ∈ AlternatingSix.ShadowLocal.natural) :
    coverResidualIn K ≠ one L T V₁ := by
  intro he
  have hH := c.component.local_overgroup
  let d := (centralPreimageQuotientEquiv (pCore 2 K)).trans eZ
  have ht : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype (le_sup_right.trans hH.1.2),map_subgroupOf_eq_of_le (le_sup_right.trans hH.1.2)⟩
  have hproper : H ⊓ M < H := lt_of_le_of_ne inf_le_left
    (fun hh => hH.2.2 (hh.ge.trans inf_le_right))
  have hspan := solvableOvergroupSpan_le_overlap H K (one L T V₁) T G₁ M hH.2.1 he
    (SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339)
  obtain ⟨t,htbad⟩ := six_source_diagram_actor H K T (H ⊓ M) (component_le c)
    (source_product_of_residual_eq_one c he) ht d hproper hspan
  apply htbad
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hh := hn (QuotientGroup.mk' (pCore 2 H) ⟨t,hTH t.property⟩)
  rwa [sourceAction_eq_centralModelAction] at hh

private noncomputable def centralSixEquiv
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple) :
    ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* AlternatingSix.ShadowLocal.A6 :=
  (QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)).trans
    Hexacode.even_quotient_center_equiv

variable [IsElementaryAbelian 2 (Source.UH H V₃)] [(K.subgroupOf H).Normal]

/-- Reducibility of the actual source module forces the proper plus residual. -/
theorem source_six_cover_residual_of_proper_section
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (W : Subrepresentation act.representation) (hb : W ≠ ⊥) (ht : W ≠ ⊤) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      coverResidualIn K = plus L T V₁ ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,coverResidualIn K⁆ := by
  have hn := source_six_cover_residual_ne_one_of_natural c (centralSixEquiv e)
    (source_six_cover_natural_of_proper_section c e act W hb ht (centralSixEquiv e))
  exact source_proper_residual_generates c
    ((Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card) hn

/-- With the homogeneous alternatives, native recognition forces the proper residual. -/
theorem source_six_cover_residual_of_alternatives
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (P : Sylow 2 (Source.Hstar H))
    (hP : (P : Subgroup (Source.Hstar H)) = Source.starImage H (T : Subgroup G))
    (src : Recognition.Alternatives act.representation (Source.starImage H K) P
      (star_sylow_generation H K (T : Subgroup G) (source_six_cover_consequences c e).2.1 P hP)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      coverResidualIn K = plus L T V₁ ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,coverResidualIn K⁆ := by
  have hn := source_six_cover_residual_ne_one_of_natural c (centralSixEquiv e)
    (source_six_cover_natural_of_alternatives c e act P hP src (centralSixEquiv e))
  exact source_proper_residual_generates c
    ((Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card) hn
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
