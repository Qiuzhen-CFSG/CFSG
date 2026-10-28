module
public import Theory.Representation.InvertedCubicTensor.QuadraticOffenders
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.LinearTwo

/-!
# The original faithful FF multiplicity action

The commuting symmetric-three action doubles the dimension of its inverter-fixed
multiplicity space. Faithfulness of the nontrivial perfect component forces the
whole dimension above four. A source quadratic actor moving the normal cubic
would have rank one and fixed codimension equal to half that dimension, which
contradicts its quadratic bound. It therefore centralizes the cubic; the
common-centralizer calculation makes it commute with the marked symmetric-three
group. On the generated component-and-actor subgroup, the actual multiplicity
representation is faithful and halves fixed codimension, producing an offender.

The generated subgroup has the original component as its entire generalized
Fitting subgroup and inherits SQTK. This constructs the FF input from original
source assumptions, with no universal F.9.18 contract or equality W=U.
The remaining constituent recognition and field exclusions stay with
qt-d-138-fields-source; qt-d-1381-source supplies the preceding source context.
Source: Aschbacher–Smith, F.9.18 and 13.8.20(a), printed pp.325–326,954.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections CriticalGeometry.Reorientation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The original quadratic actor gives a faithful FF action on the literal
inverter-fixed multiplicity, with its component and generated actor retained. -/
theorem source_external_ff_multiplicity
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (X : Subgroup G) (ha : ExternalXAlternative H K X)
    (hx : ExternalSourceData H K X) (hseed : V₃ = ⁅V₃,X⁆) :
    ∃ s : S₃ →* Source.Hstar H,
      Function.Injective s ∧
      (alternatingGroup (Fin 3)).map s = Source.starImage H X ∧
      (∀ v, act.representation (s cubic) v = v → v = 0) ∧
      ∃ A : Subgroup (Source.Hstar H), QuadraticMember act.representation A ∧
        let E := Source.starImage H K ⊔ A
        ∃ hs : ∀ (g : E) t, Commute (g : Source.Hstar H) (s t),
          ∃ μ : Representation (ZMod 2) E (multiplicitySpace (act.representation.comp s)),
          μ = multiplicity (act.representation.comp s) (act.representation.comp E.subtype)
            (ambient_commute act.representation E.subtype s hs) ∧
          Function.Injective μ ∧ IsOffender μ (A.subgroupOf E) ∧
          generalizedFitting E = (Source.starImage H K).subgroupOf E ∧
          IsSQTK KnownSimple.IsKnownSimple E := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Ks.Normal := c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let : Xs.Normal := hx.2.2.1
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  let : IsSimpleGroup (Ks ⧸ center Ks) := IsQuasisimple.simple
  let : Nontrivial Ks := (QuotientGroup.mk'_surjective (center Ks)).nontrivial
  have hF9 := c.f9 H c.component.local_overgroup
  have hf := f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  have hcommon := source_external_common_centralizer c X hx
  obtain ⟨s,hsi,hsc,hm,hgen,hfree,_⟩ := source_external_cubic_action act X ha hx hseed
  have hks : ∀ (k : Ks) g, Commute (k : Source.Hstar H) (s g) := by
    intro k g
    exact hsc ⟨g,rfl⟩ k k.property
  have hd : 4 < Module.finrank (ZMod 2) (SeedAction.Space H V₃ V₁) :=
    four_lt_finrank_of_perfect (act.representation.comp s)
      (act.representation.comp Ks.subtype)
      (ambient_commute act.representation Ks.subtype s hks) hfree
      (hf.comp Ks.subtype_injective)
  obtain ⟨A,hq,_⟩ := source_quotient_faithful_quadratic_actor c act
  have hAX : A ≤ centralizer (Xs : Set (Source.Hstar H)) := by
    by_contra hn
    obtain ⟨hr,hhalf⟩ := normalThree_quadratic_rank_fixedCodim act.representation hf Xs
      inferInstance hx.1 hgen A hq.1 hq.2.1 hn
    change 2 * fixedCodim act.representation A =
      Module.finrank (ZMod 2) (SeedAction.Space H V₃ V₁) at hhalf
    have hb := hq.2.2
    omega
  have hAC : A ≤ centralizer (s.range : Set (Source.Hstar H)) :=
    (elementary_centralizes_component_centralizer Ks Xs A hx.1 hcommon hq.1.2 hAX).trans
      (centralizer_le hsc)
  have hKC : Ks ≤ centralizer (s.range : Set (Source.Hstar H)) := by
    intro k hk t ht
    obtain ⟨g,rfl⟩ := ht
    exact (hks ⟨k,hk⟩ g).symm.eq
  let E := Ks ⊔ A
  have hs : ∀ (g : E) t, Commute (g : Source.Hstar H) (s t) := by
    intro g t
    exact ((sup_le hKC hAC) g.property (s t) ⟨t,rfl⟩).symm
  let μ := multiplicity (act.representation.comp s) (act.representation.comp E.subtype)
    (ambient_commute act.representation E.subtype s hs)
  have hAE : IsElementaryTwo (A.subgroupOf E) := by
    let := hq.1.2
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ E from le_sup_right)⟩
    intro he
    exact hq.1.1 (by rw [←map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right),he,Subgroup.map_bot])
  have hb : fixedCodim (act.representation.comp E.subtype) (A.subgroupOf E) ≤
      2 * rank (A.subgroupOf E) := by
    rw [fixedCodim_subgroupOf act.representation (show A ≤ E from le_sup_right),
      rank_subgroupOf (show A ≤ E from le_sup_right)]
    exact hq.2.2
  have hKX : Ks ≤ centralizer (Xs : Set (Source.Hstar H)) := by
    intro k hk x hx'
    change x ∈ Source.starImage H X at hx'
    rw [←hm] at hx'
    obtain ⟨g,_,rfl⟩ := hx'
    exact (hks ⟨k,hk⟩ g).symm.eq
  refine ⟨s,hsi,hm,hfree,A,hq,hs,μ,rfl,?_,?_,?_,?_⟩
  · exact multiplicity_injective (act.representation.comp s)
      (act.representation.comp E.subtype) _ hfree (hf.comp E.subtype_injective)
  · exact offender_multiplicity (act.representation.comp s)
      (act.representation.comp E.subtype) _ hfree _ hAE hb
  · exact LinearTwo.NoStrongMoved.generated_fitting Ks Xs hx.1 hcommon hKX hq.1 hAX
  · exact (Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
      (source_sqtk c) (pCore 2 H) pCore_isPGroup).subgroup E
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
