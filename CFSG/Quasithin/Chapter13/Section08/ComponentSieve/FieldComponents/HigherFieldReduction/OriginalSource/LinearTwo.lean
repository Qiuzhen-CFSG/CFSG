module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Critical
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NativeMoved
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Faithful

/-!
# The original external PSL₂ moved space

The original residual alternatives bound the Fitting subgroup by order three;
the external normal cubic is therefore exactly that subgroup. The solvable
local supplement makes the component centralizer solvable, yielding the
common-centralizer bound that makes noncentral sections faithful.

F.9.18 supplies a quadratic actor faithful on the component. Both quotient
actions are compared through their literal conjugation formulas. Applying
the native B.4.2 and B.1.5(3) proofs then excludes strong FF-modules on every
noncentral invariant section and identifies every actual H-orbit of an Irr⁺
constituent with [U_H/V₁,K*]. No equality with the whole ambient module is
asserted. The remaining natural/five recognition and terminal contradiction
stay with qt-d-138-fields-source; preceding source inputs retain their
producers through qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.14, F.9.18(2,6), and 13.8.20(a), pp.951,325–326,954.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections
open SolvableExclusion.Three.Supercritical.Offenders CriticalGeometry.Reorientation
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u w
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The original Fitting alternatives identify the external normal cubic
with the whole Fitting subgroup of the literal quotient. -/
theorem source_external_fitting
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (X : Subgroup G) (hs : ExternalSourceData H K X) :
    fittingSubgroup (Source.Hstar H) = Source.starImage H X := by
  let Xs := Source.starImage H X
  let : Xs.Normal := hs.2.2.1
  have hp : IsPGroup 3 Xs := IsPGroup.of_card (n := 1) (by simpa using hs.1)
  have hx : Xs ≤ fittingSubgroup (Source.Hstar H) := le_sSup ⟨inferInstance,hp.isNilpotent⟩
  have hwhole := LocalFitting.whole_residual c.localSetup c.component.local_overgroup
    c.earlier1339 (SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339)
  have hc := Components.Fitting.fitting_star_trivial_or_card_three H L
    (one L T V₁) (plus L T V₁) hwhole (LocalFitting.ordinary_core_card c.localSetup)
    (fun h => LocalFitting.covered_core_card c.localSetup
      ⟨local_quotient_quasisimple c.localSetup,h.2⟩)
  rcases hc with hc | hc
  · have he : Xs = ⊥ := bot_unique (hx.trans_eq hc)
    have hh := hs.1
    change Nat.card Xs = 3 at hh
    rw [he,card_bot] at hh
    omega
  · exact (eq_of_le_of_card_ge hx (by rw [hc]; exact hs.1.ge)).symm

/-- The original solvable supplement and external cubic identify the common
centralizer bound used by the faithful section argument. -/
theorem source_external_common_centralizer
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (X : Subgroup G) (hs : ExternalSourceData H K X) :
    centralizer (Source.starImage H K : Set (Source.Hstar H)) ⊓
      centralizer (Source.starImage H X : Set (Source.Hstar H)) ≤ Source.starImage H X := by
  let Ks := Source.starImage H K
  let : Ks.Normal := c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hPH := c.component.local_overgroup.1.2
  let P := Source.starImage H (one L T V₁ ⊔ (T : Subgroup G))
  let : Group.IsSolvable (one L T V₁ ⊔ (T : Subgroup G) : Subgroup G) :=
    LocalFitting.local_solvable c.localSetup
  let : Group.IsSolvable P := by
    let : Group.IsSolvable ((one L T V₁ ⊔ (T : Subgroup G)).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hPH).toMonoidHom) (subgroupOfEquivOfLe hPH).injective
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)
  have hgen : Ks ⊔ P = ⊤ := by
    change Source.starImage H K ⊔ Source.starImage H (one L T V₁ ⊔ (T : Subgroup G)) = ⊤
    unfold Source.starImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hKH hPH,←sup_assoc,c.component.generated]
    simp [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let q := QuotientGroup.mk' Ks
  have hmap : P.map q = ⊤ := by
    have he := congrArg (map q) hgen
    simpa only [q,Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using he
  have hq : Function.Surjective (q.comp P.subtype) := by
    intro y
    have hy : y ∈ P.map q := by rw [hmap]; trivial
    obtain ⟨p,hp,he⟩ := hy
    exact ⟨⟨p,hp⟩,he⟩
  let : Group.IsSolvable (Source.Hstar H ⧸ Ks) := Group.isSolvable_of_surjective hq
  exact LinearTwo.NoStrongMoved.common_centralizer_le Ks (Source.starImage H X)
    (centralizer_solvable_of_centerless_quotient Ks hs.2.2.2.2.1)
    (source_external_fitting c X hs).le

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- F.9.18 supplies its faithful quadratic actor on the same original
representation used in the field argument. -/
theorem source_quotient_faithful_quadratic_actor
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) :
    ∃ A : Subgroup (Source.Hstar H), QuadraticMember act.representation A ∧
      A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ := by
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hgen : K ⊔ ((L ⊔ (T : Subgroup G)) ⊓ H) = H := by
    rw [Comparison.local_edge c.localSetup (c.f9 H c.component.local_overgroup),←sup_assoc]
    exact c.component.generated
  obtain ⟨a,B,_,_,hq,hfaith⟩ := F918.exists_faithful_edge_actor c.localSetup
    (c.f9 H c.component.local_overgroup) K hgen
    ((normal_subgroupOf_iff_le_normalizer hKH).mp c.component.normal)
  have he : linearAction a = act.representation := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
    change Additive.ofMul (a.action (QuotientGroup.mk' (pCore 2 H) h)
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) v)) =
        act.representation (QuotientGroup.mk' (pCore 2 H) h)
          (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) v))
    rw [a.conjugation,act.conjugation]
    rfl
  exact ⟨Source.starImage H B,he ▸ hq,hfaith⟩

/-- The original external PSL₂ branch has no strong FF-module, and every
noncentral invariant section is faithful and has no strong FF image. -/
theorem source_external_linearTwo_sections
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (X : Subgroup G) (ha : ExternalXAlternative H K X)
    (hs : ExternalSourceData H K X) (hseed : V₃ = ⁅V₃,X⁆)
    {F : Type w} [Field F] [Finite F] [CharP F 2]
    (e : Source.starImage H K ≃* PSL(2,F)) :
    ¬ IsStrongFFModule act.representation ∧
      ∀ (C W : Subrepresentation act.representation) (E : Subgroup (Source.Hstar H)),
        (¬ ∀ k ∈ Source.starImage H K, ∀ v,
          sectionRepresentation act.representation C W k v = v) →
        Function.Injective (sectionRepresentation act.representation C W) ∧
          ¬ IsStrongFFModule (imageRepresentation
            ((sectionRepresentation act.representation C W).comp E.subtype)) := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Ks.Normal := c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let : Xs.Normal := hs.2.2.1
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  have hc := source_external_common_centralizer c X hs
  have hF9 := c.f9 H c.component.local_overgroup
  have hf := f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  obtain ⟨s,_,hcomm,hm,hg,_,_⟩ := source_external_cubic_action act X ha hs hseed
  exact ⟨LinearTwo.NativeSource.no_strong_cubic Ks Xs e hsq hs.1 hc act.representation hf hg,
    fun C W E hn => LinearTwo.NativeSource.section_faithful_no_strong Ks Xs e hsq hs.1 hc
      act.representation s hm hg C W E hn⟩

/-- Every actual H-orbit of an Irr⁺ constituent is exactly the component
moved space in the original external PSL₂ branch. The quadratic actor,
section faithfulness and both classification premises are discharged. -/
theorem source_external_linearTwo_moved
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (X : Subgroup G) (ha : ExternalXAlternative H K X)
    (hs : ExternalSourceData H K X) (hseed : V₃ = ⁅V₃,X⁆)
    {F : Type w} [Field F] [Finite F] [CharP F 2]
    (e : Source.starImage H K ≃* PSL(2,F))
    (I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)))
    (hI : IsIrrPlus act.representation (Source.starImage H K) I)
    (W : Subrepresentation act.representation) (hW : W.toSubmodule = orbitSpan act.representation ⊤ I) :
    W.toSubmodule = subspaceCommutator act.representation ⊤ (Source.starImage H K) := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Ks.Normal := c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let : Xs.Normal := hs.2.2.1
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  obtain ⟨s,_,hcomm,hm,hg,_,_⟩ := source_external_cubic_action act X ha hs hseed
  obtain ⟨A,hA,hfaith⟩ := source_quotient_faithful_quadratic_actor c act
  apply LinearTwo.NativeSource.moved_space Ks Xs e hsq hs.1
    (source_external_common_centralizer c X hs) act.representation s
    (fun k g => hcomm ⟨g,rfl⟩ k k.property) hm hg W
  · rw [hW]
    exact orbitSpan_ne_bot _ hI
  · rw [hW]
    exact orbitSpan_full_commutator _ (by rw [normalizer_eq_top]) hI
  · exact hA.1
  · exact hA.2.2
  · exact hfaith
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
