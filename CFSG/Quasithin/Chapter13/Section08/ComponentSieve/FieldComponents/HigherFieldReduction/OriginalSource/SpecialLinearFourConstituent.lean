module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.SpecialLinearFourModule
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NativeSelection

/-!
# The original natural constituent and its disjoint graph translate

The source edge actor lies in the original T*. Its faithful quadratic action
and the fixed-free scalar center construct a T*-homogeneous natural Irr⁺
constituent inside the literal U_H/V₁. The proved saturation and H=KT show
that both its H* and T* orbits span that whole module.

The original covered inverter is retained. Changing to the natural marking
changes only the GL₃ correction in its graph relation. Natural–dual
inequivalence moves the chosen constituent, and whole-action irreducibility
makes the translate disjoint from it. No natural constituent, module model,
classification callback or orbit equality is assumed.

It remains to prove that these two summands exhaust the full orbit and then
apply the critical-subspace obstruction. This module does not assert the
terminal SL₃(4) exclusion or completion of 13.8.20.
Source: Aschbacher–Smith, 13.8.20, printed p.955, using F.9.18(3–4,7),
B.4.5 and the original marked Borel/inverter.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.SL3FourNaturalDual
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExceptionalFields.LinearThreeFour.AutomorphismModule
open ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
open LocalBorel.CentralizingCalculation
open SolvableExclusion.Three.Supercritical.Offenders CriticalGeometry.Reorientation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private theorem source_sylow_quadratic_actor
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) :
    ∃ A : Subgroup (Source.Hstar H), A ≤ Source.starImage H (T : Subgroup G) ∧ QuadraticMember act.representation A ∧
      A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ := by
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hgen : K ⊔ ((L ⊔ (T : Subgroup G)) ⊓ H) = H := by
    rw [Comparison.local_edge c.localSetup (c.f9 H c.component.local_overgroup),←sup_assoc]
    exact c.component.generated
  obtain ⟨a,B,_,hBT,hq,hfaith⟩ := F918.exists_faithful_edge_actor c.localSetup
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
  exact ⟨Source.starImage H B,SourceMarking.starImage_mono H hBT,he ▸ hq,hfaith⟩


/-- Construct the natural constituent, its whole original orbit, and its disjoint
translate by the original inverter, with all quotient and component maps literal. -/
theorem source_specialLinearThree_natural_constituent
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) (eK : Source.starImage H K ≃* SL) :
    ∃ (I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)))
      (_hI : Homogeneous.IsIrrPlusWith act.representation (Source.starImage H K)
        (Source.starImage H (T : Subgroup G)) I)
      (e : Source.starImage H K ≃* SL)
      (_n : NaturalCentralSection act.representation (Source.starImage H K) e I),
      Homogeneous.orbitSpan act.representation ⊤ I = ⊤ ∧
      Homogeneous.orbitSpan act.representation (Source.starImage H (T : Subgroup G)) I = ⊤ ∧
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
        InvertsTwoCoreQuotient (plus L T V₁) t.val ∧
        let tstar := QuotientGroup.mk' (pCore 2 H)
          ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩
        ∃ g : Matrix.GeneralLinearGroup (Fin 3) F,
          (∀ k, sourceActor H K e k * tstar = tstar * sourceActor H K e
            (Matrix.PSL3.OuterSolvable.linearConjSL F g
              (Matrix.SpecialLinearGroup.inverseTranspose k))) ∧
          Disjoint I (I.map (act.representation tstar)) := by
  let Ks := Source.starImage H K
  let : Ks.Normal := c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  have hF9 := c.f9 H c.component.local_overgroup
  have hf := f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  obtain ⟨x,hx,hfree⟩ := source_specialLinearThree_scalar_fixedFree c act eK
  obtain ⟨A,hAT,hA,hAC⟩ := source_sylow_quadratic_actor c act
  obtain ⟨I,hI,_,e,⟨n⟩⟩ := NaturalRecognition.Native.quadratic_natural_constituent
    act.representation Ks eK hsq hf x hx hfree A (Source.starImage H (T : Subgroup G))
      (T.isPGroup'.comap_subtype.map _) hAT hA.1 hA.2.1 hA.2.2 hAC
  have hfull := source_specialLinearThree_orbit_eq_top c act eK I hI.isIrrPlus
  have hgen : Ks ⊔ Source.starImage H (T : Subgroup G) = ⊤ := by
    have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
    have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans c.component.local_overgroup.1.2
    change Source.starImage H K ⊔ Source.starImage H (T : Subgroup G) = ⊤
    unfold Source.starImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hKH hTH,
      ←(source_specialLinearThree_reduction c eK).2.1]
    simp [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hfullT : Homogeneous.orbitSpan act.representation
      (Source.starImage H (T : Subgroup G)) I = ⊤ := by
    apply top_unique
    rw [←hfull]
    apply Homogeneous.orbitSpan_le _ (Homogeneous.le_orbitSpan _ _ _)
    rw [←hgen]
    exact sup_le (Homogeneous.orbitSpan_component_invariant _ hI.normalizes hI.isIrrPlus)
      (Homogeneous.orbitSpan_invariant _ _ _)
  obtain ⟨_,t,hinv,g,_,ht,_,_⟩ := source_specialLinearThree_graph c eK
  obtain ⟨g',ht'⟩ := Matrix.PSL3Even.GraphRemarking.graph_relation_trans
    Ks.subtype eK (eK.symm.trans e) _ g ht
  have he : eK.trans (eK.symm.trans e) = e := by
    apply MulEquiv.ext
    intro k
    change e (eK.symm (eK k)) = e k
    rw [eK.symm_apply_apply]
  rw [he] at ht'
  let d : LiteralAction H V₃ V₁ := ⟨act.representation,act.conjugation⟩
  have hm := natural_section_moved d K e _ I hI.isIrrPlus n g' ht'
  refine ⟨I,hI,e,n,hfull,hfullT,t,hinv,g',ht',?_⟩
  exact ((hI.isIrrPlus.eq_or_disjoint_conjugate_of_normal_restriction act.representation
    (source_specialLinearThree_irreducible c act eK) Ks _).resolve_left hm).symm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
