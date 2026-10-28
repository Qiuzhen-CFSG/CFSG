module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.SpecialLinearFourGraph
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.LinearTwo
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF.NativeSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NativeRecognition
public import Theory.Representation.GoldschmidtONan.Basic
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CoveredSeed

/-!
# The original SL₃(4) scalar action and module saturation

The original Borel and inverter identify L₁,+* with the scalar center of K*.
Relative normality lifts through the two-core, and the covered seed satisfies
[V₃,L₁,+]=V₃. Its full H-orbit therefore has no scalar-fixed vectors. This
argument keeps the order-three center of the full SL₃(4) carrier.

Native B.5.1 and the actual graph action exclude FF modules. Applying the two
strict no-FF inequalities to an invariant submodule and its quotient proves
saturation at the original quadratic actor's ratio-two bound. The separately
proved U_H=[U_H,K] identifies this moved space with the full source module;
the scalar cubic then makes every invariant submodule component-moved, proving
irreducibility for the whole action. In particular the full H-orbit of every
Irr⁺ constituent is the literal U_H/V₁.

Native B.4.5 now recognizes any H-invariant Irr⁺ member. The original graph
relation survives the resulting change of marking and excludes that invariant
case. SpecialLinearFourConstituent constructs a natural member and its disjoint
graph translate. Their spanning equality and the terminal critical geometry
are still required to exclude SL₃(4). The genuine earlier-source
premises remain in SourceContext and with the original assembly owners.
Source: Aschbacher–Smith, 13.8.20, printed p.955, using B.5.1 and F.9.18(7).
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
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem specialLinearThree_quotient_two
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : Source.starImage H K ≃* SL) [(Source.starImage H K).Normal] :
    IsPGroup 2 (Source.Hstar H ⧸ Source.starImage H K) := by
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans c.component.local_overgroup.1.2
  have hgen := (source_specialLinearThree_reduction c eK).2.1
  have hs : Source.starImage H K ⊔ Source.starImage H (T : Subgroup G) = ⊤ := by
    unfold Source.starImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hKH hTH,←hgen]
    simp [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact quotient_isPGroup_of_sup_eq_top (Source.starImage H (T : Subgroup G))
    (Source.starImage H K) (T.isPGroup'.comap_subtype.map _) ((sup_comm _ _).trans hs)

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The scalar center moves the original seed and hence the full literal module.
Its nonidentity generator has no fixed vector, retaining the covering center. -/
theorem source_specialLinearThree_scalar_fixedFree
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) (eK : Source.starImage H K ≃* SL) :
    ∃ x : Source.Hstar H, x ∈ (center (Source.starImage H K)).map
      (Source.starImage H K).subtype ∧ ∀ v, act.representation x v = v → v = 0 := by
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e,t,_,g,_,_,hX,_⟩ := source_specialLinearThree_graph c eK
  let X := plus L T V₁
  let Z := Source.starImage H X
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hXH : X ≤ H := ((plus_le_one L T V₁ c.localSetup.line_stable).trans
    (source_specialLinearThree_containment c eK)).trans hKH
  have hQ : Source.QH H ≤ normalizer (X : Set G) :=
    (c.f9 H c.component.local_overgroup).QH_le_T.trans
      (T_normalizes_plus L T V₁ c.localSetup.normalizes_L c.localSetup.line_stable)
  have hn := normalizes_of_central_starImage H K X hXH (plus_isPPerfect L T V₁) hQ hX
  let : (X.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hXH).mpr hn
  have hg : subspaceCommutator act.representation ⊤ Z = ⊤ :=
    ExternalModules.Structure.source_commutator_generation H X V₃ V₁ hXH
      act.representation act.conjugation
      (Section07.ModelExclusions.seed_commutator_plus (localNaturalSetup c.localSetup) ⟨e⟩).symm
  have hZ : Nat.card Z = 3 := by
    rw [show Z = (center (Source.starImage H K)).map (Source.starImage H K).subtype from hX,
      Nat.card_congr (equivMapOfInjective (center (Source.starImage H K))
        (Source.starImage H K).subtype (Source.starImage H K).subtype_injective).symm.toEquiv,
      Nat.card_congr (centerCongr eK).toEquiv,Atlas.ExceptionalSupport.card_sl_center,
      Fintype.card_fin,Nat.card_eq_fintype_card,SL2FourNatural.card_field]
    decide
  have hc : IsCompl (fixedSpace act.representation Z)
      (subspaceCommutator act.representation ⊤ Z) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := act.representation)
        (Y := Z) (by rw [hZ]; decide))
  have hz : fixedSpace act.representation Z = ⊥ := by
    simpa only [hg,disjoint_top] using hc.disjoint
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 (by rw [hZ])
  have hxne : x ≠ 1 := by intro he; simp [he] at hx
  have hgen : zpowers (x : Source.Hstar H) = Z := by
    have hh := congrArg (Subgroup.map Z.subtype) (zpowers_eq_top_of_prime_card hZ hxne)
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,Subgroup.coe_subtype] using hh
  refine ⟨x,hX ▸ x.property,?_⟩
  intro v hv
  have hvZ : v ∈ fixedSpace act.representation Z := by
    rw [←hgen,mem_fixedSpace_zpowers_iff]
    exact hv
  exact (Submodule.mem_bot (ZMod 2)).mp (hz ▸ hvZ)

/-- Native B.5.1 excludes FF modules for the actual original graph action. -/
theorem source_specialLinearThree_not_ff
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) (eK : Source.starImage H K ≃* SL) :
    ¬ IsFFModule act.representation := by
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
  obtain ⟨_,t,_,g,_,ht,_,_⟩ := source_specialLinearThree_graph c eK
  exact NoFF.Native.not_ff act.representation (hsq.subgroup Ks) eK
    (specialLinearThree_quotient_two c eK) (pCore_quotient_pCore_eq_bot 2) hf _ g ht

/-- Every nonzero invariant component-moved submodule is the full literal
source module. No recognition, central-quotient saturation or FF premise remains. -/
theorem source_specialLinearThree_saturation
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) (eK : Source.starImage H K ≃* SL)
    (W : Subrepresentation act.representation) (hW : W.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator act.representation W.toSubmodule (Source.starImage H K) =
      W.toSubmodule) : W.toSubmodule = ⊤ := by
  let Ks := Source.starImage H K
  let : Ks.Normal := c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  obtain ⟨_,t,_,g,_,ht,_,_⟩ := source_specialLinearThree_graph c eK
  obtain ⟨x,hx,hfree⟩ := source_specialLinearThree_scalar_fixedFree c act eK
  obtain ⟨A,hA,_⟩ := source_quotient_faithful_quadratic_actor c act
  have he := NoFF.Native.moved_space act.representation (hsq.subgroup Ks) eK
    (specialLinearThree_quotient_two c eK) (pCore_quotient_pCore_eq_bot 2) _ g ht x hx hfree
    W hW hfull A hA.1 hA.2.2
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let d : LiteralAction H V₃ V₁ := ⟨act.representation,act.conjugation⟩
  exact he.trans (d.commutator_eq_top K hKH (source_specialLinearThree_reduction c eK).2.2)

/-- The central cubic makes every invariant submodule component-moved;
saturation therefore proves irreducibility for the whole original actor. -/
theorem source_specialLinearThree_irreducible
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) (eK : Source.starImage H K ≃* SL) :
    IsIrreducible act.representation := by
  have hdim := source_quotient_dimension_gt_two c act
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨x,hx,hfree⟩ := source_specialLinearThree_scalar_fixedFree c act eK
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun W => ?_⟩
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply source_specialLinearThree_saturation c act eK W hW
    have hKW : subspaceCommutator W.toRepresentation ⊤ (Source.starImage H K) = ⊤ :=
      ExternalModules.FFSections.LinearTwo.NoStrongMoved.full_of_fixedFree
        (Source.starImage H K) W.toRepresentation x ((map_subtype_le _) hx)
        (fun v hv => Subtype.ext (hfree v (congrArg Subtype.val hv)))
    have he := subspaceCommutator_map_embedding act.representation W.toRepresentation
      (MonoidHom.id (Source.Hstar H)) W.toSubmodule.subtype (fun _ _ => rfl)
      (Source.starImage H K) ⊤
    simpa only [hKW,Submodule.map_top,Submodule.range_subtype,Subgroup.map_id] using he

/-- Apply saturation to the actual full H-orbit of any Irr⁺ constituent,
preserving its inclusion in U_H/V₁. -/
theorem source_specialLinearThree_orbit_eq_top
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) (eK : Source.starImage H K ≃* SL)
    (I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)))
    (hI : IsIrrPlus act.representation (Source.starImage H K) I) :
    Homogeneous.orbitSpan act.representation ⊤ I = ⊤ := by
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let W : Subrepresentation act.representation :=
    ⟨Homogeneous.orbitSpan act.representation ⊤ I,
      fun g _ hv => (Homogeneous.orbitSpan_invariant act.representation ⊤ I (mem_top g) _).2 hv⟩
  exact source_specialLinearThree_saturation c act eK W
    (Homogeneous.orbitSpan_ne_bot _ hI)
    (Homogeneous.orbitSpan_full_commutator _ (by rw [normalizer_eq_top]) hI)

/-- Native B.4.5 on the actual faithful image recognizes an invariant Irr⁺
section as natural. The original graph actor contradicts its invariance. -/
theorem source_specialLinearThree_no_invariant_constituent
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) (eK : Source.starImage H K ≃* SL)
    (I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)))
    (hI : IsIrrPlus act.representation (Source.starImage H K) I) :
    ¬ (⊤ : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer act.representation I := by
  intro hstable
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  obtain ⟨A,hA,hAC⟩ := source_quotient_faithful_quadratic_actor c act
  obtain ⟨e,⟨n⟩⟩ := NaturalRecognition.Native.invariant_natural_section act.representation
    (Source.starImage H K) eK hsq (specialLinearThree_quotient_two c eK)
    I hI hstable A hA.1 hA.2.1 hA.2.2 (disjoint_iff.mpr hAC)
  obtain ⟨_,t,_,g,_,ht,_,_⟩ := source_specialLinearThree_graph c eK
  obtain ⟨g',ht'⟩ := Matrix.PSL3Even.GraphRemarking.graph_relation_trans
    (Source.starImage H K).subtype eK (eK.symm.trans e) _ g ht
  have he : eK.trans (eK.symm.trans e) = e := by
    apply MulEquiv.ext
    intro k
    change e (eK.symm (eK k)) = e k
    rw [eK.symm_apply_apply]
  rw [he] at ht'
  let d : LiteralAction H V₃ V₁ := ⟨act.representation,act.conjugation⟩
  have hm := natural_section_moved d K e _ I hI n g' ht'
  exact hm ((subspace_map_eq_iff act.representation I _).mpr (hstable (mem_top _)))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
