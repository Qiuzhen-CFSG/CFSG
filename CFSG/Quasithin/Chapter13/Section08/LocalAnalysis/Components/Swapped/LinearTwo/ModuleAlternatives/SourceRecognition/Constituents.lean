module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.ComponentFixed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Applications
public import Theory.Representation.CliffordRestriction
public import Theory.Representation.BinaryOffender.SemisimpleIrrPlus
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit
public import Theory.Representation.BinaryOffender.SmallRatioTransport

/-!
# Faithful constituents stabilized by the original quadratic actor

Zero fixed spaces for both components make every nonzero invariant subspace
faithful for their product. Clifford semisimplicity then supplies an actual
irreducible constituent. Homogeneous selection and the quadratic orbit bound
show that the elementary actor stabilizes this constituent: a moved constituent
would have dimension at most two, contrary to perfectness.

The source applications construct the F.9 edge actor, transport its action to
the literal maximal quotient, and retain its placement, quadraticity and
codimension bound. The selected quotient retains the proved consumer taking
orthogonal recognition to the original whole-module alternative. Recognition
of the constituent and quotient remains a separate mathematical obligation.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953, using F.9.18;
the quadratic homogeneous-orbit argument is D.3.5, printed pp.195–196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.NoStrong

/-- With both component fixed spaces zero, every nonzero orbit-invariant
subspace is faithful for the literal component product. -/
theorem faithful_on_component_invariant
    {D F U : Type*} [Group D] [Finite D] [Field F] [Finite F] [CharP F 2]
    (a : ExchangedActor KnownSimple.IsKnownSimple D F 2)
    [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) D U)
    (ha : fixedSpace σ a.component = ⊥) (hb : fixedSpace σ a.second = ⊥)
    (I : Submodule (ZMod 2) U) (hne : I ≠ ⊥)
    (hi : a.orbit ≤ subspaceStabilizer σ I) :
    Function.Injective (invariantSubspace σ a.orbit I hi).toRepresentation := by
  let τ := (invariantSubspace σ a.orbit I hi).toRepresentation
  let A := a.component.subgroupOf a.orbit
  let B := a.second.subgroupOf a.orbit
  have hA := a.component_isComponent.subgroupOf a.component_le
  have hB := a.second_isComponent.subgroupOf a.second_le
  have hn (C : Subgroup D) (hC : C ≤ a.orbit) (hc : fixedSpace σ C = ⊥) :
      ¬ C.subgroupOf a.orbit ≤ τ.ker := by
    intro hk
    apply hne
    apply bot_unique
    intro v hv
    apply hc.le
    intro c
    have hmem : (⟨c,hC c.property⟩ : a.orbit) ∈ τ.ker := hk c.property
    have he := LinearMap.congr_fun hmem (⟨v,hv⟩ : I)
    exact congrArg Subtype.val he
  have hac := (hA.normal_dichotomy τ.ker).resolve_left (hn a.component a.component_le ha)
  have hbc := (hB.normal_dichotomy τ.ker).resolve_left (hn a.second a.second_le hb)
  have hjoin : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup a.component_le a.second_le,
      IrreducibleReduction.components_sup a,subgroupOf_self]
  have hcent : (⊤ : Subgroup a.orbit) ≤ centralizer (τ.ker : Set a.orbit) := by
    rw [← hjoin]
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hac)
      (commutator_eq_bot_iff_le_centralizer.mp hbc)
  have hz := center_eq_bot_of_product_equiv a.orbit a.productEquiv
  apply τ.ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  apply hz.le
  exact mem_center_iff.mpr (fun y => (hcent (mem_top y) x hx).symm)

/-- A quadratic actor of ratio at most two stabilizes a faithful irreducible
constituent for the exchanged component orbit. -/
theorem exists_quadratic_faithful_constituent
    {D F U : Type*} [Group D] [Finite D] [Field F] [Finite F] [CharP F 2]
    (a : ExchangedActor KnownSimple.IsKnownSimple D F 2)
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) D U) [σ.IsIrreducible]
    (ha : fixedSpace σ a.component = ⊥) (hb : fixedSpace σ a.second = ⊥)
    (B : Subgroup D) (hB : IsElementaryTwo B) (hq : IsQuadratic σ B)
    (hbound : fixedCodim σ B ≤ 2 * rank B) :
    ∃ I : Submodule (ZMod 2) U, ∃ hi : a.orbit ≤ subspaceStabilizer σ I,
      Homogeneous.IsIrrPlusWith σ a.orbit B I ∧
      IsIrreducible (invariantSubspace σ a.orbit I hi).toRepresentation ∧
      Function.Injective (invariantSubspace σ a.orbit I hi).toRepresentation ∧
      B ≤ subspaceStabilizer σ I := by
  let : a.orbit.Normal := a.orbit_normal
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial σ
  have hz : fixedSpace σ a.orbit = ⊥ := by
    apply bot_unique
    apply le_trans _ ha.le
    intro u hu c
    exact hu ⟨c,a.component_le c.property⟩
  have hn : ¬ (⊤ : Submodule (ZMod 2) U) ≤ fixedSpace σ a.orbit := by
    rw [hz]
    intro ht
    exact (top_ne_bot : (⊤ : Submodule (ZMod 2) U) ≠ ⊥) (le_antisymm ht bot_le)
  have hN : Group.IsPerfect a.orbit := by
    let : IsQuasisimple a.component := a.component_isComponent.2
    rw [a.orbit_eq]
    exact conjugateSpanBy_isPerfect _ _
  let := hN
  obtain ⟨J,hJ⟩ := exists_isIrrPlus_of_not_fixed σ a.orbit hn
  let : IsElementaryAbelian 2 B := hB.2
  obtain ⟨I,_,hI⟩ := Homogeneous.exists_isIrrPlusWith_le_orbitSpan σ
    (show B ≤ normalizer (a.orbit : Set D) from le_normalizer_of_normal)
    (IsElementaryAbelian.isPGroup 2 B) hJ
  have hf := faithful_on_component_invariant a σ ha hb I (hI.isIrrPlus.ne_bot σ) hI.invariant
  have hfN : ∀ k ∈ a.orbit, (∀ v ∈ I, σ k v = v) → k = 1 := by
    intro k hk hv
    have he : (⟨k,hk⟩ : a.orbit) = 1 := hf (by
      ext v
      change σ k v = σ 1 v
      simpa only [map_one,Module.End.one_apply] using hv v v.property)
    exact congrArg Subtype.val he
  have hfaith := actor_faithful_on_section σ a.orbit B I hI.invariant hfN
    hI.normalizes (by rw [a.centralizer_eq_bot,inf_bot_eq])
  have hs := hI.quadratic_stabilizes σ hz hB hq hfaith
    (hI.isIrrPlus.finrank_gt_two σ a.orbit) hbound
  let : IsSemisimpleModule (ZMod 2)[a.orbit] (Representation.asModule (σ.comp a.orbit.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple σ inferInstance a.orbit
  let : IsSemisimpleRepresentation (σ.comp a.orbit.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr inferInstance
  exact ⟨I,hI.invariant,hI,hI.isIrrPlus.irreducible_of_semisimple σ,hf,hs⟩

open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open SolvableExclusion Three.Supercritical.Offenders
open CriticalGeometry.Reorientation

private theorem source_representation_eq
    {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (a : Five.StarAction H (Source.UH H V₃) V₁) : ρ = linearAction a := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  have hv : v = Additive.ofMul (sourceProjection H V₃ V₁ u) := hu.symm
  rw [hv,hρ]
  exact congrArg Additive.ofMul (a.conjugation x u).symm

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving

/-- The actual F.9 actor descends to any proper irreducible source quotient
and stabilizes a faithful irreducible component-orbit constituent there. -/
theorem source_quotient_quadratic_constituent {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [hEA : IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G))
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    [W.quotientRepresentation.IsIrreducible] :
    ∃ B : Subgroup G, B ≤ ((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 ∧ B ≤ T ∧
      QuadraticMember W.quotientRepresentation (Source.starImage H B) ∧
      ∃ I : Submodule (ZMod 2) (SourceSpace H V₃ V₁ ⧸ W.toSubmodule),
      ∃ hi : Source.starImage H (conjugateSpanBy K (T : Subgroup G)) ≤
          subspaceStabilizer W.quotientRepresentation I,
        Homogeneous.IsIrrPlusWith W.quotientRepresentation
          (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))
          (Source.starImage H B) I ∧
        IsIrreducible (invariantSubspace W.quotientRepresentation _ I hi).toRepresentation ∧
        Function.Injective (invariantSubspace W.quotientRepresentation _ I hi).toRepresentation ∧
        Source.starImage H B ≤ subspaceStabilizer W.quotientRepresentation I := by
  obtain ⟨α,B,hB,hBT,hA,_⟩ := @F918.source_component_actor G _ _ T L V V₁ V₂ V₃ M G₁ H
    d hEA h hF9all hcentral hcomm hsource hH K hKH hK hgen
  rw [← source_representation_eq H V₃ V₁ ρ hρ α] at hA
  have hq : IsQuadratic W.quotientRepresentation (Source.starImage H B) :=
    quadratic_of_equivariant_surjection ρ W.quotientRepresentation
      W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective
      (fun g v => (W.quotientRepresentation_mk g v).symm) _ hA.2.1
  have hbound : fixedCodim W.quotientRepresentation (Source.starImage H B) ≤
      2 * rank (Source.starImage H B) := by
    have hh := fixedCodim_quotient_add_subrepresentation_le ρ W (Source.starImage H B)
    exact (Nat.le_add_right _ _).trans (hh.trans hA.2.2)
  refine ⟨B,hB,hBT,⟨hA.1,hq,hbound⟩,?_⟩
  obtain ⟨ha,hb⟩ := source_irreducible_quotient_component_fixed_eq_bot
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn W hW
  obtain ⟨F,hF,hfin,hchar,a,hfirst,hsecond,horbit,_⟩ := exists_source_exchangedActor
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
  rw [← hfirst] at ha
  rw [← hsecond] at hb
  rw [← horbit]
  exact exists_quadratic_faithful_constituent a W.quotientRepresentation ha hb
    (Source.starImage H B) hA.1 hq hbound

/-- The literal selected quotient, its faithful component-orbit constituent,
and the original whole-module recognition consumer. The actor and constituent
are constructed here; recognition of the quotient remains to be proved. -/
theorem exists_source_constituent_reduction {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧
      W.quotientRepresentation.IsIrreducible ∧
      Function.Injective W.quotientRepresentation ∧
      (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ ≠ ⊥ ∧
      (HasOrthogonalFourOrbit W.quotientRepresentation
          (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) →
        HasOrthogonalFourOrbit ρ
          (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))) ∧
      ∃ B : Subgroup G, B ≤ ((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 ∧ B ≤ T ∧
        QuadraticMember W.quotientRepresentation (Source.starImage H B) ∧
        ∃ I : Submodule (ZMod 2) (SourceSpace H V₃ V₁ ⧸ W.toSubmodule),
        ∃ hi : Source.starImage H (conjugateSpanBy K (T : Subgroup G)) ≤
            subspaceStabilizer W.quotientRepresentation I,
          Homogeneous.IsIrrPlusWith W.quotientRepresentation
            (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))
            (Source.starImage H B) I ∧
          IsIrreducible (invariantSubspace W.quotientRepresentation _ I hi).toRepresentation ∧
          Function.Injective (invariantSubspace W.quotientRepresentation _ I hi).toRepresentation ∧
          Source.starImage H B ≤ subspaceStabilizer W.quotientRepresentation I := by
  obtain ⟨W,hW,hirr,hfaith,hseed,hlift⟩ := exists_source_quotient_reduction
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn
  let := hirr
  refine ⟨W,hW,hirr,hfaith,hseed,fun hm => hlift (Or.inr hm),?_⟩
  exact source_quotient_quadratic_constituent
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn W hW

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
