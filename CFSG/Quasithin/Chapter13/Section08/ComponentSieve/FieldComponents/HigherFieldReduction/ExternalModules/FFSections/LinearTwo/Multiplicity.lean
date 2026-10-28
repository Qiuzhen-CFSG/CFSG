module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.MultiplicitySections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NativeMoved
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.Realization.Multiplicity

/-!
# The full moved constituent in a faithful PSL₂ FF action

Minimal-offender replacement gives an invariant Irr⁺ constituent and a
faithful FF central-section action. The native absence of strong PSL₂
modules forces equality in the fixed-codimension bound. The offender
therefore centralizes the quotient by the constituent; its commutator with
the component generates the component, so every component difference lies
in the constituent. Its central action retains the literal component map.
OriginalSource.LinearTwoComplete applies this to the constructed source
multiplicity action. Source: Aschbacher–Smith, B.1.5, B.1.11, B.4.2,
F.9.18 and 13.8.20(a), pp.69–73,86,325–326,954.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo
open CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u v w
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- For a faithful FF action with generalized Fitting subgroup PSL₂ in
characteristic two, every constituent stabilized by a best offender contains
all component commutators. -/
theorem ff_constituent_eq_moved
    (ρ : Representation (ZMod 2) D V)
    (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hfit : generalizedFitting D = K) (hS : IsSQTK KnownSimple.IsKnownSimple D)
    {F : Type w} [Field F] [Finite F] [CharP F 2] (e : K ≃* PSL(2,F))
    (A : Subgroup D) (hA : IsBestOffender ρ A)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hAI : A ≤ subspaceStabilizer ρ I) :
    I = subspaceCommutator ρ ⊤ K := by
  let : IsElementaryAbelian 2 A := hA.1.2
  have hp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  have hz := NoStrongMoved.psl_center_bot K e
  have hc := NoStrongMoved.selfcentral_of_fitting K hfit hz
  have hcore : pCore 2 D = ⊥ := by
    apply bot_unique
    rw [←hc]
    exact ChapterB.irreducibleReduction_core_centralizes K
  have hZ : center D = ⊥ := by
    apply le_bot_iff.mp
    rw [←hc]
    intro z hz k hk
    exact mem_center_iff.mp hz k
  have hfitZ : generalizedFitting D = K ⊔ center D := by rw [hfit,hZ,sup_bot_eq]
  have hKA : ⁅K,A⁆ = K := by
    have hq : IsQuasisimple (generalizedFitting D) := hfit.symm ▸ inferInstance
    simpa only [hfit] using ChapterB.QuasisimpleSections.commutator_fitting_eq hcore hq hA.1.1 hp
  let E := K ⊔ A
  let L := K.subgroupOf E
  let A₀ := A.subgroupOf E
  let τ := ρ.comp E.subtype
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (show K ≤ E from le_sup_left)).symm
  have hfitE : generalizedFitting E = L := local_generalizedFitting K A hfitZ hcore hp
  let eL : L ≃* PSL(2,F) := (subgroupOfEquivOfLe le_sup_left).trans e
  have hcent : centralizer (L : Set E) = ⊥ :=
    NoStrongMoved.selfcentral_of_fitting L hfitE (NoStrongMoved.psl_center_bot L eL)
  have hEI : E ≤ subspaceStabilizer ρ I := sup_le hI.choose hAI
  let U : Subrepresentation τ := ⟨I, fun g _ hv => (hEI g.property _).2 hv⟩
  have hnU : ¬ ∀ l ∈ L, ∀ v, U.toRepresentation l v = v := by
    intro ht
    apply hI.not_le_fixedSpace ρ
    intro v hv k
    exact congrArg Subtype.val (ht ⟨k,mem_sup_left k.property⟩ k.property ⟨v,hv⟩)
  have hkU : (actionHom U.toRepresentation).ker = ⊥ := by
    apply bot_unique
    rw [←hcent]
    exact CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.action_kernel_le_centralizer U.toRepresentation L
      (CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.central_kernel_of_quasisimple U.toRepresentation L hnU)
  have hfU : Function.Injective U.toRepresentation := by
    intro a b hab
    apply (MonoidHom.ker_eq_bot_iff (actionHom U.toRepresentation)).mp hkU
    exact imageRepresentation_injective _ hab
  have hnsU : ¬ IsStrongFFModule U.toRepresentation := by
    intro hstrong
    exact NativeSource.preaction_impossible_of_source {
      Actor := E
      Space := I
      representation := U.toRepresentation
      sqtk := hS.subgroup E
      faithful := hfU
      strong := hstrong
      quasisimple := by rw [hfitE]; infer_instance
      componentEquiv := (MulEquiv.subgroupCongr hfitE).trans eL }
  have hA₀ := hA.subgroupOf ρ (show A ≤ E from le_sup_right)
  have hrA : rank A₀ = rank A := rank_subgroupOf (show A ≤ E from le_sup_right)
  have hcod : fixedCodim τ A₀ = fixedCodim ρ A :=
    fixedCodim_subgroupOf ρ (show A ≤ E from le_sup_right)
  have hlow : rank A₀ ≤ fixedCodim U.toRepresentation A₀ :=
    Nat.le_of_not_gt (fun hlt => hnsU ⟨A₀,hA₀.1,hlt⟩)
  have hle := fixedCodim_subrepresentation_le τ U A₀
  have hoff := (hA.isOffender ρ).2
  have heq : fixedCodim U.toRepresentation A₀ = fixedCodim τ A₀ := by omega
  have hsup := (fixedCodim_subrepresentation_eq_iff τ U A₀).mp heq
  have hfixA := quotient_trivial_of_sup_fixedSpace τ U A₀ hsup
  have hcomm : ⁅L,A₀⁆ = L := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_commutator]
    change ⁅(K.subgroupOf E).map E.subtype, (A.subgroupOf E).map E.subtype⁆ = (K.subgroupOf E).map E.subtype
    rw [map_subgroupOf_eq_of_le (show K ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right), hKA]
  have hfixK := trivial_sup_of_commutator_eq U.quotientRepresentation L A₀ hcomm hfixA
  apply le_antisymm
  · exact hI.choose_spec.1.ge.trans (subspaceCommutator_mono_left ρ le_top K)
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    exact (Submodule.Quotient.eq I).mp (hfixK ⟨k,mem_sup_left hk⟩ (mem_sup_right hk) (I.mkQ v))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo
open FiveReconstruction
universe u w
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

local instance cqFinite (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    (I : Submodule (ZMod 2) V) : Finite (centralQuotient ρ K I) :=
  Finite.of_surjective _ (Submodule.mkQ_surjective _)

/-- The canonical faithful central-section image is realized by its actual
actor and quotient map; the component equivalence is the induced action map. -/
def centralImageRealization
    (ρ : Representation (ZMod 2) D V) (K J : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hz : center K = ⊥) (hKJ : K ≤ J)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hJI : J ≤ subspaceStabilizer ρ I)
    (hfit : let τ := centralSectionRepresentation ρ K J I hJI le_normalizer_of_normal
      generalizedFitting (actionImage τ) = actionSubgroup τ (K.subgroupOf J)) :
    ConstituentRealization ρ K
      (imageRepresentation (centralSectionRepresentation ρ K J I hJI le_normalizer_of_normal))
      (generalizedFitting (actionImage
        (centralSectionRepresentation ρ K J I hJI le_normalizer_of_normal))) := by
  let τ := centralSectionRepresentation ρ K J I hJI le_normalizer_of_normal
  let L := K.subgroupOf J
  let b : L ≃* K := subgroupOfEquivOfLe hKJ
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv b.symm
  have hzL : center L = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro k hk
    have hh := (centerCongr b ⟨k,hk⟩).property
    change b k ∈ center K at hh
    rw [hz,mem_bot] at hh
    exact mem_bot.mpr (b.injective (hh.trans b.map_one.symm))
  have hn : ¬ L ≤ (actionHom τ).ker := by
    intro hk
    apply hI.not_le_fixedSpace ρ
    rw [←hI.choose_spec.1]
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hkK,v,hv,rfl⟩
    have he := (actionHom_eq_one_iff τ (⟨k,hKJ hkK⟩ : J)).mp (hk hkK)
      (Submodule.Quotient.mk (⟨v,hv⟩ : I))
    exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.subtype)).mp he
  exact {
    actor := J
    contains := hKJ
    space := I
    stable := hJI
    irrPlus := hI
    groupMap := actionHom τ
    surjective := τ.asGroupHom.rangeRestrict_surjective
    component := b.symm.trans
      ((SourceOrbit.ActionImage.Structure.componentEquiv τ L hn hzL).trans
        (MulEquiv.subgroupCongr hfit.symm))
    component_map := fun _ => rfl
    linearEquiv := LinearEquiv.refl _ _
    intertwines := fun _ _ => rfl }

/-- Replacement and the absence of strong PSL₂ offenders construct a
realized FF central section whose actual constituent is the full moved space. -/
theorem faithful_ff_moved_realization
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hfit : generalizedFitting D = K) (hS : IsSQTK KnownSimple.IsKnownSimple D)
    {F : Type w} [Field F] [Finite F] [CharP F 2] (e : K ≃* PSL(2,F))
    (hff : IsFFModule ρ) :
    ∃ (B : Subgroup D) (I : Submodule (ZMod 2) V)
      (hJI : K ⊔ B ≤ subspaceStabilizer ρ I),
      let τ := centralSectionRepresentation ρ K (K ⊔ B) I hJI le_normalizer_of_normal
      CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
        KnownSimple.IsKnownSimple (imageRepresentation τ) ∧
      IsFFModule (imageRepresentation τ) ∧
      ∃ r : ConstituentRealization ρ K (imageRepresentation τ) (generalizedFitting (actionImage τ)),
        r.space = I ∧ I = subspaceCommutator ρ ⊤ K := by
  have hz := NoStrongMoved.psl_center_bot K e
  obtain ⟨B,I,hB,hI,hJI,hB4,hFF,hfit',_⟩ :=
    faithful_irreducible_ff_section ρ hf K hfit hz hS hff
  refine ⟨B,I,hJI,hB4,hFF,
    centralImageRealization ρ K (K ⊔ B) hz le_sup_left I hI hJI hfit',rfl,?_⟩
  exact ff_constituent_eq_moved ρ K hfit hS e B hB.1 I hI
    (le_sup_right.trans hJI)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo
